import BioLib.Sim.Core

/-!
# Simulator runtime (floating point)

Random generation, read-count sampling and CSV output around the generic core.
Everything here runs on `Float` and nothing here is proved.  In particular the
random number generation and the multinomial sampler are ordinary unverified
code.

Generative model for one data set:

1. A species pool: growth rates `r`, a competitive interaction matrix `A`
   (negative self-limitation, nonpositive off-diagonal entries, so trajectories
   stay bounded), and per-species drug sensitivities `s`.
2. A per-study, per-species multiplicative measurement bias.
3. Per sample: a random subset of species present at random initial
   abundances; a treated/untreated label; `simulate` to a final state;
   `observe` with the study's bias; multinomial read counts at fixed depth.
-/

namespace BioLib.Sim

/-- Settings of a simulation run. -/
structure Config where
  species : Nat := 50
  samples : Nat := 100
  studies : Nat := 1
  depth : Nat := 10000
  steps : Nat := 2000
  dt : Float := 0.01
  seed : Nat := 0
  /-- Probability that a sample is treated. -/
  treatedFrac : Float := 0.5
  /-- Inhibitor concentration in treated samples. -/
  dose : Float := 1.0
  /-- Probability that a species is sensitive to the inhibitor. -/
  sensitiveFrac : Float := 0.5
  /-- Probability that a species is present at the start of a sample. -/
  presence : Float := 0.8
  /-- Probability that one species competes with another. -/
  connectance : Float := 0.2
  /-- Largest off-diagonal competition strength. -/
  strength : Float := 0.5
  /-- Standard deviation of the log of the measurement bias. -/
  biasSd : Float := 0.0

/-- Uniform draw from `[0, 1)`. -/
def uniform (g : StdGen) : Float × StdGen :=
  let (k, g) := randNat g 0 (2 ^ 53 - 1)
  (k.toFloat / (2 ^ 53 : Nat).toFloat, g)

/-- Uniform draw from `[lo, hi)`. -/
def uniformIn (lo hi : Float) (g : StdGen) : Float × StdGen :=
  let (u, g) := uniform g
  (lo + (hi - lo) * u, g)

/-- Standard normal draw (Box–Muller). -/
def normal (g : StdGen) : Float × StdGen :=
  let (u₁, g) := uniform g
  let (u₂, g) := uniform g
  (Float.sqrt (-2.0 * Float.log (1.0 - u₁)) * Float.cos (6.283185307179586 * u₂), g)

/-- A vector of `n` independent draws. -/
def drawVec (n : Nat) (draw : StdGen → Float × StdGen) (g : StdGen) : Vector Float n × StdGen :=
  Fin.foldl n (fun (acc : Vector Float n × StdGen) i =>
    let (x, g) := draw acc.2
    (acc.1.set i x, g)) (Vector.replicate n 0.0, g)

/-- The fixed ingredients shared by all samples of a run. -/
structure Pool (n : Nat) where
  r : Vector Float n
  s : Vector Float n
  A : Vector (Vector Float n) n
  /-- One bias vector per study. -/
  bias : Array (Vector Float n)

/-- Draw a species pool. -/
def drawPool (c : Config) (g : StdGen) : Pool c.species × StdGen :=
  let n := c.species
  let (r, g) := drawVec n (uniformIn 0.5 1.5) g
  let (s, g) := drawVec n (fun g =>
    let (u, g) := uniform g
    if u < c.sensitiveFrac then uniformIn 0.5 2.0 g else (0.0, g)) g
  let (A, g) := Fin.foldl n (fun (acc : Vector (Vector Float n) n × StdGen) i =>
    let (row, g) := drawVec n (fun g =>
      let (u, g) := uniform g
      if u < c.connectance then
        let (w, g) := uniformIn 0.0 c.strength g
        (-w, g)
      else (0.0, g)) acc.2
    (acc.1.set i (row.set i (-1.0)), g)) (Vector.replicate n (Vector.replicate n 0.0), g)
  let (bias, g) := (List.range (max c.studies 1)).foldl
    (fun (acc : Array (Vector Float n) × StdGen) _ =>
      let (b, g) := drawVec n (fun g =>
        let (z, g) := normal g
        (Float.exp (c.biasSd * z), g)) acc.2
      (acc.1.push b, g)) (#[], g)
  ({ r, s, A, bias }, g)

/-- Draw `depth` reads from the distribution `p` and count them per species. -/
def sampleCounts {n : Nat} (p : Vector Float n) (depth : Nat) (g : StdGen) :
    Vector Nat n × StdGen :=
  let cdf : Vector Float n := (Fin.foldl n (fun (acc : Vector Float n × Float) i =>
    let t := acc.2 + p[i]
    (acc.1.set i t, t)) (Vector.replicate n 0.0, 0.0)).1
  (List.range depth).foldl (fun (acc : Vector Nat n × StdGen) _ =>
    let (u, g) := uniform acc.2
    -- binary search for the first index whose cumulative probability exceeds `u`
    let idx := Id.run do
      let mut lo := 0
      let mut hi := n
      while lo < hi do
        let mid := (lo + hi) / 2
        if h : mid < n then
          if cdf[mid] ≤ u then lo := mid + 1 else hi := mid
        else hi := mid
      return lo
    if h : idx < n then (acc.1.set idx (acc.1[idx] + 1), g) else (acc.1, g))
    (Vector.replicate n 0, g)

/-- One simulated sample. -/
structure Sample (n : Nat) where
  study : Nat
  treated : Bool
  /-- Total absolute abundance at the end of the simulation; not observable from counts. -/
  total : Float
  counts : Vector Nat n

/-- Simulate one sample from the pool. -/
def drawSample (c : Config) (pool : Pool c.species) (idx : Nat) (g : StdGen) :
    Sample c.species × StdGen :=
  let n := c.species
  let study := idx % max c.studies 1
  let (u, g) := uniform g
  let treated : Bool := u < c.treatedFrac
  let (x₀, g) := drawVec n (fun g =>
    let (u, g) := uniform g
    if u < c.presence then uniformIn 0.01 0.2 g else (0.0, g)) g
  let B := if treated then c.dose else 0.0
  let x := simulate (fun i => pool.r[i]) (fun i => pool.s[i]) (fun i j => pool.A[i][j])
    B c.dt c.steps x₀
  let b := pool.bias[study]!
  let p := observe (fun i => b[i]) x
  let total := sumFin (n := n) fun i => x[i]
  -- An empty community has no reads.  This case needs separate handling because
  -- `relAbundance` divides by the total: over the reals `0 / 0 = 0`, but in
  -- floating point it is NaN.
  let (counts, g) := if total > 0.0 then sampleCounts p c.depth g else (Vector.replicate n 0, g)
  ({ study, treated, total, counts }, g)

/-- CSV header line. -/
def csvHeader (n : Nat) : String :=
  "sample,study,treated,total_abundance," ++
    ",".intercalate ((List.range n).map fun i => s!"sp{i}")

/-- CSV line for one sample. -/
def Sample.toCsv {n : Nat} (idx : Nat) (s : Sample n) : String :=
  s!"{idx},{s.study},{if s.treated then 1 else 0},{s.total}," ++
    ",".intercalate (s.counts.toList.map toString)

/-- Run the whole simulation, writing CSV lines with `emit`. -/
def run (c : Config) (emit : String → IO Unit) : IO Unit := do
  let g := mkStdGen c.seed
  let (pool, g) := drawPool c g
  emit (csvHeader c.species)
  let mut g := g
  for idx in [0:c.samples] do
    let (s, g') := drawSample c pool idx g
    g := g'
    emit (s.toCsv idx)

/-- Convert an exact rational to a float.  Numerator and denominator are first
shifted right so that the denominator has about 64 bits; converting very large
naturals directly would overflow to infinity.  The shift costs a relative error
of at most about `2⁻⁶³`, far below `Float` precision. -/
def ratToFloat (q : Rat) : Float :=
  let shift := q.den.log2 - 64
  let a := (q.num.natAbs >>> shift).toFloat / (q.den >>> shift).toFloat
  if q.num < 0 then -a else a

/-- Largest difference between the `Float` simulation and the exact rational
simulation of the same small system, over `k` Euler steps. -/
def selfCheck (k : Nat) : Float :=
  let r : Fin 3 → Rat := fun i => #[1, 3/4, 5/4][i]!
  let s : Fin 3 → Rat := fun i => #[1/2, 0, 1][i]!
  let A : Fin 3 → Fin 3 → Rat := fun i j =>
    #[#[-1, -1/4, 0], #[-1/8, -1, -1/2], #[0, -1/4, -1]][i]![j]!
  let x₀ : Vector Rat 3 := #v[1/10, 1/5, 1/20]
  let exact := simulate r s A (1/2) (1/64) k x₀
  let approx := simulate (fun i => ratToFloat (r i)) (fun i => ratToFloat (s i))
    (fun i j => ratToFloat (A i j)) 0.5 (1.0 / 64.0) k (x₀.map ratToFloat)
  Fin.foldl 3 (fun acc i => max acc (Float.abs (ratToFloat exact[i] - approx[i]))) 0.0

end BioLib.Sim
