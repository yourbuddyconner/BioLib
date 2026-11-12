import BioLib.Sim.Core

/-!
# Simulator runtime (floating point)

Random generation, read-count sampling and CSV output around the generic core.
Everything here runs on `Float` and nothing here is proved.  In particular the
random number generation and the multinomial sampler are ordinary unverified
code.

Two generative models are available.

**Stochastic logistic model** (default; `Config.slm`).  Each species' abundance
is drawn from the stationary gamma distribution of the model of Grilli (2020),
with mean abundances lognormal across species; see `BioLib.Papers.Grilli2020`.
Species do not interact.  Its parameters (`beta`, `taylorExponent`, `madSigma`, `species`)
are meant to be estimated from data (`python/fit_slm.py`).  The treatment
effect and the measurement bias are additions with no source.

**Lotka–Volterra competition** (`Config.slm := false`):

1. A species pool.  Species `i` has growth rate `rᵢ`, carrying capacity `Kᵢ`
   (lognormal across species) and drug sensitivity `sᵢ`.  The interaction
   matrix has `Aᵢᵢ = -rᵢ / Kᵢ` and, for a random subset of pairs,
   `Aᵢⱼ = -rᵢ αᵢⱼ / Kⱼ`, so the model is
   `xᵢ' = rᵢ xᵢ (1 - xᵢ / Kᵢ - ∑ⱼ αᵢⱼ xⱼ / Kⱼ)`: a competitor's effect is
   measured relative to its own capacity.  The `αᵢⱼ` are scaled so that the
   expected total competition on a species is `strength`.
2. A per-study, per-species multiplicative measurement bias.
3. Per sample: a random subset of species present, each starting below its
   capacity; a lognormal per-species environmental factor multiplying the
   growth rates; a treated/untreated label; `simulate` to a final state;
   observation with the study's bias; multinomial read counts at fixed depth.

The parameter distributions are modelling choices made to match summary
statistics of real data (see `python/realism.py`); they are not derived from
measurements of any organism.
-/

namespace BioLib.Sim

/-- Settings of a simulation run. -/
structure Config where
  species : Nat := 50
  samples : Nat := 100
  studies : Nat := 1
  depth : Nat := 10000
  steps : Nat := 600
  dt : Float := 0.02
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
  connectance : Float := 0.05
  /-- Expected total competition on a species, in units of its own self-limitation. -/
  strength : Float := 0.5
  /-- Standard deviation of the natural log of carrying capacity across species. -/
  capacitySd : Float := 0.0
  /-- Standard deviation of the natural log of the per-sample environmental factor. -/
  envSd : Float := 0.0
  /-- Standard deviation of the log of the measurement bias. -/
  biasSd : Float := 0.0
  /-- Use the stochastic logistic model (`true`) or Lotka–Volterra competition (`false`). -/
  slm : Bool := true
  /-- Stochastic logistic model: gamma shape `β` of abundance fluctuations
  (`β = 2 / σ - 1`) for a species of mean abundance `betaRefAbundance`. -/
  beta : Float := 1.0
  /-- Stochastic logistic model: exponent `z` of Taylor's law, variance ∝ mean ^ z.
  The paper's law is `z = 2`, for which every species has shape `beta`.  In
  general a species of mean abundance `m` has shape
  `beta * (m / betaRefAbundance) ^ (2 - z)`. -/
  taylorExponent : Float := 2.0
  /-- Stochastic logistic model: standard deviation of the natural log of mean
  abundance across species.  Mean abundances are rescaled to sum to one. -/
  madSigma : Float := 2.0
  /-- Stochastic logistic model: draw read counts as independent Poisson
  variables with mean `depth * abundance`, without normalizing (the sampling
  model of the paper, Eq. 7), instead of normalizing to relative abundance and
  drawing exactly `depth` reads. -/
  poisson : Bool := false

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
  /-- Carrying capacities. -/
  K : Vector Float n
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
  let (K, g) := drawVec n (fun g =>
    let (z, g) := normal g
    (Float.exp (c.capacitySd * z), g)) g
  -- Largest competition coefficient: uniform on `[0, αmax)` with probability
  -- `connectance` gives expected total `strength` over `n` potential competitors.
  let αmax := 2.0 * c.strength / (c.connectance * n.toFloat)
  let (A, g) := Fin.foldl n (fun (acc : Vector (Vector Float n) n × StdGen) i =>
    let (row, g) := Fin.foldl n (fun (acc : Vector Float n × StdGen) j =>
      let (u, g) := uniform acc.2
      if u < c.connectance then
        let (α, g) := uniformIn 0.0 αmax g
        (acc.1.set j (-(r[i] * α / K[j])), g)
      else (acc.1, g)) (Vector.replicate n 0.0, acc.2)
    (acc.1.set i (row.set i (-(r[i] / K[i]))), g)) (Vector.replicate n (Vector.replicate n 0.0), g)
  let (bias, g) := (List.range (max c.studies 1)).foldl
    (fun (acc : Array (Vector Float n) × StdGen) _ =>
      let (b, g) := drawVec n (fun g =>
        let (z, g) := normal g
        (Float.exp (c.biasSd * z), g)) acc.2
      (acc.1.push b, g)) (#[], g)
  ({ r, K, s, A, bias }, g)

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

/-- One row of the interaction matrix, storing only its nonzero entries. -/
structure SparseRow where
  idx : Array Nat
  val : FloatArray
  deriving Inhabited

/-- The nonzero entries of each row of `A`, in increasing column order. -/
def sparseRows {n : Nat} (A : Vector (Vector Float n) n) : Array SparseRow :=
  A.toArray.map fun row => Id.run do
    let mut idx := #[]
    let mut val := FloatArray.empty
    for j in [0:n] do
      let a := row[j]!
      if a != 0.0 then
        idx := idx.push j
        val := val.push a
    return { idx, val }

/-- One Euler step of the Lotka–Volterra model on unboxed arrays.

This is a hand-specialized version of `eulerStep (glvRate rates A) h` from
`BioLib.Sim.Core`.  It performs the same floating-point operations in the same
order, skipping only the terms where the interaction coefficient is zero, so
its output is expected to equal the generic definition's output exactly.  That
is tested (`fastCheck`), not proved. -/
def fastStep (rates : FloatArray) (rows : Array SparseRow) (h : Float) (x : FloatArray) :
    FloatArray := Id.run do
  let n := x.size
  let mut out := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let row : SparseRow := rows[i]!
    let mut acc := 0.0
    for k in [0:row.idx.size] do
      acc := acc + row.val[k]! * x[row.idx[k]!]!
    let xi := x[i]!
    out := out.push (xi + h * (xi * (rates[i]! + acc)))
  return out

/-- `k` Euler steps of the inhibited Lotka–Volterra model on unboxed arrays.

Only species present in `x₀` are simulated.  This relies on two facts about
the model: an absent species stays absent (`eulerStep_glvRate_absent`), and an
absent species contributes a zero term to every other species' rate. -/
def fastSimulate {n : Nat} (r s : Vector Float n) (rows : Array SparseRow) (B h : Float)
    (k : Nat) (x₀ : Vector Float n) : Vector Float n := Id.run do
  -- `pos[j]` is the position of species `j` among the present species, or `n` if absent.
  let mut present : Array Nat := #[]
  let mut pos : Array Nat := Array.replicate n n
  for j in [0:n] do
    if x₀[j]! != 0.0 then
      pos := pos.set! j present.size
      present := present.push j
  let mut rates := FloatArray.emptyWithCapacity present.size
  let mut x := FloatArray.emptyWithCapacity present.size
  let mut sub : Array SparseRow := Array.emptyWithCapacity present.size
  for i in present do
    rates := rates.push (r[i]! - s[i]! * B)
    x := x.push x₀[i]!
    let row : SparseRow := rows[i]!
    let mut idx : Array Nat := #[]
    let mut val := FloatArray.empty
    for e in [0:row.idx.size] do
      let q := pos[row.idx[e]!]!
      if q < n then
        idx := idx.push q
        val := val.push row.val[e]!
    sub := sub.push { idx, val }
  for _ in [0:k] do
    x := fastStep rates sub h x
  let mut out : Vector Float n := Vector.replicate n 0.0
  for q in [0:present.size] do
    out := out.set! present[q]! x[q]!
  return out

/-- One simulated sample. -/
structure Sample (n : Nat) where
  study : Nat
  treated : Bool
  /-- Total absolute abundance at the end of the simulation; not observable from counts. -/
  total : Float
  counts : Vector Nat n

/-- Simulate one sample from the pool. -/
def drawSample (c : Config) (pool : Pool c.species) (rows : Array SparseRow) (idx : Nat)
    (g : StdGen) : Sample c.species × StdGen :=
  let n := c.species
  let study := idx % max c.studies 1
  let (u, g) := uniform g
  let treated : Bool := u < c.treatedFrac
  let (x₀, g) := Fin.foldl n (fun (acc : Vector Float n × StdGen) i =>
    let (u, g) := uniform acc.2
    if u < c.presence then
      let (f, g) := uniformIn 0.1 1.0 g
      (acc.1.set i (pool.K[i] * f), g)
    else (acc.1, g)) (Vector.replicate n 0.0, g)
  let (env, g) := drawVec n (fun g =>
    let (z, g) := normal g
    (Float.exp (c.envSd * z), g)) g
  let rEnv : Vector Float n := Vector.ofFn fun i => pool.r[i] * env[i]
  let B := if treated then c.dose else 0.0
  let x := fastSimulate rEnv pool.s rows B c.dt c.steps x₀
  let b := pool.bias[study]!
  let p := observeFast (fun i => b[i]) x
  let total := sumFin (n := n) fun i => x[i]
  -- An empty community has no reads.  This case needs separate handling because
  -- `relAbundance` divides by the total: over the reals `0 / 0 = 0`, but in
  -- floating point it is NaN.
  let (counts, g) := if total > 0.0 then sampleCounts p c.depth g else (Vector.replicate n 0, g)
  ({ study, treated, total, counts }, g)

/-- Largest difference between the specialized and the generic simulation on a
random pool of `n` species over `k` steps.  Expected to be exactly zero. -/
def fastCheck (n k seed : Nat) : Float :=
  let c : Config := { species := n, seed }
  let (pool, g) := drawPool c (mkStdGen seed)
  let (x₀, _) := drawVec n (fun g =>
    let (u, g) := uniform g
    if u < 0.6 then uniformIn 0.0 0.2 g else (0.0, g)) g
  let generic := simulate (fun i => pool.r[i]) (fun i => pool.s[i]) (fun i j => pool.A[i][j])
    0.7 c.dt k x₀
  let fast := fastSimulate pool.r pool.s (sparseRows pool.A) 0.7 c.dt k x₀
  Fin.foldl n (fun acc i => max acc (Float.abs (generic[i] - fast[i]))) 0.0

/-- Gamma draw with shape `a ≥ 1` and scale 1 (Marsaglia–Tsang rejection method). -/
def gammaGe1 (a : Float) (g : StdGen) : Float × StdGen :=
  let d := a - 1.0 / 3.0
  let c := 1.0 / Float.sqrt (9.0 * d)
  let rec loop (fuel : Nat) (g : StdGen) : Float × StdGen :=
    match fuel with
    | 0 => (d, g)
    | fuel + 1 =>
      let (z, g) := normal g
      let v := (1.0 + c * z) * (1.0 + c * z) * (1.0 + c * z)
      let (u, g) := uniform g
      if v > 0.0 && Float.log (1.0 - u) < 0.5 * z * z + d - d * v + d * Float.log v then
        (d * v, g)
      else loop fuel g
  loop 1000 g

/-- Gamma draw with shape `a > 0` and scale 1. -/
def gammaDraw (a : Float) (g : StdGen) : Float × StdGen :=
  if a < 1.0 then
    let (x, g) := gammaGe1 (a + 1.0) g
    let (u, g) := uniform g
    (x * Float.pow (1.0 - u) (1.0 / a), g)
  else gammaGe1 a g

/-- Mean abundance at which `Config.beta` applies when Taylor's exponent is not 2. -/
def betaRefAbundance : Float := 1.0e-3

/-- Poisson draw with mean `lam`, by multiplying uniforms (Knuth), applied to
chunks of mean at most 30 so that `exp (-chunk)` does not underflow. -/
def poissonDraw (lam : Float) (g : StdGen) : Nat × StdGen :=
  let chunks := (lam / 30.0).ceil.toUInt64.toNat + 1
  let limit := Float.exp (-(lam / chunks.toFloat))
  (List.range chunks).foldl (fun (acc : Nat × StdGen) _ =>
    let rec loop (fuel k : Nat) (p : Float) (g : StdGen) : Nat × StdGen :=
      match fuel with
      | 0 => (k, g)
      | fuel + 1 =>
        let (u, g) := uniform g
        let p := p * (1.0 - u)
        if p > limit then loop fuel (k + 1) p g else (k, g)
    let (k, g) := loop 2000 0 1.0 acc.2
    (acc.1 + k, g)) (0, g)

/-- Species pool for the stochastic logistic model. -/
structure SlmPool (n : Nat) where
  /-- Mean abundances, summing to one. -/
  mean : Vector Float n
  /-- Noise parameter `σᵢ = 2 / (βᵢ + 1)` of each species. -/
  σ : Vector Float n
  /-- Carrying capacities `Kᵢ = meanᵢ / (1 - σᵢ / 2)`. -/
  K : Vector Float n
  /-- Sensitivities, in units of `1 / (τ * concentration)`. -/
  s : Vector Float n
  bias : Array (Vector Float n)

/-- Draw a pool for the stochastic logistic model.  Mean abundances are
lognormal across species and rescaled to sum to one.  Each species' gamma
shape follows Taylor's law with the configured exponent. -/
def drawSlmPool (c : Config) (g : StdGen) : SlmPool c.species × StdGen :=
  let n := c.species
  let (raw, g) := drawVec n (fun g =>
    let (z, g) := normal g
    (Float.exp (c.madSigma * z), g)) g
  let total := sumFin (n := n) fun i => raw[i]
  let mean : Vector Float n := Vector.ofFn fun i => raw[i] / total
  let σ : Vector Float n := Vector.ofFn fun i =>
    2.0 / (c.beta * Float.pow (mean[i] / betaRefAbundance) (2.0 - c.taylorExponent) + 1.0)
  let K : Vector Float n := Vector.ofFn fun i => mean[i] / (1.0 - σ[i] / 2.0)
  let (s, g) := drawVec n (fun g =>
    let (u, g) := uniform g
    if u < c.sensitiveFrac then uniformIn 0.5 2.0 g else (0.0, g)) g
  let (bias, g) := (List.range (max c.studies 1)).foldl
    (fun (acc : Array (Vector Float n) × StdGen) _ =>
      let (b, g) := drawVec n (fun g =>
        let (z, g) := normal g
        (Float.exp (c.biasSd * z), g)) acc.2
      (acc.1.push b, g)) (#[], g)
  ({ mean, σ, K, s, bias }, g)

/-- One sample from the stationary distribution of the stochastic logistic
model.  In a treated sample each species keeps the fraction
`growthFraction 1 sᵢ dose` of its growth rate; its abundance is then gamma
with shape `slmShape σᵢ f` and mean `slmMean Kᵢ σᵢ f`, or zero when the shape
is not positive (the species cannot persist). -/
def drawSlmSample (c : Config) (pool : SlmPool c.species) (idx : Nat) (g : StdGen) :
    Sample c.species × StdGen :=
  let n := c.species
  let study := idx % max c.studies 1
  let (u, g) := uniform g
  let treated : Bool := u < c.treatedFrac
  let B := if treated then c.dose else 0.0
  let (x, g) := Fin.foldl n (fun (acc : Vector Float n × StdGen) i =>
    let f := growthFraction 1.0 pool.s[i] B
    let shape := slmShape pool.σ[i] f
    if shape > 0.0 then
      let (γ, g) := gammaDraw shape acc.2
      (acc.1.set i (slmMean pool.K[i] pool.σ[i] f / shape * γ), g)
    else (acc.1, acc.2)) (Vector.replicate n 0.0, g)
  let b := pool.bias[study]!
  let total := sumFin (n := n) fun i => x[i]
  let (counts, g) :=
    if c.poisson then
      Fin.foldl n (fun (acc : Vector Nat n × StdGen) i =>
        let lam := c.depth.toFloat * b[i] * x[i]
        if lam > 0.0 then
          let (k, g) := poissonDraw lam acc.2
          (acc.1.set i k, g)
        else acc) (Vector.replicate n 0, g)
    else if total > 0.0 then sampleCounts (observeFast (fun i => b[i]) x) c.depth g
    else (Vector.replicate n 0, g)
  ({ study, treated, total, counts }, g)

/-- Time-averaged mean and squared coefficient of variation of one
Euler–Maruyama trajectory of the stochastic logistic model with `τ = K = 1`,
returned as relative errors against the stationary values `1 - σ / 2` and
`1 / β`.  A test of the simulation against the stationary law, not a proof. -/
def slmCheck (β h : Float) (burn steps seed : Nat) : Float × Float :=
  let σ := 2.0 / (β + 1.0)
  let amp := Float.sqrt (σ * h)
  let advance := fun (x : Float) (g : StdGen) =>
    let (z, g) := normal g
    (slmStep 1.0 1.0 h (amp * z) x, g)
  let (x, g) := (List.range burn).foldl (fun (acc : Float × StdGen) _ => advance acc.1 acc.2)
    (0.5, mkStdGen seed)
  let (_, _, s1, s2) := (List.range steps).foldl
    (fun (acc : Float × StdGen × Float × Float) _ =>
      let (x, g) := advance acc.1 acc.2.1
      (x, g, acc.2.2.1 + x, acc.2.2.2 + x * x)) (x, g, 0.0, 0.0)
  let mean := s1 / steps.toFloat
  let cv2 := (s2 / steps.toFloat - mean * mean) / (mean * mean)
  ((mean - (1.0 - σ / 2.0)) / (1.0 - σ / 2.0), (cv2 - 1.0 / β) * β)

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
  emit (csvHeader c.species)
  if c.slm then
    let (pool, g) := drawSlmPool c g
    let mut g := g
    for idx in [0:c.samples] do
      let (s, g') := drawSlmSample c pool idx g
      g := g'
      emit (s.toCsv idx)
  else
    let (pool, g) := drawPool c g
    let rows := sparseRows pool.A
    let mut g := g
    for idx in [0:c.samples] do
      let (s, g') := drawSample c pool rows idx g
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
