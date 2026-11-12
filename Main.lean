import BioLib.Sim.Run

/-!
# `biolib-sim`: command-line entry point for the simulator

Writes a CSV of simulated read counts to standard output.  Run with `--help`
for the options.  This file and its imports do not depend on Mathlib.
-/

open BioLib.Sim

def usage : String :=
  "biolib-sim [options]   write simulated microbiome read counts as CSV to stdout

  --model M           'slm' (stochastic logistic model, default) or 'glv'
                      (Lotka-Volterra competition)
  --species N         number of species in the pool (default 50)
  --samples N         number of samples (default 100)
  --studies N         number of studies, each with its own measurement bias (default 1)
  --depth N           reads per sample (default 10000)
  --steps N           glv: Euler steps per sample (default 600)
  --dt X              glv: Euler step size (default 0.02)
  --seed N            random seed (default 0)
  --treated-frac X    probability that a sample is treated (default 0.5)
  --dose X            inhibitor concentration in treated samples (default 1.0)
  --sensitive-frac X  probability that a species is sensitive (default 0.5)
  --presence X        probability that a species starts present (default 0.8)
  --connectance X     probability of a competitive interaction (default 0.05)
  --strength X        expected total competition on a species (default 0.5)
  --capacity-sd X     std. dev. of log carrying capacity across species (default 0)
  --env-sd X          std. dev. of log per-sample environmental factor (default 0)
  --beta X            slm: gamma shape of abundance fluctuations, at mean
                      abundance 0.001 (default 1.0)
  --taylor-exponent X slm: variance scales as mean^X; 2 gives every species
                      the same shape, as in the paper (default 2)
  --mad-sigma X       slm: std. dev. of log mean abundance across species;
                      mean abundances are rescaled to sum to one (default 2)
  --sampling S        slm: 'multinomial' (normalize, then exactly --depth reads;
                      default) or 'poisson' (independent Poisson counts with
                      mean depth x abundance, as in the paper)
  --bias-sd X         std. dev. of log measurement bias per study (default 0)
  --selfcheck N       largest Float-vs-exact-rational difference over N ≤ 16 steps,
                      then the difference between the fast and generic code paths"

def parseUnsigned (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map Nat.toFloat
  | [a, b] => do
      let whole ← if a.isEmpty then some 0 else a.toNat?
      let frac ← if b.isEmpty then some 0 else b.toNat?
      some (whole.toFloat + frac.toFloat / (10 ^ b.length : Nat).toFloat)
  | _ => none

def parseFloat (s : String) : Option Float :=
  if s.startsWith "-" then (parseUnsigned (s.drop 1).toString).map (-·) else parseUnsigned s

def parseArgs : Config → List String → Except String Config
  | c, [] => .ok c
  | c, flag :: value :: rest =>
    let nat (k : Nat → Config) : Except String Config :=
      match value.toNat? with
      | some v => parseArgs (k v) rest
      | none => .error s!"{flag} needs a natural number, got '{value}'"
    let float (k : Float → Config) : Except String Config :=
      match parseFloat value with
      | some v => parseArgs (k v) rest
      | none => .error s!"{flag} needs a decimal number, got '{value}'"
    match flag with
    | "--species" => nat fun v => { c with species := v }
    | "--samples" => nat fun v => { c with samples := v }
    | "--studies" => nat fun v => { c with studies := v }
    | "--depth" => nat fun v => { c with depth := v }
    | "--steps" => nat fun v => { c with steps := v }
    | "--seed" => nat fun v => { c with seed := v }
    | "--dt" => float fun v => { c with dt := v }
    | "--treated-frac" => float fun v => { c with treatedFrac := v }
    | "--dose" => float fun v => { c with dose := v }
    | "--sensitive-frac" => float fun v => { c with sensitiveFrac := v }
    | "--presence" => float fun v => { c with presence := v }
    | "--connectance" => float fun v => { c with connectance := v }
    | "--strength" => float fun v => { c with strength := v }
    | "--capacity-sd" => float fun v => { c with capacitySd := v }
    | "--env-sd" => float fun v => { c with envSd := v }
    | "--beta" => float fun v => { c with beta := v }
    | "--taylor-exponent" => float fun v => { c with taylorExponent := v }
    | "--sampling" =>
      match value with
      | "poisson" => parseArgs { c with poisson := true } rest
      | "multinomial" => parseArgs { c with poisson := false } rest
      | _ => .error s!"--sampling is 'poisson' or 'multinomial', got '{value}'"
    | "--mad-sigma" => float fun v => { c with madSigma := v }
    | "--model" =>
      match value with
      | "slm" => parseArgs { c with slm := true } rest
      | "glv" => parseArgs { c with slm := false } rest
      | _ => .error s!"--model is 'slm' or 'glv', got '{value}'"
    | "--bias-sd" => float fun v => { c with biasSd := v }
    | _ => .error s!"unknown option '{flag}'"
  | _, [flag] => .error s!"option '{flag}' needs a value"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | ["--selfcheck", k] =>
    match k.toNat? with
    | some k =>
      if k > 16 then
        IO.eprintln "--selfcheck supports at most 16 steps: exact rational states double in size every step"
        return 2
      IO.println s!"{selfCheck k / 2.220446049250313e-16} machine epsilons"
      IO.println s!"{fastCheck 40 300 1} fast-vs-generic difference"
      let (m, v) := slmCheck 1.5 0.001 20000 2000000 1
      IO.println s!"{m} {v} relative error of SLM trajectory mean and CV^2 against the stationary law"
      return 0
    | none => IO.eprintln "--selfcheck needs a natural number"; return 2
  | _ =>
    match parseArgs {} args with
    | .error e => IO.eprintln s!"biolib-sim: {e}\n\n{usage}"; return 2
    | .ok c =>
      if c.species = 0 then
        IO.eprintln "biolib-sim: --species must be positive"; return 2
      let out ← IO.getStdout
      run c fun line => out.putStrLn line
      return 0
