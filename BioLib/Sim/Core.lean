/-!
# Simulator core

Computable definitions for simulating microbial communities, written once and
generic over the number type `α`.  The same definitions are

* run with `α = Float` by the `biolib-sim` executable,
* run exactly with `α = Rat` as a reference,
* reasoned about with `α = ℝ` in `BioLib.Sim.Theorems`.

This file must not import Mathlib: an executable that imports Mathlib has to
compile all of it.  Only arithmetic operations are assumed of `α`, because
`Float` is not a lawful field.
-/

namespace BioLib.Sim

variable {α : Type} [Add α] [Sub α] [Mul α] [Div α] [OfNat α 0] {n : Nat}

/-- Sum of `f` over `Fin n`, by a left fold. -/
def sumFin (f : Fin n → α) : α := Fin.foldl n (fun acc i => acc + f i) 0

/-- Generalized Lotka–Volterra rate `xᵢ * (rᵢ + ∑ⱼ Aᵢⱼ xⱼ)`. -/
def glvRate (r : Fin n → α) (A : Fin n → Fin n → α) (x : Fin n → α) (i : Fin n) : α :=
  x i * (r i + sumFin fun j => A i j * x j)

/-- Intrinsic growth rates under an inhibitor at concentration `B`, with
per-species sensitivities `s`: `rᵢ - sᵢ * B`. -/
def inhibitedRates (r s : Fin n → α) (B : α) (i : Fin n) : α := r i - s i * B

/-- One explicit Euler step of size `h` for the vector field `f`. -/
def eulerStep (f : (Fin n → α) → Fin n → α) (h : α) (x : Fin n → α) (i : Fin n) : α :=
  x i + h * f x i

/-- Relative abundance: each component divided by the total. -/
def relAbundance (x : Fin n → α) (i : Fin n) : α := x i / sumFin x

/-- Taxon-specific multiplicative measurement bias. -/
def applyBias (b x : Fin n → α) (i : Fin n) : α := b i * x i

/-- Apply a map on states to a state stored as an array, storing the result. -/
def stepVec (f : (Fin n → α) → Fin n → α) (v : Vector α n) : Vector α n :=
  Vector.ofFn (f fun i => v[i])

/-- Apply `stepVec f` `k` times. -/
def iterateVec (f : (Fin n → α) → Fin n → α) : Nat → Vector α n → Vector α n
  | 0, v => v
  | k + 1, v => iterateVec f k (stepVec f v)

/-- State after `k` Euler steps of the inhibited Lotka–Volterra model. -/
def simulate (r s : Fin n → α) (A : Fin n → Fin n → α) (B h : α) (k : Nat)
    (x₀ : Vector α n) : Vector α n :=
  iterateVec (eulerStep (glvRate (inhibitedRates r s B) A) h) k x₀

/-- What is observed of a state: biased, then normalized to relative abundance. -/
def observe (b : Fin n → α) (v : Vector α n) : Vector α n :=
  stepVec (fun x => relAbundance (applyBias b x)) v

/-! ### Stochastic logistic model (Grilli 2020)

`dx/dt = (x / τ) (1 - x / K) + √(σ / τ) x ξ(t)`.  The definitions below are the
deterministic ingredients; see `BioLib.Papers.Grilli2020` for the source and
for what is proved about them. -/

/-- Drift of the stochastic logistic model: `(x / τ) * (1 - x / K)`. -/
def slmDrift [OfNat α 1] (τ K x : α) : α := x / τ * (1 - x / K)

/-- One Euler–Maruyama step of the stochastic logistic model.  `w` is the
noise increment `√(σ h / τ) * z` for a standard normal `z`, supplied by the caller. -/
def slmStep [OfNat α 1] (τ K h w x : α) : α := x + h * slmDrift τ K x + w * x

/-- Fraction of the growth rate left under an inhibitor: `1 - τ * s * B`, for
sensitivity `s` and concentration `B`. -/
def growthFraction [OfNat α 1] (τ s B : α) : α := 1 - τ * s * B

/-- Shape parameter of the stationary gamma distribution when a fraction `f`
of the growth rate remains: `2 f / σ - 1`.  At `f = 1` this is `2 / σ - 1`. -/
def slmShape [OfNat α 1] [OfNat α 2] (σ f : α) : α := 2 * f / σ - 1

/-- Mean of the stationary distribution when a fraction `f` of the growth rate
remains: `K * (f - σ / 2)`.  At `f = 1` this is `K * (1 - σ / 2)`. -/
def slmMean [OfNat α 2] (K σ f : α) : α := K * (f - σ / 2)

/-- `observe`, computing the total once instead of once per component. -/
def observeFast (b : Fin n → α) (v : Vector α n) : Vector α n :=
  let w := stepVec (applyBias b) v
  let total := sumFin fun i : Fin n => w[i]
  w.map (· / total)

end BioLib.Sim
