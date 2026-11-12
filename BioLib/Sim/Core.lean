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

/-- `observe`, computing the total once instead of once per component. -/
def observeFast (b : Fin n → α) (v : Vector α n) : Vector α n :=
  let w := stepVec (applyBias b) v
  let total := sumFin fun i : Fin n => w[i]
  w.map (· / total)

end BioLib.Sim
