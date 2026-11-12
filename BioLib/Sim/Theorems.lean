import BioLib.Sim.Core
import BioLib.Ecology.Competition
import BioLib.Ecology.Inhibition
import BioLib.Chemistry.Conservation

/-!
# Theorems about the simulator core

The definitions in `BioLib.Sim.Core` are generic over the number type.  This
file instantiates them at the real numbers (or any field) and proves:

* the simulated rate law is the library's generalized Lotka–Volterra field;
* storing states in arrays does not change the computed values;
* an Euler step keeps a present species present under a step-size condition,
  and keeps an absent species absent;
* an Euler step preserves every linear conservation law of a reaction network
  exactly, for any step size;
* relative abundances sum to one, and are unchanged when every abundance is
  multiplied by the same nonzero factor.  So absolute abundance cannot be
  recovered from relative abundance, and measurement bias is only identifiable
  up to a common factor.

**Scope.**  These are statements about the definitions evaluated in exact
arithmetic.  The executable evaluates the same definitions in floating point,
where they hold only approximately; `biolib-sim --selfcheck` measures the
difference from exact rational arithmetic on a small system.  The random
sampling code in `BioLib.Sim.Run` is not covered by any theorem.  One known
divergence: for an all-zero state `relAbundance` is `0` over the reals (Lean's
`0 / 0 = 0`) and NaN in floating point; the runtime handles that case separately.  Nothing here
bounds the error of the Euler method against the true solution of the ODE.
-/

open Matrix

namespace BioLib.Sim

variable {n : ℕ}

/-- The fold-based sum is the usual finite sum. -/
theorem sumFin_eq_sum {α : Type} [AddCommMonoid α] (f : Fin n → α) :
    sumFin f = ∑ i, f i := by
  unfold sumFin
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    congr 1
    exact ih fun i => f i.castSucc

/-- Storing a state in an array and applying a map gives that map's values. -/
theorem stepVec_getElem {α : Type} (f : (Fin n → α) → Fin n → α) (v : Vector α n)
    (i : Fin n) : (stepVec f v)[i] = f (fun j => v[j]) i := by
  simp [stepVec]

/-- The simulated rate law is the generalized Lotka–Volterra field of `BioLib.Ecology`. -/
theorem glvRate_eq_glvField (r : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    glvRate r A x = Ecology.glvField r (Matrix.of A) x := by
  funext i
  simp [glvRate, Ecology.glvField, sumFin_eq_sum, Matrix.mulVec, dotProduct]

/-- The simulated growth rates under inhibition are `netGrowthRate`, species by species. -/
theorem inhibitedRates_eq_netGrowthRate (r s : Fin n → ℝ) (B : ℝ) (i : Fin n) :
    inhibitedRates r s B i = Ecology.netGrowthRate (r i) (s i) B := rfl

section Euler

variable {r : Fin n → ℝ} {A : Fin n → Fin n → ℝ} {x : Fin n → ℝ} {h : ℝ} {i : Fin n}

/-- An Euler step of the Lotka–Volterra model multiplies each abundance by
`1 + h * (per-capita rate)`. -/
theorem eulerStep_glvRate (r : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (h : ℝ) (i : Fin n) :
    eulerStep (glvRate r A) h x i = x i * (1 + h * (r i + ∑ j, A i j * x j)) := by
  simp only [eulerStep, glvRate, sumFin_eq_sum]
  ring

/-- A present species stays present after an Euler step, provided the step
does not remove more than the whole population: `h * (per-capita rate) > -1`. -/
theorem eulerStep_glvRate_pos (hx : 0 < x i) (hstep : -1 < h * (r i + ∑ j, A i j * x j)) :
    0 < eulerStep (glvRate r A) h x i := by
  rw [eulerStep_glvRate]
  exact mul_pos hx (by linarith)

/-- An absent species stays absent after an Euler step. -/
theorem eulerStep_glvRate_absent (hx : x i = 0) : eulerStep (glvRate r A) h x i = 0 := by
  rw [eulerStep_glvRate, hx, zero_mul]

/-- An Euler step preserves every linear conservation law of a reaction
network exactly, for any step size and any state-dependent flux. -/
theorem eulerStep_conserves {R : Type*} [Fintype R] {N : Chemistry.Network (Fin n) R}
    {c : Fin n → ℝ} (hc : N.IsConservationLaw c) (v : (Fin n → ℝ) → R → ℝ) (h : ℝ)
    (x : Fin n → ℝ) :
    c ⬝ᵥ eulerStep (fun y => N.rateOfChange (v y)) h x = c ⬝ᵥ x := by
  have hstep : eulerStep (fun y => N.rateOfChange (v y)) h x = x + h • N.rateOfChange (v x) := by
    funext i
    simp [eulerStep]
  rw [hstep, dotProduct_add, dotProduct_smul, hc.dotProduct_rateOfChange, smul_zero, add_zero]

end Euler

section Observation

variable {𝕜 : Type} [Field 𝕜] {x : Fin n → 𝕜}

/-- Relative abundances sum to one when the total is nonzero. -/
theorem sum_relAbundance (hx : ∑ i, x i ≠ 0) : ∑ i, relAbundance x i = 1 := by
  simp only [relAbundance, sumFin_eq_sum]
  rw [← Finset.sum_div, div_self hx]

/-- Scale invariance: multiplying every abundance by the same nonzero factor
leaves relative abundance unchanged. -/
theorem relAbundance_scale {c : 𝕜} (hc : c ≠ 0) (x : Fin n → 𝕜) :
    relAbundance (fun i => c * x i) = relAbundance x := by
  funext i
  simp only [relAbundance, sumFin_eq_sum]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- Relative abundance does not determine total abundance: for any state with
nonzero total there is a different state with the same relative abundances. -/
theorem relAbundance_not_injective [CharZero 𝕜] (hx : ∑ i, x i ≠ 0) :
    ∃ y : Fin n → 𝕜, relAbundance y = relAbundance x ∧ ∑ i, y i ≠ ∑ i, x i := by
  refine ⟨fun i => 2 * x i, relAbundance_scale two_ne_zero x, ?_⟩
  rw [← Finset.mul_sum]
  intro h
  have : (2 - 1) * ∑ i, x i = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 this with h2 | h2
  · norm_num at h2
  · exact hx h2

/-- Measurement bias is identifiable only up to a common factor: scaling the
bias of every species by the same nonzero constant gives the same observation. -/
theorem relAbundance_applyBias_scale {c : 𝕜} (hc : c ≠ 0) (b x : Fin n → 𝕜) :
    relAbundance (applyBias (fun i => c * b i) x) = relAbundance (applyBias b x) := by
  have : applyBias (fun i => c * b i) x = fun i => c * applyBias b x i := by
    funext i
    simp [applyBias, mul_assoc]
  rw [this, relAbundance_scale hc]

end Observation

end BioLib.Sim
