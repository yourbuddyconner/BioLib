import Mathlib

/-!
# Linear scalar dynamics

The linear ODE `x' = a * x` underlies exponential growth, first-order decay and
constant-rate inhibition.  This file gives its closed-form solution and proves
that the closed form is the *only* solution, so qualitative statements about the
formula are statements about the dynamics.

All results are over the mathematical reals.  Nothing here says anything about
floating-point simulation.
-/

open Filter Topology

namespace BioLib

/-- The closed-form solution `x₀ * exp (a * t)` of `x' = a * x` with `x 0 = x₀`. -/
noncomputable def expTrajectory (x₀ a t : ℝ) : ℝ := x₀ * Real.exp (a * t)

variable {x₀ a : ℝ}

@[simp] theorem expTrajectory_zero (x₀ a : ℝ) : expTrajectory x₀ a 0 = x₀ := by
  simp [expTrajectory]

theorem expTrajectory_pos (hx : 0 < x₀) (t : ℝ) : 0 < expTrajectory x₀ a t :=
  mul_pos hx (Real.exp_pos _)

/-- `expTrajectory x₀ a` solves `x' = a * x`. -/
theorem hasDerivAt_expTrajectory (x₀ a t : ℝ) :
    HasDerivAt (expTrajectory x₀ a) (a * expTrajectory x₀ a t) t := by
  have h : HasDerivAt (fun t => a * t) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun t => x₀ * Real.exp (a * t)) (x₀ * (Real.exp (a * t) * a)) t :=
    h.exp.const_mul x₀
  exact h2.congr_deriv (by unfold expTrajectory; ring)

/-- Uniqueness: every solution of `x' = a * x` on the whole real line is the
exponential trajectory through its value at time `0`. -/
theorem eq_expTrajectory_of_hasDerivAt {x : ℝ → ℝ} {a : ℝ}
    (hx : ∀ t, HasDerivAt x (a * x t) t) (t : ℝ) :
    x t = expTrajectory (x 0) a t := by
  have hd : ∀ t, HasDerivAt (fun t => x t * Real.exp (-a * t)) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t => -a * t) (-a) t := by
      simpa using (hasDerivAt_id t).const_mul (-a)
    exact ((hx t).mul h1.exp).congr_deriv (by ring)
  have hc : x t * Real.exp (-a * t) = x 0 * Real.exp (-a * 0) :=
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  simp only [mul_zero, Real.exp_zero, mul_one] at hc
  rw [expTrajectory, ← hc, mul_assoc, ← Real.exp_add]
  simp

/-- A positive quantity with a negative rate coefficient strictly decreases. -/
theorem expTrajectory_strictAnti (hx : 0 < x₀) (ha : a < 0) :
    StrictAnti (expTrajectory x₀ a) := by
  intro s t hst
  have h : a * t < a * s := mul_lt_mul_of_neg_left hst ha
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 h) hx

/-- A positive quantity with a positive rate coefficient strictly increases. -/
theorem expTrajectory_strictMono (hx : 0 < x₀) (ha : 0 < a) :
    StrictMono (expTrajectory x₀ a) := by
  intro s t hst
  have h : a * s < a * t := mul_lt_mul_of_pos_left hst ha
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 h) hx

/-- With a negative rate coefficient the trajectory decays to zero. -/
theorem tendsto_expTrajectory_atTop_zero (x₀ : ℝ) (ha : a < 0) :
    Tendsto (expTrajectory x₀ a) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => a * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg ha
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul x₀
  simpa [expTrajectory, Function.comp_def] using h2

end BioLib
