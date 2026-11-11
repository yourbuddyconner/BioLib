import BioLib.Foundations.Dynamics
import BioLib.Foundations.Saturation

/-!
# Single-population growth laws

Rate laws for one population with abundance `P`:

* exponential growth `dP/dt = r * P`, with its closed-form solution;
* logistic growth `dP/dt = r * P * (1 - P / K)`;
* nutrient-dependent (Monod) per-capita growth `μmax * N / (Ks + N)`.

Abundances are bare real numbers.  Units (cells, CFU/mL, optical density) are
not tracked by the type system.
-/

namespace BioLib.Ecology

/-- Exponential growth rate law `dP/dt = r * P`. -/
def exponentialRate (r P : ℝ) : ℝ := r * P

/-- The exponential trajectory solves the exponential rate law. -/
theorem hasDerivAt_exponential (P₀ r t : ℝ) :
    HasDerivAt (expTrajectory P₀ r) (exponentialRate r (expTrajectory P₀ r t)) t :=
  hasDerivAt_expTrajectory P₀ r t

/-- Logistic growth rate law `dP/dt = r * P * (1 - P / K)` with carrying capacity `K`. -/
noncomputable def logisticRate (r K P : ℝ) : ℝ := r * P * (1 - P / K)

variable {r K P : ℝ}

@[simp] theorem logisticRate_zero (r K : ℝ) : logisticRate r K 0 = 0 := by
  simp [logisticRate]

/-- The carrying capacity is an equilibrium. -/
theorem logisticRate_capacity (r : ℝ) (hK : K ≠ 0) : logisticRate r K K = 0 := by
  simp [logisticRate, div_self hK]

/-- Below carrying capacity the population grows. -/
theorem logisticRate_pos (hr : 0 < r) (hP : 0 < P) (hPK : P < K) :
    0 < logisticRate r K P := by
  have hK : 0 < K := hP.trans hPK
  have h : P / K < 1 := (div_lt_one hK).2 hPK
  exact mul_pos (mul_pos hr hP) (by linarith)

/-- Above carrying capacity the population shrinks. -/
theorem logisticRate_neg (hr : 0 < r) (hK : 0 < K) (hPK : K < P) :
    logisticRate r K P < 0 := by
  have h : 1 < P / K := (one_lt_div hK).2 hPK
  exact mul_neg_of_pos_of_neg (mul_pos hr (hK.trans hPK)) (by linarith)

/-- Logistic growth never exceeds exponential growth at the same intrinsic rate. -/
theorem logisticRate_le_exponentialRate (hr : 0 ≤ r) (hK : 0 < K) (hP : 0 ≤ P) :
    logisticRate r K P ≤ exponentialRate r P := by
  have h : 0 ≤ P / K := div_nonneg hP hK.le
  unfold logisticRate exponentialRate
  nlinarith [mul_nonneg (mul_nonneg hr hP) h]

/-- Monod per-capita growth rate as a function of nutrient concentration `N`.
This is the shared `saturation` response under its ecological name. -/
noncomputable abbrev monodRate (μmax Ks N : ℝ) : ℝ := saturation μmax Ks N

end BioLib.Ecology
