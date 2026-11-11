import BioLib.Foundations.Saturation

/-!
# Hill function

`x ↦ vmax * (x / K) ^ n / (1 + (x / K) ^ n)`, the sigmoidal generalization of
the saturation response, with a real exponent `n` (the Hill coefficient).

It is defined as `saturation` applied to `(x / K) ^ n`, so its properties come
from the saturation lemmas and monotonicity of real powers.
-/

namespace BioLib

/-- Hill function with maximum `vmax`, half-maximum point `K` and coefficient `n`. -/
noncomputable def hill (vmax K n x : ℝ) : ℝ := saturation vmax 1 ((x / K) ^ n)

variable {vmax K n x y : ℝ}

theorem hill_eq (vmax K n x : ℝ) :
    hill vmax K n x = vmax * (x / K) ^ n / (1 + (x / K) ^ n) := rfl

@[simp] theorem hill_zero (vmax K : ℝ) (hn : n ≠ 0) : hill vmax K n 0 = 0 := by
  simp [hill, Real.zero_rpow hn]

/-- At `x = K` the Hill function is half of its maximum. -/
theorem hill_half (vmax n : ℝ) (hK : K ≠ 0) : hill vmax K n K = vmax / 2 := by
  unfold hill saturation
  rw [div_self hK, Real.one_rpow]
  ring

/-- With coefficient `1` the Hill function is the saturation response. -/
theorem hill_one (vmax : ℝ) (hK : 0 < K) (hx : 0 ≤ x) :
    hill vmax K 1 x = saturation vmax K x := by
  have h : K + x ≠ 0 := by linarith
  unfold hill saturation
  rw [Real.rpow_one]
  field_simp

theorem hill_nonneg (hv : 0 ≤ vmax) (hK : 0 < K) (hx : 0 ≤ x) : 0 ≤ hill vmax K n x :=
  saturation_nonneg hv one_pos (Real.rpow_nonneg (div_nonneg hx hK.le) n)

theorem hill_lt_max (hv : 0 < vmax) (hK : 0 < K) (hx : 0 ≤ x) : hill vmax K n x < vmax :=
  saturation_lt_max hv one_pos (Real.rpow_nonneg (div_nonneg hx hK.le) n)

/-- Strictly increasing on nonnegative inputs for a positive coefficient. -/
theorem hill_strictMonoOn (hv : 0 < vmax) (hK : 0 < K) (hn : 0 < n) :
    StrictMonoOn (hill vmax K n) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a / K := div_nonneg ha hK.le
  have hb' : 0 ≤ b / K := div_nonneg hb hK.le
  have h : (a / K) ^ n < (b / K) ^ n :=
    Real.rpow_lt_rpow ha' (div_lt_div_of_pos_right hab hK) hn
  exact saturation_strictMonoOn hv one_pos (Set.mem_Ici.2 (Real.rpow_nonneg ha' n))
    (Set.mem_Ici.2 (Real.rpow_nonneg hb' n)) h

/-- Inversion: for a level `0 ≤ y < vmax`, the Hill function exceeds `y` exactly
when the input exceeds `K * (y / (vmax - y)) ^ (1 / n)`. -/
theorem lt_hill_iff (hK : 0 < K) (hn : 0 < n) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y < vmax) :
    y < hill vmax K n x ↔ K * (y / (vmax - y)) ^ (1 / n) < x := by
  have hc : 0 ≤ y / (vmax - y) := div_nonneg hy0 (by linarith)
  have hxK : 0 ≤ x / K := div_nonneg hx hK.le
  have h1 : ((y / (vmax - y)) ^ (1 / n)) ^ n = y / (vmax - y) := by
    rw [← Real.rpow_mul hc, one_div_mul_cancel hn.ne', Real.rpow_one]
  rw [hill, lt_saturation_iff one_pos (Real.rpow_nonneg hxK n) hy, mul_one]
  constructor
  · intro h
    rw [← h1] at h
    have := (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hc _) hxK hn).1 h
    rw [lt_div_iff₀ hK] at this
    linarith
  · intro h
    have h2 : (y / (vmax - y)) ^ (1 / n) < x / K := by
      rw [lt_div_iff₀ hK]; linarith
    have := (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hc _) hxK hn).2 h2
    rwa [h1] at this

end BioLib
