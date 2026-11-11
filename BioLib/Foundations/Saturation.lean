import Mathlib

/-!
# Hyperbolic saturation response

The function `x ↦ vmax * x / (K + x)` appears across biology under different
names: Michaelis–Menten rate law, Monod growth law, Holling type II response,
Langmuir isotherm.  It is defined once here, with the properties that downstream
models need, so that each domain can reuse the same lemmas.

The half-saturation constant `K` is required to be positive and the argument
nonnegative wherever the denominator matters.  Outside that range the formula is
still defined (Lean's division is total, `a / 0 = 0`) but has no intended meaning.
-/

namespace BioLib

/-- Hyperbolic saturation: `vmax * x / (K + x)`. -/
noncomputable def saturation (vmax K x : ℝ) : ℝ := vmax * x / (K + x)

variable {vmax K x y : ℝ}

@[simp] theorem saturation_zero (vmax K : ℝ) : saturation vmax K 0 = 0 := by
  simp [saturation]

/-- At `x = K` the response is half of its maximum. -/
theorem saturation_half (vmax : ℝ) (hK : K ≠ 0) : saturation vmax K K = vmax / 2 := by
  unfold saturation
  field_simp
  ring

theorem saturation_nonneg (hv : 0 ≤ vmax) (hK : 0 < K) (hx : 0 ≤ x) :
    0 ≤ saturation vmax K x :=
  div_nonneg (mul_nonneg hv hx) (by linarith)

/-- The response never reaches its supremum `vmax`. -/
theorem saturation_lt_max (hv : 0 < vmax) (hK : 0 < K) (hx : 0 ≤ x) :
    saturation vmax K x < vmax := by
  unfold saturation
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_pos hv hK]

theorem saturation_le_max (hv : 0 ≤ vmax) (hK : 0 < K) (hx : 0 ≤ x) :
    saturation vmax K x ≤ vmax := by
  unfold saturation
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hv hK.le]

/-- Strictly increasing on nonnegative inputs when `vmax` and `K` are positive. -/
theorem saturation_strictMonoOn (hv : 0 < vmax) (hK : 0 < K) :
    StrictMonoOn (saturation vmax K) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  unfold saturation
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_lt_mul_of_pos_left hab (mul_pos hv hK)]

/-- Monotone on nonnegative inputs. -/
theorem saturation_monotoneOn (hv : 0 < vmax) (hK : 0 < K) :
    MonotoneOn (saturation vmax K) (Set.Ici 0) :=
  (saturation_strictMonoOn hv hK).monotoneOn

/-- Inversion of the response: for a target level `y` below the maximum, the
response exceeds `y` exactly when the input exceeds `y * K / (vmax - y)`. -/
theorem lt_saturation_iff (hK : 0 < K) (hx : 0 ≤ x) (hy : y < vmax) :
    y < saturation vmax K x ↔ y * K / (vmax - y) < x := by
  unfold saturation
  rw [lt_div_iff₀ (by linarith), div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- If the target level is at or above the maximum, the response never exceeds it. -/
theorem saturation_le_of_max_le (hv : 0 ≤ vmax) (hK : 0 < K) (hx : 0 ≤ x) (hy : vmax ≤ y) :
    saturation vmax K x ≤ y :=
  (saturation_le_max hv hK hx).trans hy

end BioLib
