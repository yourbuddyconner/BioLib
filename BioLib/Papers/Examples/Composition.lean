import BioLib.Papers.Examples.NutrientResponse
import BioLib.Papers.Examples.MicrobialInhibition

/-!
# Composition: a nutrient threshold for suppression

Model A (`NutrientResponse`) maps nutrient level to compound level.  Model B
(`MicrobialInhibition`) maps compound level to net growth.  Neither imports the
other.  Their shared interface is one real number, the compound concentration,
and the composed model is literally function composition:

`g(B(N)) = r - α * Bmax * N / (K + N)`.

Main result: if `α * Bmax > r`, then every nutrient level above
`r * K / (α * Bmax - r)` gives negative net growth, and a population held at
that nutrient level declines to extinction.  If `α * Bmax ≤ r`, no nonnegative
nutrient level gives negative growth.

The proofs go through the lemmas of the two component models (`lt_saturation_iff`
and `netGrowth_neg_iff`), not through an expanded formula.

**Compatibility assumptions that Lean does not check.**  The composition is only
meaningful if the compound produced in Model A is the compound acting in Model
B, measured in the same unit and in the same compartment, and if production
equilibrates fast relative to population change.
-/

open Filter Topology

namespace BioLib.Papers.Examples.Composition

open BioLib BioLib.Ecology
open NutrientResponse MicrobialInhibition

variable (a : NutrientResponse.Params) (b : MicrobialInhibition.Params) {N : ℝ}

/-- Net growth of the target population as a function of nutrient level. -/
noncomputable def composedGrowth (N : ℝ) : ℝ := netGrowth b (production a N)

/-- The composed model written out. -/
theorem composedGrowth_eq (N : ℝ) :
    composedGrowth a b N = b.r - b.α * (a.Bmax * N / (a.K + N)) := rfl

/-- Nutrient level above which the target population is suppressed. -/
noncomputable def suppressionThreshold : ℝ := b.r * a.K / (b.α * a.Bmax - b.r)

theorem suppressionThreshold_pos (h : b.r < b.α * a.Bmax) : 0 < suppressionThreshold a b :=
  div_pos (mul_pos b.r_pos a.K_pos) (by linarith)

/-- The threshold of the composed model is the inversion point of Model A at
Model B's critical compound level `r / α`. -/
theorem suppressionThreshold_eq (h : b.r < b.α * a.Bmax) :
    suppressionThreshold a b = b.r / b.α * a.K / (a.Bmax - b.r / b.α) := by
  have hα := b.α_pos
  have h1 : b.α * a.Bmax - b.r ≠ 0 := by linarith
  have h2 : a.Bmax - b.r / b.α ≠ 0 := by
    have : b.r / b.α < a.Bmax := by rw [div_lt_iff₀ hα]; linarith
    linarith
  unfold suppressionThreshold
  field_simp

/-- For nonnegative nutrient levels, growth is negative exactly above the threshold. -/
theorem composedGrowth_neg_iff (h : b.r < b.α * a.Bmax) (hN : 0 ≤ N) :
    composedGrowth a b N < 0 ↔ suppressionThreshold a b < N := by
  have hlt : b.r / b.α < a.Bmax := by rw [div_lt_iff₀ b.α_pos]; linarith
  rw [composedGrowth, netGrowth_neg_iff, production, lt_saturation_iff a.K_pos hN hlt,
    suppressionThreshold_eq a b h]

/-- **Nutrient threshold theorem.**  Assuming `α * Bmax > r`,
`N > r * K / (α * Bmax - r)` implies `g(B(N)) < 0`. -/
theorem composedGrowth_neg_of_threshold_lt (h : b.r < b.α * a.Bmax)
    (hN : suppressionThreshold a b < N) : composedGrowth a b N < 0 :=
  (composedGrowth_neg_iff a b h ((suppressionThreshold_pos a b h).le.trans hN.le)).2 hN

/-- If the compound cannot reach the critical level even at saturation
(`α * Bmax ≤ r`), growth stays positive at every nonnegative nutrient level. -/
theorem composedGrowth_pos_of_max_le (h : b.α * a.Bmax ≤ b.r) (hN : 0 ≤ N) :
    0 < composedGrowth a b N := by
  rw [composedGrowth, netGrowth_pos_iff]
  have h1 : a.Bmax ≤ b.r / b.α := by rw [le_div_iff₀ b.α_pos]; linarith
  exact (production_lt_max a hN).trans_le h1

/-- Dynamic consequence: at a constant nutrient level above the threshold, a
positive population following `dP/dt = g(B(N)) * P` strictly declines. -/
theorem population_strictAnti_of_threshold_lt (h : b.r < b.α * a.Bmax)
    (hN : suppressionThreshold a b < N) {P₀ : ℝ} (hP : 0 < P₀) :
    StrictAnti (expTrajectory P₀ (composedGrowth a b N)) :=
  expTrajectory_strictAnti hP (composedGrowth_neg_of_threshold_lt a b h hN)

/-- Dynamic consequence: under the same conditions the population tends to zero. -/
theorem population_tendsto_zero_of_threshold_lt (h : b.r < b.α * a.Bmax)
    (hN : suppressionThreshold a b < N) (P₀ : ℝ) :
    Tendsto (expTrajectory P₀ (composedGrowth a b N)) atTop (𝓝 0) :=
  tendsto_expTrajectory_atTop_zero P₀ (composedGrowth_neg_of_threshold_lt a b h hN)

end BioLib.Papers.Examples.Composition
