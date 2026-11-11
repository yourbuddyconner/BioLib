import BioLib.Foundations.Dynamics

/-!
# Growth inhibition by an antimicrobial compound

The linear inhibition model `dP/dt = (r - α * B) * P`:

* `P` microbial abundance;
* `r` intrinsic growth rate;
* `α` inhibition sensitivity;
* `B` antimicrobial compound concentration.

For constant `B` the net per-capita rate `r - α * B` is constant, the dynamics
are linear, and the population declines exactly when `B > r / α`.
-/

open Filter Topology

namespace BioLib.Ecology

/-- Net per-capita growth rate `r - α * B` under linear inhibition. -/
def netGrowthRate (r α B : ℝ) : ℝ := r - α * B

/-- Inhibited growth rate law `dP/dt = (r - α * B) * P`. -/
def inhibitedRate (r α B P : ℝ) : ℝ := netGrowthRate r α B * P

variable {r α B P₀ : ℝ}

@[simp] theorem netGrowthRate_zero (r α : ℝ) : netGrowthRate r α 0 = r := by
  simp [netGrowthRate]

/-- More compound means slower net growth. -/
theorem netGrowthRate_strictAnti (hα : 0 < α) : StrictAnti (netGrowthRate r α) := by
  intro a b hab
  unfold netGrowthRate
  nlinarith [mul_lt_mul_of_pos_left hab hα]

/-- Criterion for negative net growth: the compound concentration exceeds `r / α`. -/
theorem netGrowthRate_neg_iff (hα : 0 < α) : netGrowthRate r α B < 0 ↔ r / α < B := by
  unfold netGrowthRate
  rw [div_lt_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- Criterion for positive net growth. -/
theorem netGrowthRate_pos_iff (hα : 0 < α) : 0 < netGrowthRate r α B ↔ B < r / α := by
  unfold netGrowthRate
  rw [lt_div_iff₀ hα]
  constructor <;> intro h <;> linarith

/-- For constant `B`, the exponential trajectory with rate `r - α * B` solves the
inhibited growth law. -/
theorem hasDerivAt_inhibited (P₀ r α B t : ℝ) :
    HasDerivAt (expTrajectory P₀ (netGrowthRate r α B))
      (inhibitedRate r α B (expTrajectory P₀ (netGrowthRate r α B) t)) t :=
  hasDerivAt_expTrajectory P₀ _ t

/-- For constant `B`, that trajectory is the only solution. -/
theorem eq_expTrajectory_of_inhibited {P : ℝ → ℝ}
    (hP : ∀ t, HasDerivAt P (inhibitedRate r α B (P t)) t) (t : ℝ) :
    P t = expTrajectory (P 0) (netGrowthRate r α B) t :=
  eq_expTrajectory_of_hasDerivAt hP t

/-- With negative net growth a positive population strictly declines. -/
theorem population_strictAnti_of_netGrowthRate_neg (hP : 0 < P₀)
    (h : netGrowthRate r α B < 0) : StrictAnti (expTrajectory P₀ (netGrowthRate r α B)) :=
  expTrajectory_strictAnti hP h

/-- With negative net growth the population tends to extinction. -/
theorem population_tendsto_zero_of_netGrowthRate_neg (P₀ : ℝ)
    (h : netGrowthRate r α B < 0) :
    Tendsto (expTrajectory P₀ (netGrowthRate r α B)) atTop (𝓝 0) :=
  tendsto_expTrajectory_atTop_zero P₀ h

end BioLib.Ecology
