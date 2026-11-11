import BioLib.Chemistry.Network

/-!
# Conservation laws

A weight vector `c` on species is a conservation law of a network when it
annihilates the stoichiometric matrix from the left, `cᵀ S = 0`.  The weighted
total `c · x` is then unchanged by every flux vector, and constant along every
trajectory of `ẋ = S v(t)`, whatever the kinetics that produce `v`.
-/

open Matrix

namespace BioLib.Chemistry.Network

variable {S R R' : Type*} [Fintype S]

/-- `c` is a conservation law of `N` when `cᵀ S = 0`. -/
def IsConservationLaw (N : Network S R) (c : S → ℝ) : Prop :=
  c ᵥ* N.realStoichMatrix = 0

/-- Reaction-by-reaction form: every reaction leaves the weighted total unchanged. -/
theorem isConservationLaw_iff {N : Network S R} {c : S → ℝ} :
    N.IsConservationLaw c ↔ ∀ j, ∑ s, c s * ((N.reaction j).netChange s : ℝ) = 0 := by
  unfold IsConservationLaw
  rw [funext_iff]
  rfl

theorem isConservationLaw_zero (N : Network S R) : N.IsConservationLaw 0 :=
  Matrix.zero_vecMul _

theorem IsConservationLaw.add {N : Network S R} {c d : S → ℝ}
    (hc : N.IsConservationLaw c) (hd : N.IsConservationLaw d) :
    N.IsConservationLaw (c + d) := by
  unfold IsConservationLaw at *
  rw [Matrix.add_vecMul, hc, hd, add_zero]

theorem IsConservationLaw.smul {N : Network S R} {c : S → ℝ}
    (hc : N.IsConservationLaw c) (a : ℝ) : N.IsConservationLaw (a • c) := by
  unfold IsConservationLaw at *
  rw [Matrix.smul_vecMul, hc, smul_zero]

/-- Composition: a weight vector is conserved by the union of two networks over
the same species exactly when it is conserved by each of them.

The compatibility conditions are that both networks use the same species type
(so that a shared species really is the same index) and that the same weight
vector is a conservation law of both. -/
theorem isConservationLaw_union_iff {N₁ : Network S R} {N₂ : Network S R'} {c : S → ℝ} :
    (N₁.union N₂).IsConservationLaw c ↔ N₁.IsConservationLaw c ∧ N₂.IsConservationLaw c := by
  simp only [isConservationLaw_iff, Sum.forall, union_reaction_inl, union_reaction_inr]

/-- Conservation is preserved by composition of networks. -/
theorem IsConservationLaw.union {N₁ : Network S R} {N₂ : Network S R'} {c : S → ℝ}
    (h₁ : N₁.IsConservationLaw c) (h₂ : N₂.IsConservationLaw c) :
    (N₁.union N₂).IsConservationLaw c :=
  isConservationLaw_union_iff.2 ⟨h₁, h₂⟩

variable [Fintype R]

/-- A conserved weighted total has zero rate of change under any flux vector. -/
theorem IsConservationLaw.dotProduct_rateOfChange {N : Network S R} {c : S → ℝ}
    (h : N.IsConservationLaw c) (v : R → ℝ) : c ⬝ᵥ N.rateOfChange v = 0 := by
  have h' : c ᵥ* N.realStoichMatrix = 0 := h
  rw [rateOfChange, Matrix.dotProduct_mulVec, h', zero_dotProduct]

/-- A conserved weighted total is constant along every trajectory of
`ẋ = S v(t)`, for an arbitrary time-dependent flux `v`. -/
theorem IsConservationLaw.dotProduct_trajectory_eq {N : Network S R} {c : S → ℝ}
    (h : N.IsConservationLaw c) {x : ℝ → S → ℝ} {v : ℝ → R → ℝ}
    (hx : ∀ t, HasDerivAt x (N.rateOfChange (v t)) t) (t₁ t₂ : ℝ) :
    c ⬝ᵥ x t₁ = c ⬝ᵥ x t₂ := by
  have hd : ∀ t, HasDerivAt (fun t => c ⬝ᵥ x t) 0 t := by
    intro t
    have h1 : ∀ s ∈ Finset.univ,
        HasDerivAt (fun t => c s * x t s) (c s * N.rateOfChange (v t) s) t :=
      fun s _ => ((hasDerivAt_pi.1 (hx t)) s).const_mul (c s)
    have h2 := HasDerivAt.fun_sum h1
    have h0 : ∑ s, c s * N.rateOfChange (v t) s = 0 := h.dotProduct_rateOfChange (v t)
    rw [h0] at h2
    exact h2
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t₁ t₂

end BioLib.Chemistry.Network
