import BioLib.Chemistry.Conservation

/-!
# Mass-action kinetics

Under mass action a reaction with rate constant `k` fires at rate
`k * ∏ s, x s ^ (reactant coefficient of s)`.  Feeding these rates into the
stoichiometric matrix gives the mass-action vector field of a network.

Conservation laws are a property of stoichiometry alone, so they hold for the
mass-action field without any assumption on the rate constants.
-/

open Matrix

namespace BioLib.Chemistry

variable {S R : Type*} [Fintype S]

/-- Mass-action rate of a single reaction at concentrations `x`. -/
noncomputable def Reaction.massActionRate (r : Reaction S) (k : ℝ) (x : S → ℝ) : ℝ :=
  k * ∏ s, x s ^ r.reactants s

theorem Reaction.massActionRate_nonneg (r : Reaction S) {k : ℝ} {x : S → ℝ}
    (hk : 0 ≤ k) (hx : ∀ s, 0 ≤ x s) : 0 ≤ r.massActionRate k x :=
  mul_nonneg hk (Finset.prod_nonneg fun s _ => pow_nonneg (hx s) _)

namespace Network

/-- Mass-action flux vector for rate constants `k` at concentrations `x`. -/
noncomputable def massActionFlux (N : Network S R) (k : R → ℝ) (x : S → ℝ) : R → ℝ :=
  fun j => (N.reaction j).massActionRate (k j) x

variable [Fintype R]

/-- Mass-action vector field: the right-hand side of `ẋ = S v(x)`. -/
noncomputable def massActionField (N : Network S R) (k : R → ℝ) (x : S → ℝ) : S → ℝ :=
  N.rateOfChange (N.massActionFlux k x)

/-- Conservation laws hold for the mass-action field, for any rate constants. -/
theorem IsConservationLaw.dotProduct_massActionField {N : Network S R} {c : S → ℝ}
    (h : N.IsConservationLaw c) (k : R → ℝ) (x : S → ℝ) :
    c ⬝ᵥ N.massActionField k x = 0 :=
  h.dotProduct_rateOfChange _

end Network

end BioLib.Chemistry
