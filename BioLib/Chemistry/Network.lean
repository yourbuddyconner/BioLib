import BioLib.Chemistry.Reaction

/-!
# Reaction networks, stoichiometric matrices and mass balance

A network is a family of reactions indexed by a type `R`, over a species type
`S`.  Its stoichiometric matrix has one row per species and one column per
reaction.  For a flux vector `v` the rate of concentration change is `S v`, and
`v` is a steady-state flux when `S v = 0`.

Matrices, `mulVec` and `dotProduct` are Mathlib's.
-/

open Matrix

namespace BioLib.Chemistry

/-- A reaction network: reactions indexed by `R` over species `S`. -/
structure Network (S R : Type*) where
  /-- The reaction with index `j`. -/
  reaction : R → Reaction S

namespace Network

variable {S R R' : Type*}

/-- The integer stoichiometric matrix: rows are species, columns are reactions. -/
def stoichMatrix (N : Network S R) : Matrix S R ℤ :=
  Matrix.of fun s j => (N.reaction j).netChange s

/-- The stoichiometric matrix with real entries, for use with real fluxes. -/
noncomputable def realStoichMatrix (N : Network S R) : Matrix S R ℝ :=
  Matrix.of fun s j => ((N.reaction j).netChange s : ℝ)

@[simp] theorem stoichMatrix_apply (N : Network S R) (s : S) (j : R) :
    N.stoichMatrix s j = (N.reaction j).netChange s := rfl

@[simp] theorem realStoichMatrix_apply (N : Network S R) (s : S) (j : R) :
    N.realStoichMatrix s j = ((N.reaction j).netChange s : ℝ) := rfl

/-- Combine two networks over the same species by taking all reactions of both. -/
def union (N₁ : Network S R) (N₂ : Network S R') : Network S (R ⊕ R') :=
  ⟨Sum.elim N₁.reaction N₂.reaction⟩

@[simp] theorem union_reaction_inl (N₁ : Network S R) (N₂ : Network S R') (j : R) :
    (N₁.union N₂).reaction (Sum.inl j) = N₁.reaction j := rfl

@[simp] theorem union_reaction_inr (N₁ : Network S R) (N₂ : Network S R') (j : R') :
    (N₁.union N₂).reaction (Sum.inr j) = N₂.reaction j := rfl

section Flux

variable [Fintype R]

/-- Rate of concentration change `ẋ = S v` produced by the flux vector `v`. -/
noncomputable def rateOfChange (N : Network S R) (v : R → ℝ) : S → ℝ :=
  N.realStoichMatrix *ᵥ v

theorem rateOfChange_apply (N : Network S R) (v : R → ℝ) (s : S) :
    N.rateOfChange v s = ∑ j, ((N.reaction j).netChange s : ℝ) * v j := rfl

/-- Steady-state mass balance: `S v = 0`. -/
def IsSteadyState (N : Network S R) (v : R → ℝ) : Prop :=
  N.rateOfChange v = 0

/-- The zero flux vector satisfies steady-state mass balance. -/
theorem isSteadyState_zero (N : Network S R) : N.IsSteadyState 0 :=
  Matrix.mulVec_zero _

theorem IsSteadyState.add {N : Network S R} {v w : R → ℝ}
    (hv : N.IsSteadyState v) (hw : N.IsSteadyState w) : N.IsSteadyState (v + w) := by
  unfold IsSteadyState rateOfChange at *
  rw [Matrix.mulVec_add, hv, hw, add_zero]

theorem IsSteadyState.smul {N : Network S R} {v : R → ℝ}
    (hv : N.IsSteadyState v) (a : ℝ) : N.IsSteadyState (a • v) := by
  unfold IsSteadyState rateOfChange at *
  rw [Matrix.mulVec_smul, hv, smul_zero]

/-- In a union of networks the rates of change add. -/
theorem rateOfChange_union [Fintype R'] (N₁ : Network S R) (N₂ : Network S R')
    (v : R ⊕ R' → ℝ) :
    (N₁.union N₂).rateOfChange v =
      N₁.rateOfChange (v ∘ Sum.inl) + N₂.rateOfChange (v ∘ Sum.inr) := by
  funext s
  simp [rateOfChange_apply, Fintype.sum_sum_type]

end Flux

end Network

end BioLib.Chemistry
