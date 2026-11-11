import Mathlib

/-!
# Stoichiometric reactions

A reaction over a species type `S` is a pair of nonnegative integer coefficient
functions, one for the reactant side and one for the product side.  For
`A + 2B → C` the reactant coefficients are `A ↦ 1, B ↦ 2, C ↦ 0` and the product
coefficients are `A ↦ 0, B ↦ 0, C ↦ 1`.

The species type is a parameter, so "species" is whatever index type a model
needs.  No ontology of chemical entities is imposed.
-/

namespace BioLib.Chemistry

/-- A stoichiometric reaction over species `S`. -/
structure Reaction (S : Type*) where
  /-- Stoichiometric coefficient of each species on the reactant side. -/
  reactants : S → ℕ
  /-- Stoichiometric coefficient of each species on the product side. -/
  products : S → ℕ

namespace Reaction

variable {S : Type*}

/-- Net change in the count of species `s` when the reaction fires once. -/
def netChange (r : Reaction S) (s : S) : ℤ :=
  (r.products s : ℤ) - (r.reactants s : ℤ)

/-- A reaction with identical reactant and product sides changes nothing. -/
theorem netChange_eq_zero_of_reactants_eq_products (r : Reaction S)
    (h : r.reactants = r.products) : r.netChange = 0 := by
  funext s
  simp [netChange, h]

/-- The reverse reaction. -/
def reverse (r : Reaction S) : Reaction S := ⟨r.products, r.reactants⟩

@[simp] theorem netChange_reverse (r : Reaction S) : r.reverse.netChange = -r.netChange := by
  funext s
  simp [netChange, reverse]

end Reaction

end BioLib.Chemistry
