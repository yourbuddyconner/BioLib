import BioLib.Imported.EnzymeMechanism
import BioLib.Chemistry.Conservation

/-!
# A theorem about an imported SBML model

`BioLib.Imported.EnzymeMechanism` is generated from `examples/sbml/enzyme.xml`.
This hand-written file proves that total enzyme `E + ES` is a conservation law
of the imported network, which shows that generated networks work with the
library's theorems.

The SBML file is a hand-written test model, not a published one.
-/

namespace BioLib.Examples.ImportedEnzyme

open BioLib.Chemistry BioLib.Imported.EnzymeMechanism

theorem sum_species (f : Species → ℝ) : ∑ s, f s = f .E + f .S + f .ES + f .P := by
  have h : (Finset.univ : Finset Species) = {.E, .S, .ES, .P} := rfl
  rw [h]
  simp [add_assoc]

/-- Weights counting enzyme in free and bound form. -/
def totalEnzyme : Species → ℝ
  | .E => 1 | .ES => 1 | _ => 0

/-- Total enzyme is conserved by the imported network. -/
theorem totalEnzyme_conserved : network.IsConservationLaw totalEnzyme := by
  rw [Network.isConservationLaw_iff]
  intro j
  cases j <;> simp [sum_species, network, totalEnzyme, Reaction.netChange]

end BioLib.Examples.ImportedEnzyme
