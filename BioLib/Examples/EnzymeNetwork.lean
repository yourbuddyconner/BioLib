import BioLib.Chemistry.Kinetics

/-!
# Worked example: the enzyme–substrate mechanism

The network `E + S ⇌ ES → E + P` on four species and three reactions.

Two conservation laws are proved from the stoichiometry alone:

* total enzyme `E + ES`;
* total substrate `S + ES + P`.

As a consequence, total enzyme is constant along every trajectory of the
network, whatever rate laws drive the three reactions.  Free enzyme on its own
is shown *not* to be conserved, so the predicate is not vacuous.

This is a textbook mechanism used as a test of the abstractions.  It is not a
formalization of any particular publication.
-/

open Matrix

namespace BioLib.Examples.EnzymeNetwork

open BioLib.Chemistry

/-- Species: free enzyme, substrate, enzyme–substrate complex, product. -/
inductive Sp
  | E | S | ES | P
  deriving DecidableEq, Fintype

/-- Reactions: binding, unbinding, catalysis. -/
inductive Rx
  | bind | unbind | cat
  deriving DecidableEq, Fintype

/-- `E + S → ES`, `ES → E + S`, `ES → E + P`. -/
def network : Network Sp Rx where
  reaction
    | .bind => ⟨fun | .E => 1 | .S => 1 | _ => 0, fun | .ES => 1 | _ => 0⟩
    | .unbind => ⟨fun | .ES => 1 | _ => 0, fun | .E => 1 | .S => 1 | _ => 0⟩
    | .cat => ⟨fun | .ES => 1 | _ => 0, fun | .E => 1 | .P => 1 | _ => 0⟩

theorem sum_species (f : Sp → ℝ) : ∑ s, f s = f .E + f .S + f .ES + f .P := by
  have h : (Finset.univ : Finset Sp) = {.E, .S, .ES, .P} := by decide
  rw [h]
  simp [add_assoc]

/-- Weights counting enzyme in both its free and bound forms. -/
def totalEnzyme : Sp → ℝ
  | .E => 1 | .ES => 1 | _ => 0

/-- Weights counting substrate in free, bound and converted forms. -/
def totalSubstrate : Sp → ℝ
  | .S => 1 | .ES => 1 | .P => 1 | _ => 0

/-- Total enzyme `E + ES` is a conservation law. -/
theorem totalEnzyme_conserved : network.IsConservationLaw totalEnzyme := by
  rw [Network.isConservationLaw_iff]
  intro j
  cases j <;> simp [sum_species, network, totalEnzyme, Reaction.netChange]

/-- Total substrate `S + ES + P` is a conservation law. -/
theorem totalSubstrate_conserved : network.IsConservationLaw totalSubstrate := by
  rw [Network.isConservationLaw_iff]
  intro j
  cases j <;> simp [sum_species, network, totalSubstrate, Reaction.netChange]

/-- Free enzyme alone is not conserved: binding consumes it. -/
theorem freeEnzyme_not_conserved :
    ¬ network.IsConservationLaw (fun | .E => 1 | _ => 0) := by
  rw [Network.isConservationLaw_iff]
  intro h
  have := h .bind
  simp [sum_species, network, Reaction.netChange] at this

/-- Along any trajectory of the network, with arbitrary time-dependent fluxes,
the amount of enzyme `E + ES` stays at its initial value. -/
theorem enzyme_total_constant {x : ℝ → Sp → ℝ} {v : ℝ → Rx → ℝ}
    (hx : ∀ t, HasDerivAt x (network.rateOfChange (v t)) t) (t : ℝ) :
    x t .E + x t .ES = x 0 .E + x 0 .ES := by
  have h := totalEnzyme_conserved.dotProduct_trajectory_eq hx t 0
  simpa [dotProduct, sum_species, totalEnzyme] using h

end BioLib.Examples.EnzymeNetwork
