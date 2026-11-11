import BioLib.Ecology.Inhibition
import BioLib.Evidence.Provenance

/-!
# Model B: microbial inhibition by an antimicrobial compound

`g(B) = r - α * B`: net per-capita growth rate of a target population at
compound concentration `B`, giving `dP/dt = g(B) * P`.

**Illustrative model.**  Not taken from any publication (`source := none`).
This module does not import Model A.
-/

namespace BioLib.Papers.Examples.MicrobialInhibition

open BioLib.Evidence BioLib.Ecology

/-- Parameters of the inhibition model, with their constraints. -/
structure Params where
  /-- Intrinsic growth rate. -/
  r : ℝ
  /-- Inhibition sensitivity. -/
  α : ℝ
  r_pos : 0 < r
  α_pos : 0 < α

/-- Net per-capita growth rate at compound concentration `B`. -/
def netGrowth (p : Params) (B : ℝ) : ℝ := netGrowthRate p.r p.α B

variable (p : Params) {B : ℝ}

/-- Net growth is negative exactly when `B` exceeds `r / α`. -/
theorem netGrowth_neg_iff : netGrowth p B < 0 ↔ p.r / p.α < B :=
  netGrowthRate_neg_iff p.α_pos

/-- Net growth is positive exactly when `B` is below `r / α`. -/
theorem netGrowth_pos_iff : 0 < netGrowth p B ↔ B < p.r / p.α :=
  netGrowthRate_pos_iff p.α_pos

/-- Provenance record. -/
def record : ModelRecord where
  id := "BioLib.Papers.Examples.MicrobialInhibition"
  version := "0.1.0"
  source := none
  parameters :=
    [ { name := "r", unit := "1/time", description := "intrinsic growth rate" },
      { name := "α", unit := "1/(time·concentration)",
        description := "inhibition sensitivity" } ]
  assumptions :=
    [ { name := "positive parameters", kind := .mathematical,
        statement := "r > 0 and α > 0", formalizedAs := "Params.r_pos, Params.α_pos" },
      { name := "constant compound level", kind := .modelling,
        statement := "B does not change over the time window considered" },
      { name := "linear dose response", kind := .empirical,
        statement := "the kill rate is proportional to compound concentration" } ]
  applicability :=
    "Concentrations where the dose response is approximately linear; no resistance evolution."

end BioLib.Papers.Examples.MicrobialInhibition
