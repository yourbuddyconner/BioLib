import BioLib.Foundations.Saturation
import BioLib.Evidence.Provenance

/-!
# Model A: nutrient-dependent antimicrobial production

`B(N) = Bmax * N / (K + N)`: steady antimicrobial compound level as a
saturating function of nutrient concentration `N`.

**Illustrative model.**  This module shows the paper-module convention on a
generic saturation form.  It is not taken from, and must not be cited as, any
publication.  Its provenance record says so (`source := none`).
-/

namespace BioLib.Papers.Examples.NutrientResponse

open BioLib.Evidence

/-- Parameters of the production model, with their constraints. -/
structure Params where
  /-- Maximal compound level. -/
  Bmax : ℝ
  /-- Nutrient concentration at half-maximal production. -/
  K : ℝ
  Bmax_pos : 0 < Bmax
  K_pos : 0 < K

/-- Compound level at nutrient concentration `N`. -/
noncomputable def production (p : Params) (N : ℝ) : ℝ := saturation p.Bmax p.K N

variable (p : Params) {N : ℝ}

theorem production_nonneg (hN : 0 ≤ N) : 0 ≤ production p N :=
  saturation_nonneg p.Bmax_pos.le p.K_pos hN

theorem production_lt_max (hN : 0 ≤ N) : production p N < p.Bmax :=
  saturation_lt_max p.Bmax_pos p.K_pos hN

/-- Production is monotone in nutrient concentration on `N ≥ 0`. -/
theorem production_monotoneOn : MonotoneOn (production p) (Set.Ici 0) :=
  saturation_monotoneOn p.Bmax_pos p.K_pos

theorem production_strictMonoOn : StrictMonoOn (production p) (Set.Ici 0) :=
  saturation_strictMonoOn p.Bmax_pos p.K_pos

/-- Provenance record. -/
def record : ModelRecord where
  id := "BioLib.Papers.Examples.NutrientResponse"
  version := "0.1.0"
  source := none
  parameters :=
    [ { name := "Bmax", unit := "concentration", description := "maximal compound level" },
      { name := "K", unit := "concentration",
        description := "nutrient concentration at half-maximal production" } ]
  assumptions :=
    [ { name := "positive parameters", kind := .mathematical,
        statement := "Bmax > 0 and K > 0", formalizedAs := "Params.Bmax_pos, Params.K_pos" },
      { name := "quasi-steady production", kind := .modelling,
        statement := "the compound level is an instantaneous function of nutrient level" },
      { name := "saturating response", kind := .empirical,
        statement := "production follows a hyperbolic saturation curve in nutrient level" } ]
  applicability := "Nonnegative nutrient concentrations."

end BioLib.Papers.Examples.NutrientResponse
