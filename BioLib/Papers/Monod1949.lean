import BioLib.Foundations.Saturation
import BioLib.Foundations.Dynamics
import BioLib.Evidence.Provenance

/-!
# Monod (1949): growth rate as a function of nutrient concentration

**Source.** J. Monod, "The growth of bacterial cultures", *Annual Review of
Microbiology* 3:371–394 (1949). DOI `10.1146/annurev.mi.03.100149.002103`.

**Equations formalized.**

* Definition of the exponential growth rate (section "Growth constants", p. 374–375):
  `R = (log₂ x₂ - log₂ x₁) / (t₂ - t₁)`, in divisions per unit time.
* Equation [2] (section "Rate-concentration relations", p. 383):
  `R = R_K * C / (C₁ + C)`, where `C` is the concentration of the limiting
  nutrient, `R_K` "the rate limit for increasing concentrations of C" and `C₁`
  "the concentration of nutrient at which the rate is half the maximum".

**What Monod claims.** He presents equation [2] as an empirical law: "Several
mathematically different formulations could be made to fit the data. But it is
both convenient and logical to adopt a hyperbolic equation".  Nothing here
asserts that the law holds for any organism.

**What is proved.** The two verbal descriptions of the constants are theorems
about the formula: the rate at `C = C₁` is `R_K / 2`, and the rate tends to `R_K`
as `C → ∞` without ever reaching it.  A culture whose density is
`x₀ * 2 ^ (R * t)` has growth rate `R` in Monod's sense.

**Differences from the source.**

* Positivity of `R_K` and `C₁` is not stated by Monod; it is implicit in their
  meaning and added here as parameter constraints.
* Monod's law concerns the exponential phase with a single limiting nutrient
  whose concentration is treated as fixed.  Nutrient depletion is not modelled.
* `density` is the idealized exponential-phase growth curve implied by the
  definition of `R`; Monod gives no closed form for it.
-/

open Filter Topology

namespace BioLib.Papers.Monod1949

open BioLib.Evidence

/-- Constants of Monod's equation [2]. -/
structure Params where
  /-- `R_K`: rate limit for increasing nutrient concentration (divisions per unit time). -/
  RK : ℝ
  /-- `C₁`: nutrient concentration at which the rate is half the maximum. -/
  C₁ : ℝ
  RK_pos : 0 < RK
  C₁_pos : 0 < C₁

/-- Monod's equation [2]: exponential growth rate at nutrient concentration `C`. -/
noncomputable def growthRate (p : Params) (C : ℝ) : ℝ := saturation p.RK p.C₁ C

variable (p : Params) {C : ℝ}

/-- Equation [2] written out. -/
theorem growthRate_eq (C : ℝ) : growthRate p C = p.RK * C / (p.C₁ + C) := rfl

/-- "`C₁` is the concentration of nutrient at which the rate is half the maximum." -/
theorem growthRate_half : growthRate p p.C₁ = p.RK / 2 :=
  saturation_half p.RK p.C₁_pos.ne'

/-- "`R_K` is the rate limit for increasing concentrations of `C`." -/
theorem tendsto_growthRate : Tendsto (growthRate p) atTop (𝓝 p.RK) :=
  tendsto_saturation_atTop p.RK p.C₁_pos

/-- The limit is never attained at a finite concentration. -/
theorem growthRate_lt_RK (hC : 0 ≤ C) : growthRate p C < p.RK :=
  saturation_lt_max p.RK_pos p.C₁_pos hC

theorem growthRate_nonneg (hC : 0 ≤ C) : 0 ≤ growthRate p C :=
  saturation_nonneg p.RK_pos.le p.C₁_pos hC

theorem growthRate_pos (hC : 0 < C) : 0 < growthRate p C :=
  div_pos (mul_pos p.RK_pos hC) (by linarith [p.C₁_pos])

/-- The growth rate increases strictly with nutrient concentration. -/
theorem growthRate_strictMonoOn : StrictMonoOn (growthRate p) (Set.Ici 0) :=
  saturation_strictMonoOn p.RK_pos p.C₁_pos

/-- Exponential-phase density with initial density `x₀` and `R` divisions per unit time. -/
noncomputable def density (x₀ R t : ℝ) : ℝ := x₀ * (2 : ℝ) ^ (R * t)

/-- `density` has growth rate `R` in the sense of Monod's definition
`R = (log₂ x₂ - log₂ x₁) / (t₂ - t₁)`. -/
theorem density_growthRate {x₀ : ℝ} (hx : 0 < x₀) (R : ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) :
    (Real.logb 2 (density x₀ R t₂) - Real.logb 2 (density x₀ R t₁)) / (t₂ - t₁) = R := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hlog : ∀ t, Real.logb 2 (density x₀ R t) = Real.logb 2 x₀ + R * t := by
    intro t
    unfold density
    rw [Real.logb_mul hx.ne' (Real.rpow_pos_of_pos h2 _).ne',
      Real.logb_rpow h2 (by norm_num)]
  have hne : t₂ - t₁ ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  rw [hlog, hlog]
  field_simp
  ring

/-- In natural units, `R` divisions per unit time is the rate coefficient `R * ln 2`. -/
theorem density_eq_expTrajectory (x₀ R t : ℝ) :
    density x₀ R t = expTrajectory x₀ (R * Real.log 2) t := by
  unfold density expTrajectory
  rw [Real.rpow_def_of_pos (by norm_num)]
  ring_nf

/-- Provenance record. -/
def record : ModelRecord where
  id := "BioLib.Papers.Monod1949"
  version := "0.1.0"
  source := some
    { citation := "Monod J. The growth of bacterial cultures. Annual Review of Microbiology 3:371-394 (1949)."
      doi := some "10.1146/annurev.mi.03.100149.002103"
      locator := "Definition of R, section 'Growth constants', pp. 374-375; equation [2], section 'Rate-concentration relations', p. 383." }
  parameters :=
    [ { name := "RK", unit := "divisions per hour (base-2 logarithm of density per hour)",
        description := "rate limit for increasing concentrations of the nutrient" },
      { name := "C₁", unit := "concentration",
        description := "nutrient concentration at which the rate is half the maximum" } ]
  assumptions :=
    [ { name := "positive constants", kind := .mathematical,
        statement := "R_K > 0 and C₁ > 0 (implicit in the source)",
        formalizedAs := "Params.RK_pos, Params.C₁_pos" },
      { name := "single limiting nutrient", kind := .modelling,
        statement := "one essential nutrient limits growth; all others are in excess" },
      { name := "exponential phase", kind := .modelling,
        statement := "the rate is the constant rate of the exponential phase at a given nutrient concentration" },
      { name := "hyperbolic rate law", kind := .empirical,
        statement := "the rate depends on nutrient concentration through equation [2]; the source presents this as one convenient fit among several possible" } ]
  context := "Batch cultures of bacteria on defined media; Figs. 4 and 5 of the source show E. coli on glucose and M. tuberculosis on glucose."
  applicability := "Exponential phase, single limiting nutrient, nonnegative concentrations."
  evidence :=
    [ { parameter := "RK", value := "1.35 divisions per hour",
        source :=
          { citation := "Monod (1949), as above"
            doi := some "10.1146/annurev.mi.03.100149.002103"
            locator := "Legend of Fig. 4" }
        context := "Value used for the solid line drawn to equation [2] in Fig. 4." } ]
  deviations :=
    [ "Positivity of R_K and C₁ added as explicit constraints.",
      "The closed-form density x₀ * 2^(R t) is not in the source; it is the curve implied by the definition of R.",
      "Text was read from a scanned copy; the legend of Fig. 4 is partly illegible there, so only R_K is recorded as evidence." ]

end BioLib.Papers.Monod1949
