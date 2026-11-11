import BioLib.Foundations.Hill
import BioLib.Foundations.Dynamics
import BioLib.Evidence.Provenance

/-!
# Regoes et al. (2004): pharmacodynamic function for antibiotics

**Source.** R. R. Regoes, C. Wiuff, R. M. Zappala, K. N. Garner, F. Baquero,
B. R. Levin, "Pharmacodynamic functions: a multiparameter approach to the
design of antibiotic treatment regimens", *Antimicrobial Agents and
Chemotherapy* 48(10):3670–3676 (2004). DOI `10.1128/AAC.48.10.3670-3676.2004`.

**Equations formalized** (Materials and Methods).

* Equation 1: the net growth rate at antibiotic concentration `a` is
  `ψ(a) = ψmax - μ(a)`, with `ψmax` "the growth rate of the bacterial population
  in the absence of antibiotics" and `μ(a)` the antibiotic-induced death rate.
* Equation 2: `μ` is a Hill function with `Emax` "the maximum
  antibiotic-mediated death rate", `EC50` "the antibiotic concentration at which
  the death rate is at half of its maximum" and Hill coefficient `κ`.
* Equation 3: with `ψmin = ψmax - Emax` and `zMIC` defined "by requiring
  `ψ(zMIC) = 0`", the function is rewritten in terms of `ψmax`, `ψmin`, `zMIC`, `κ`.
* Equation 4: bacterial density follows `dX/dt = ln(10) * ψ(a(t)) * X`; the
  factor `ln(10)` appears because rates are "the change per hour in the
  logarithm of bacterial density to the base 10".

**What is proved.** `zMIC` has a closed form in the Equation 1–2 parameters, and
`ψ(zMIC) = 0`.  Net growth is negative exactly above `zMIC`.  The rewritten
form (Equation 3) is *derived* from Equations 1 and 2 as a theorem, not assumed.
For a constant concentration above `zMIC` the density declines to zero.

**Source ambiguity.** In the copy consulted (PubMed Central, PMC521919) the
display equations are images that could not be read.  Equations 1 and 4 and all
parameter definitions were taken from the running text, quoted above.  For
Equation 2 the text says only "a Hill function" with the three named
parameters; the standard form
`μ(a) = Emax * (a / EC50) ^ κ / (1 + (a / EC50) ^ κ)` is used here, which is the
unique Hill function with that maximum, half-maximum point and coefficient.
Equation 3 as stated in `psi_eq_rewritten` is what the text's definitions of
`ψmin` and `zMIC` imply; its typography in the paper was not checked.

**Differences from the source.**

* `ψmax > 0`, `EC50 > 0`, `κ > 0` and `Emax > ψmax` are added as constraints.
  The paper does not state them.  `Emax > ψmax` (equivalently `ψmin < 0`) is
  needed for `zMIC` to exist; every fitted `ψmin` in the paper's Table 1 is negative.
* The paper's simulations use a time-varying concentration `a(t)` (its
  Equation 5).  Only constant concentration is treated here.
* `zMIC` is the model's zero of `ψ`.  The paper distinguishes it from the
  experimentally measured MIC.
-/

open Filter Topology

namespace BioLib.Papers.Regoes2004

open BioLib.Evidence

/-- Parameters of the death-rate Hill function (Equation 2). -/
structure KillParams where
  /-- Maximum antibiotic-mediated death rate. -/
  Emax : ℝ
  /-- Concentration at which the death rate is half of its maximum. -/
  EC50 : ℝ
  /-- Hill coefficient. -/
  κ : ℝ
  EC50_pos : 0 < EC50
  κ_pos : 0 < κ

/-- Parameters of the pharmacodynamic function (Equations 1 and 2). -/
structure Params extends KillParams where
  /-- Growth rate in the absence of antibiotic. -/
  ψmax : ℝ
  ψmax_pos : 0 < ψmax
  /-- The antibiotic can kill faster than the population grows. -/
  ψmax_lt_Emax : ψmax < Emax

/-- Equation 2: death rate at antibiotic concentration `a`. -/
noncomputable def deathRate (k : KillParams) (a : ℝ) : ℝ := hill k.Emax k.EC50 k.κ a

/-- Equation 1: net growth rate at antibiotic concentration `a`. -/
noncomputable def psi (p : Params) (a : ℝ) : ℝ := p.ψmax - deathRate p.toKillParams a

/-- Minimum net growth rate, approached at high concentration. -/
def ψmin (p : Params) : ℝ := p.ψmax - p.Emax

/-- The pharmacodynamic MIC: the concentration at which net growth is zero. -/
noncomputable def zMIC (p : Params) : ℝ :=
  p.EC50 * (p.ψmax / (p.Emax - p.ψmax)) ^ (1 / p.κ)

variable (p : Params) {a : ℝ}

theorem Emax_pos : 0 < p.Emax := p.ψmax_pos.trans p.ψmax_lt_Emax

theorem ψmin_neg : ψmin p < 0 := by
  unfold ψmin
  linarith [p.ψmax_lt_Emax]

theorem zMIC_pos : 0 < zMIC p :=
  mul_pos p.EC50_pos
    (Real.rpow_pos_of_pos (div_pos p.ψmax_pos (by linarith [p.ψmax_lt_Emax])) _)

/-- Without antibiotic the net growth rate is `ψmax`. -/
theorem psi_zero : psi p 0 = p.ψmax := by
  simp [psi, deathRate, hill_zero _ _ p.κ_pos.ne']

/-- The net growth rate stays above `ψmin`. -/
theorem ψmin_lt_psi (ha : 0 ≤ a) : ψmin p < psi p a := by
  have h := hill_lt_max (n := p.κ) (Emax_pos p) p.EC50_pos ha
  unfold ψmin psi deathRate
  linarith

/-- The net growth rate is at most `ψmax`. -/
theorem psi_le_ψmax (ha : 0 ≤ a) : psi p a ≤ p.ψmax := by
  have h := hill_nonneg (n := p.κ) (Emax_pos p).le p.EC50_pos ha
  unfold psi deathRate
  linarith

/-- More antibiotic means lower net growth. -/
theorem psi_strictAntiOn : StrictAntiOn (psi p) (Set.Ici 0) := by
  intro a ha b hb hab
  have h := hill_strictMonoOn (Emax_pos p) p.EC50_pos p.κ_pos ha hb hab
  unfold psi deathRate
  linarith

/-- Net growth is negative exactly when the concentration exceeds `zMIC`. -/
theorem psi_neg_iff (ha : 0 ≤ a) : psi p a < 0 ↔ zMIC p < a := by
  unfold psi deathRate zMIC
  rw [sub_neg]
  exact lt_hill_iff p.EC50_pos p.κ_pos ha p.ψmax_pos.le p.ψmax_lt_Emax

/-- Scaled concentration at `zMIC`. -/
theorem zMIC_div_EC50_rpow :
    (zMIC p / p.EC50) ^ p.κ = p.ψmax / (p.Emax - p.ψmax) := by
  have hc : 0 ≤ p.ψmax / (p.Emax - p.ψmax) :=
    div_nonneg p.ψmax_pos.le (by linarith [p.ψmax_lt_Emax])
  unfold zMIC
  rw [mul_div_cancel_left₀ _ p.EC50_pos.ne', ← Real.rpow_mul hc,
    one_div_mul_cancel p.κ_pos.ne', Real.rpow_one]

/-- The defining property of `zMIC`: `ψ(zMIC) = 0`. -/
theorem psi_zMIC : psi p (zMIC p) = 0 := by
  have hE : p.Emax - p.ψmax ≠ 0 := by linarith [p.ψmax_lt_Emax]
  have hEm : p.Emax ≠ 0 := (Emax_pos p).ne'
  unfold psi deathRate hill saturation
  rw [zMIC_div_EC50_rpow]
  field_simp
  rw [sub_add_cancel, div_self hEm, sub_self, mul_zero]

/-- Equation 3: the pharmacodynamic function in terms of `ψmax`, `ψmin`, `zMIC`
and `κ`, derived from Equations 1 and 2. -/
theorem psi_eq_rewritten (ha : 0 ≤ a) :
    psi p a = p.ψmax -
      (p.ψmax - ψmin p) * (a / zMIC p) ^ p.κ / ((a / zMIC p) ^ p.κ - ψmin p / p.ψmax) := by
  have hE : 0 < p.Emax - p.ψmax := by linarith [p.ψmax_lt_Emax]
  have hψ := p.ψmax_pos
  have hc : 0 < p.ψmax / (p.Emax - p.ψmax) := div_pos hψ hE
  have hu : 0 ≤ (a / p.EC50) ^ p.κ := Real.rpow_nonneg (div_nonneg ha p.EC50_pos.le) _
  have h1 : (a / zMIC p) ^ p.κ = (a / p.EC50) ^ p.κ / (p.ψmax / (p.Emax - p.ψmax)) := by
    have hz : a / zMIC p = a / p.EC50 / (p.ψmax / (p.Emax - p.ψmax)) ^ (1 / p.κ) := by
      unfold zMIC
      rw [div_div]
    rw [hz, Real.div_rpow (div_nonneg ha p.EC50_pos.le) (Real.rpow_nonneg hc.le _),
      ← Real.rpow_mul hc.le, one_div_mul_cancel p.κ_pos.ne', Real.rpow_one]
  rw [h1]
  unfold psi deathRate hill saturation ψmin
  generalize (a / p.EC50) ^ p.κ = u at hu
  have h1u : 1 + u ≠ 0 := by linarith
  have hden : u / (p.ψmax / (p.Emax - p.ψmax)) - (p.ψmax - p.Emax) / p.ψmax =
      (p.Emax - p.ψmax) * (1 + u) / p.ψmax := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

/-- Equation 4 at constant concentration: rate of change of density `X`. -/
noncomputable def densityRate (p : Params) (a X : ℝ) : ℝ := Real.log 10 * psi p a * X

/-- At constant concentration the density `X₀ * exp (ln 10 * ψ(a) * t)` solves Equation 4. -/
theorem hasDerivAt_density (X₀ a t : ℝ) :
    HasDerivAt (expTrajectory X₀ (Real.log 10 * psi p a))
      (densityRate p a (expTrajectory X₀ (Real.log 10 * psi p a) t)) t :=
  hasDerivAt_expTrajectory X₀ _ t

theorem log_ten_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

/-- Above `zMIC`, a positive bacterial density strictly declines. -/
theorem density_strictAnti (h : zMIC p < a) {X₀ : ℝ} (hX : 0 < X₀) :
    StrictAnti (expTrajectory X₀ (Real.log 10 * psi p a)) :=
  expTrajectory_strictAnti hX
    (mul_neg_of_pos_of_neg log_ten_pos ((psi_neg_iff p ((zMIC_pos p).le.trans h.le)).2 h))

/-- Above `zMIC`, the bacterial density tends to zero. -/
theorem density_tendsto_zero (h : zMIC p < a) (X₀ : ℝ) :
    Tendsto (expTrajectory X₀ (Real.log 10 * psi p a)) atTop (𝓝 0) :=
  tendsto_expTrajectory_atTop_zero X₀
    (mul_neg_of_pos_of_neg log_ten_pos ((psi_neg_iff p ((zMIC_pos p).le.trans h.le)).2 h))

/-- Provenance record. -/
def record : ModelRecord where
  id := "BioLib.Papers.Regoes2004"
  version := "0.1.0"
  source := some
    { citation := "Regoes RR, Wiuff C, Zappala RM, Garner KN, Baquero F, Levin BR. Pharmacodynamic functions: a multiparameter approach to the design of antibiotic treatment regimens. Antimicrobial Agents and Chemotherapy 48(10):3670-3676 (2004)."
      doi := some "10.1128/AAC.48.10.3670-3676.2004"
      locator := "Materials and Methods, equations 1-4." }
  parameters :=
    [ { name := "ψmax", unit := "log10 units of density per hour",
        description := "growth rate in the absence of antibiotic" },
      { name := "Emax", unit := "log10 units of density per hour",
        description := "maximum antibiotic-mediated death rate" },
      { name := "EC50", unit := "concentration",
        description := "concentration at which the death rate is half of its maximum" },
      { name := "κ", unit := "dimensionless", description := "Hill coefficient" } ]
  assumptions :=
    [ { name := "positive parameters", kind := .mathematical,
        statement := "ψmax > 0, EC50 > 0, κ > 0 (not stated in the source)",
        formalizedAs := "Params.ψmax_pos, KillParams.EC50_pos, KillParams.κ_pos" },
      { name := "killing can outpace growth", kind := .mathematical,
        statement := "Emax > ψmax, equivalently ψmin < 0; required for zMIC to exist",
        formalizedAs := "Params.ψmax_lt_Emax" },
      { name := "additive death rate", kind := .modelling,
        statement := "net growth is the antibiotic-free growth rate minus a concentration-dependent death rate" },
      { name := "Hill-shaped death rate", kind := .empirical,
        statement := "the death rate is a Hill function of antibiotic concentration" },
      { name := "constant concentration", kind := .modelling,
        statement := "the antibiotic concentration is constant in time (used for the density results only)",
        formalizedAs := "densityRate takes a fixed `a`" } ]
  context := "In vitro time-kill experiments with Escherichia coli exposed to fixed concentrations of five antibiotics; rates are log10 changes in density per hour."
  applicability := "Nonnegative concentrations; the density results need constant concentration."
  deviations :=
    [ "Display equations in the consulted copy are images that could not be read; equations were reconstructed from the running text. See the module docstring.",
      "Equation 2 is taken to be the standard Hill function with the three named parameters.",
      "Equation 3 is proved from equations 1 and 2 rather than taken from the page.",
      "Parameter constraints are added; the source does not state them.",
      "The time-varying concentration of the source's equation 5 is not modelled.",
      "No fitted parameter values from the source's Table 1 are recorded, because the table was not read." ]

end BioLib.Papers.Regoes2004
