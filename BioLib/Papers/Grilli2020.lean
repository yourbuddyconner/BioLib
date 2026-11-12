import BioLib.Sim.Core
import BioLib.Evidence.Provenance
import Mathlib

/-!
# Grilli (2020): macroecological laws and the stochastic logistic model

**Source.** J. Grilli, "Macroecological laws describe variation and diversity
in microbial communities", *Nature Communications* 11:4743 (2020).
DOI `10.1038/s41467-020-18529-y`.  Equations were read from the published PDF.

**What the paper reports** (empirical claims, recorded here, not assumed):

1. *Gamma abundance fluctuations* (Eq. 1).  Across communities, the relative
   abundance of species `i` is gamma distributed with mean `x̄ᵢ` and shape
   `βᵢ = x̄ᵢ² / σ²ₓᵢ`.
2. *Taylor's law with exponent 2.*  The variance scales as the square of the
   mean, so `βᵢ = β` for all species.
3. *Lognormal mean abundances* (Eq. 3).  Across species, `x̄ᵢ` is lognormal.

It also reports that absences are due to sampling: with `Nₛ` reads in sample
`s`, the probability of seeing no read of a species is `(1 + x̄ Nₛ / β) ^ (-β)`
(Eqs. 2, 9, and Eq. 13 at `n = 0`).

**The model** (Methods, Eq. 23).  The stochastic logistic model
`dx/dt = (x / τ) (1 - x / K) + √(σ / τ) x ξ(t)` with Gaussian white noise `ξ`.
The paper states its stationary distribution (Eq. 24), a gamma distribution
with shape `2 / σ - 1` and mean `K (1 - σ / 2)`, and that species do not interact.

**What is proved here.**

* Eq. 24 is Eq. 1 with `β = 2 / σ - 1` and `x̄ = K (1 - σ / 2)`.
* The density of Eq. 24 satisfies the zero-flux stationary Fokker–Planck
  equation of Eq. 23 read as an Itô equation:
  `d/dx [ (σ / τ) x² ρ(x) / 2 ] = (x / τ) (1 - x / K) ρ(x)`.
* The two forms of the absence probability agree, it decreases to zero as the
  number of reads grows, and so predicted occupancy tends to one.
* An extension that is **not in the paper**: subtracting a per-capita loss
  `s * B` from the growth rate gives again a stochastic logistic model, with
  `τ, K, σ` replaced by `τ / f, K f, σ / f` where `f = 1 - τ s B`.  The
  simulator uses this for treated samples.

**What is not proved.**

* That Eq. 24 is the stationary distribution of the stochastic process.
  Mathlib has no theory of stochastic differential equations to state this in.
  The zero-flux identity is the standard calculation behind the claim, and it
  is checked numerically by `biolib-sim --selfcheck`.
* Whether Eq. 23 is meant in the Itô or Stratonovich sense is not stated in
  the Methods.  The Itô reading is the one under which Eq. 24 satisfies the
  zero-flux equation, so it is the reading adopted.
* The gamma–Poisson integral behind Eq. 13.
* Any of the three empirical laws.

**Differences from the source.**  Supplementary Notes were not consulted, so
the paper's parameter estimation procedure (Supplementary Notes 2 and 7) is
approximated in `python/fit_slm.py`, not reproduced.  Positivity conditions on
`τ`, `K`, `σ` are added as hypotheses.
-/

open Filter Topology

namespace BioLib.Papers.Grilli2020

open BioLib.Sim BioLib.Evidence

variable {β xbar τ K σ x N s B : ℝ}

/-- Eq. 1: gamma abundance fluctuation distribution with shape `β` and mean `xbar`. -/
noncomputable def afd (β xbar x : ℝ) : ℝ :=
  1 / Real.Gamma β * (β / xbar) ^ β * x ^ (β - 1) * Real.exp (-β * x / xbar)

/-- Eq. 24: stationary density of the stochastic logistic model. -/
noncomputable def stationaryDensity (K σ x : ℝ) : ℝ :=
  1 / Real.Gamma (2 / σ - 1) * (2 / (K * σ)) ^ (2 / σ - 1) *
    Real.exp (-(2 / (K * σ)) * x) * x ^ (2 / σ - 2)

/-- The mean of the stationary distribution, `K (1 - σ / 2)`, as stated below Eq. 23. -/
theorem slmMean_one (K σ : ℝ) : slmMean K σ 1 = K * (1 - σ / 2) := rfl

/-- The shape of the stationary distribution is `2 / σ - 1`. -/
theorem slmShape_one (σ : ℝ) : slmShape σ 1 = 2 / σ - 1 := by
  simp [slmShape]

/-- Eq. 24 is the gamma law of Eq. 1 with shape `2 / σ - 1` and mean `K (1 - σ / 2)`. -/
theorem stationaryDensity_eq_afd (hK : K ≠ 0) (hσ : σ ≠ 0) (hσ2 : σ ≠ 2) (x : ℝ) :
    stationaryDensity K σ x = afd (slmShape σ 1) (slmMean K σ 1) x := by
  have h2 : (2 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ2)
  have h : (2 / σ - 1) / (K * (1 - σ / 2)) = 2 / (K * σ) := by
    field_simp
  have hexp : -(2 / σ - 1) * x / (K * (1 - σ / 2)) = -(2 / (K * σ)) * x := by
    rw [← h]; ring
  rw [slmShape_one, slmMean_one]
  unfold afd stationaryDensity
  rw [h, hexp, show (2 / σ - 1 - 1 : ℝ) = 2 / σ - 2 by ring]
  ring

/-- Derivative of `a y² w(y) / 2` for a gamma-type weight `w(y) = C exp(-b y) y ^ p`. -/
theorem hasDerivAt_gamma_flux (a C b p : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => a * y ^ 2 * (C * Real.exp (-b * y) * y ^ p) / 2)
      (a * x * (C * Real.exp (-b * x) * x ^ p) * (p + 2 - b * x) / 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-b * y)) (Real.exp (-b * x) * -b) x := by
    have h := (hasDerivAt_id x).const_mul (-b)
    simpa using h.exp
  have h3 : HasDerivAt (fun y : ℝ => y ^ p) (p * x ^ (p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h := ((h1.const_mul a).fun_mul ((h2.const_mul C).fun_mul h3)).div_const 2
  have hpow : x ^ (p - 1) = x ^ p / x := Real.rpow_sub_one hx.ne' p
  refine h.congr_deriv ?_
  rw [hpow]
  generalize Real.exp (-b * x) = E
  generalize x ^ p = P
  field_simp
  ring

/-- The stationary density satisfies the zero-flux stationary Fokker–Planck
equation of the stochastic logistic model (Itô form):
`d/dx [ (σ / τ) x² ρ(x) / 2 ] = drift(x) ρ(x)`. -/
theorem stationaryDensity_zero_flux (hτ : τ ≠ 0) (hK : K ≠ 0) (hσ : σ ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun y => σ / τ * y ^ 2 * stationaryDensity K σ y / 2)
      (slmDrift τ K x * stationaryDensity K σ x) x := by
  have h := hasDerivAt_gamma_flux (σ / τ)
    (1 / Real.Gamma (2 / σ - 1) * (2 / (K * σ)) ^ (2 / σ - 1)) (2 / (K * σ)) (2 / σ - 2) hx
  unfold stationaryDensity slmDrift
  refine h.congr_deriv ?_
  generalize Real.exp (-(2 / (K * σ)) * x) = E
  generalize x ^ (2 / σ - 2) = P
  generalize 1 / Real.Gamma (2 / σ - 1) * (2 / (K * σ)) ^ (2 / σ - 1) = G
  field_simp
  ring

/-- Probability of observing no read of a species with mean abundance `xbar`
in a sample of `N` reads (the summand of Eq. 9). -/
noncomputable def absenceProb (β xbar N : ℝ) : ℝ := (1 + xbar * N / β) ^ (-β)

/-- Predicted occupancy at sequencing depth `N` (Eqs. 2 and 9 for a single depth). -/
noncomputable def occupancy (β xbar N : ℝ) : ℝ := 1 - absenceProb β xbar N

/-- The absence probability of Eq. 9 is Eq. 13 evaluated at zero reads. -/
theorem absenceProb_eq (hβ : 0 < β) (hx : 0 ≤ xbar) (hN : 0 ≤ N) :
    absenceProb β xbar N = (β / (β + xbar * N)) ^ β := by
  have h1 : 0 < β + xbar * N := by positivity
  have h2 : 1 + xbar * N / β = (β / (β + xbar * N))⁻¹ := by
    field_simp
  unfold absenceProb
  rw [h2, Real.inv_rpow (div_nonneg hβ.le h1.le), Real.rpow_neg (div_nonneg hβ.le h1.le), inv_inv]

theorem absenceProb_nonneg (hβ : 0 < β) (hx : 0 ≤ xbar) (hN : 0 ≤ N) :
    0 ≤ absenceProb β xbar N :=
  Real.rpow_nonneg (by positivity) _

/-- With enough reads every species is observed: the absence probability tends to zero. -/
theorem tendsto_absenceProb (hβ : 0 < β) (hx : 0 < xbar) :
    Tendsto (absenceProb β xbar) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℝ => 1 + xbar * N / β) atTop atTop := by
    have : Tendsto (fun N : ℝ => xbar / β * N) atTop atTop :=
      tendsto_id.const_mul_atTop (div_pos hx hβ)
    refine (tendsto_atTop_add_const_left _ 1 this).congr fun N => ?_
    ring
  exact (tendsto_rpow_neg_atTop hβ).comp h1

/-- "As the total number of reads increases, occupancy is predicted to tend to 1." -/
theorem tendsto_occupancy (hβ : 0 < β) (hx : 0 < xbar) :
    Tendsto (occupancy β xbar) atTop (𝓝 1) := by
  have h : Tendsto (fun N => 1 - absenceProb β xbar N) atTop (𝓝 (1 - 0)) :=
    (tendsto_absenceProb hβ hx).const_sub 1
  rw [sub_zero] at h
  exact h

/-! ### Extension, not in the paper: a per-capita loss term -/

/-- Subtracting a per-capita loss `s * B` from the growth rate of the logistic
drift gives a logistic drift with `τ` and `K` replaced by `τ / f` and `K * f`,
where `f = 1 - τ s B` is the fraction of the growth rate that remains. -/
theorem slmDrift_sub_loss (hτ : τ ≠ 0) (hK : K ≠ 0) (hf : growthFraction τ s B ≠ 0) (x : ℝ) :
    slmDrift τ K x - s * B * x =
      slmDrift (τ / growthFraction τ s B) (K * growthFraction τ s B) x := by
  unfold slmDrift
  unfold growthFraction at hf ⊢
  field_simp
  ring

/-- The noise amplitude `σ / τ` is unchanged when `σ` and `τ` are both divided by `f`. -/
theorem noise_ratio_invariant (f : ℝ) (hf : f ≠ 0) : σ / f / (τ / f) = σ / τ := by
  field_simp

/-- The shape used for treated samples is the stationary shape of the rescaled model. -/
theorem slmShape_rescaled (σ f : ℝ) : slmShape σ f = slmShape (σ / f) 1 := by
  unfold slmShape
  field_simp

/-- The mean used for treated samples is the stationary mean of the rescaled model. -/
theorem slmMean_rescaled (K σ : ℝ) {f : ℝ} (hf : f ≠ 0) :
    slmMean K σ f = slmMean (K * f) (σ / f) 1 := by
  unfold slmMean
  field_simp

/-- A treated species persists (positive stationary shape) exactly when the
remaining fraction of its growth rate exceeds `σ / 2`. -/
theorem slmShape_pos_iff (hσ : 0 < σ) {f : ℝ} : 0 < slmShape σ f ↔ σ / 2 < f := by
  unfold slmShape
  rw [sub_pos, lt_div_iff₀ hσ]
  constructor <;> intro h <;> linarith

/-- Provenance record. -/
def record : ModelRecord where
  id := "BioLib.Papers.Grilli2020"
  version := "0.1.0"
  source := some
    { citation := "Grilli J. Macroecological laws describe variation and diversity in microbial communities. Nature Communications 11:4743 (2020)."
      doi := some "10.1038/s41467-020-18529-y"
      locator := "Results, equations 1-3; Methods, equations 7, 9, 13, 23, 24." }
  parameters :=
    [ { name := "β", unit := "dimensionless",
        description := "shape of the gamma abundance fluctuation distribution; β = 2/σ - 1" },
      { name := "σ", unit := "dimensionless",
        description := "coefficient of variation of the growth-rate fluctuations" },
      { name := "τ", unit := "time", description := "inverse intrinsic growth rate" },
      { name := "K", unit := "relative abundance", description := "carrying capacity" },
      { name := "μ, σ of the mean abundance distribution", unit := "natural log of relative abundance",
        description := "parameters of the lognormal distribution of mean abundance across species" } ]
  assumptions :=
    [ { name := "no interactions", kind := .modelling,
        statement := "species populations change independently" },
      { name := "gamma abundance fluctuations", kind := .empirical,
        statement := "the abundance of each species across communities is gamma distributed" },
      { name := "Taylor's law with exponent 2", kind := .empirical,
        statement := "the variance of abundance scales as the square of its mean, so β is shared by all species" },
      { name := "lognormal mean abundances", kind := .empirical,
        statement := "mean abundance is lognormally distributed across species" },
      { name := "absences are sampling", kind := .empirical,
        statement := "a species absent from a sample is present but undetected at that sequencing depth" },
      { name := "Itô interpretation", kind := .mathematical,
        statement := "equation 23 is read as an Itô stochastic differential equation",
        formalizedAs := "stationaryDensity_zero_flux" } ]
  context := "Cross-sectional and longitudinal 16S data from several biomes, 97% OTUs, obtained from EBI Metagenomics; data sets with at least 50 samples of more than 10^4 reads."
  applicability := "Statistical description of abundance variation across communities of one biome at OTU resolution."
  evidence :=
    [ { parameter := "τ", value := "19 hours",
        source :=
          { citation := "Grilli (2020), as above"
            doi := some "10.1038/s41467-020-18529-y"
            locator := "Methods, below equation 25" }
        context := "Relaxation time-scale estimated from longitudinal data, assumed equal for all species." } ]
  deviations :=
    [ "Supplementary Notes were not consulted.",
      "Stationarity of equation 24 is not proved; only the zero-flux identity is.",
      "The per-capita loss term (treatment) is an extension that is not in the paper.",
      "No fitted values of β or of the lognormal parameters are recorded: the main text does not give them." ]

end BioLib.Papers.Grilli2020
