import BioLib.Papers.Monod1949
import BioLib.Papers.Regoes2004

/-!
# Composition: nutrient-dependent pharmacodynamic MIC

`Monod1949` gives the antibiotic-free growth rate as a function of nutrient
concentration.  `Regoes2004` takes the antibiotic-free growth rate `ψmax` as a
parameter.  The shared interface is that growth rate.

**This composition is not a result of either paper.**  It rests on assumptions
that neither source makes:

1. *Rate independence.*  The death rate `μ(a)` does not depend on nutrient
   concentration or on growth rate.  This is an added modelling hypothesis.
   It is known to be questionable: many antibiotics kill slowly growing cells
   more slowly.  The theorems below are consequences of the hypothesis, not
   evidence for it.
2. *Unit conversion.*  Monod's rate is in divisions per hour (base-2
   logarithm); Regoes' rates are base-10 logarithms per hour.  The composition
   sets `ψmax = log₁₀ 2 * R(C)`.  Both rates have dimension 1/time, so a
   dimension check alone would not catch a missing conversion factor.
3. *Same organism and conditions* for both sets of parameters, and nutrient
   concentration constant over the time considered.
4. `log₁₀ 2 * R_K ≤ Emax`: killing at saturation outpaces the fastest possible
   growth.  This guarantees `zMIC` exists at every nutrient level.

**What is proved under these assumptions.** The pharmacodynamic MIC is a
strictly increasing function of nutrient concentration, and for a nonnegative
antibiotic concentration the net growth rate is negative exactly when that
concentration exceeds the MIC at the current nutrient level.
-/

namespace BioLib.Papers.MonodRegoes

open Monod1949 Regoes2004

/-- Conversion factor from divisions per hour to base-10 logarithm units per hour. -/
noncomputable def log10Two : ℝ := Real.logb 10 2

theorem log10Two_pos : 0 < log10Two :=
  Real.logb_pos (by norm_num) (by norm_num)

variable (m : Monod1949.Params) (k : Regoes2004.KillParams)

/-- Antibiotic-free growth rate at nutrient concentration `C`, in Regoes' units. -/
noncomputable def ψmaxAt (C : ℝ) : ℝ := log10Two * growthRate m C

theorem ψmaxAt_pos {C : ℝ} (hC : 0 < C) : 0 < ψmaxAt m C :=
  mul_pos log10Two_pos (growthRate_pos m hC)

theorem ψmaxAt_lt_Emax (h : log10Two * m.RK ≤ k.Emax) {C : ℝ} (hC : 0 < C) :
    ψmaxAt m C < k.Emax :=
  (mul_lt_mul_of_pos_left (growthRate_lt_RK m hC.le) log10Two_pos).trans_le h

theorem ψmaxAt_strictMonoOn : StrictMonoOn (ψmaxAt m) (Set.Ici 0) :=
  fun _ ha _ hb hab =>
    mul_lt_mul_of_pos_left (growthRate_strictMonoOn m ha hb hab) log10Two_pos

/-- The Regoes model whose antibiotic-free growth rate is supplied by the Monod model. -/
noncomputable def paramsAt (h : log10Two * m.RK ≤ k.Emax) (C : ℝ) (hC : 0 < C) :
    Regoes2004.Params :=
  { k with
    ψmax := ψmaxAt m C
    ψmax_pos := ψmaxAt_pos m hC
    ψmax_lt_Emax := ψmaxAt_lt_Emax m k h hC }

/-- Net growth rate at nutrient concentration `C` and antibiotic concentration `a`. -/
noncomputable def netGrowth (C a : ℝ) : ℝ := ψmaxAt m C - deathRate k a

/-- Pharmacodynamic MIC at nutrient concentration `C`. -/
noncomputable def zMICAt (C : ℝ) : ℝ :=
  k.EC50 * (ψmaxAt m C / (k.Emax - ψmaxAt m C)) ^ (1 / k.κ)

theorem netGrowth_eq_psi (h : log10Two * m.RK ≤ k.Emax) {C : ℝ} (hC : 0 < C) (a : ℝ) :
    netGrowth m k C a = psi (paramsAt m k h C hC) a := rfl

theorem zMICAt_eq_zMIC (h : log10Two * m.RK ≤ k.Emax) {C : ℝ} (hC : 0 < C) :
    zMICAt m k C = zMIC (paramsAt m k h C hC) := rfl

/-- At nutrient concentration `C`, net growth is negative exactly when the
antibiotic concentration exceeds the MIC for that nutrient level. -/
theorem netGrowth_neg_iff (h : log10Two * m.RK ≤ k.Emax) {C a : ℝ} (hC : 0 < C)
    (ha : 0 ≤ a) : netGrowth m k C a < 0 ↔ zMICAt m k C < a :=
  psi_neg_iff (paramsAt m k h C hC) ha

/-- The pharmacodynamic MIC increases strictly with nutrient concentration. -/
theorem zMICAt_strictMonoOn (h : log10Two * m.RK ≤ k.Emax) :
    StrictMonoOn (zMICAt m k) (Set.Ioi 0) := by
  intro C hC D hD hCD
  have hC' : 0 < C := hC
  have hD' : 0 < D := hD
  have h1 := ψmaxAt_pos m hC'
  have h2 := ψmaxAt_lt_Emax m k h hC'
  have h3 := ψmaxAt_lt_Emax m k h hD'
  have h4 : ψmaxAt m C < ψmaxAt m D := ψmaxAt_strictMonoOn m hC'.le hD'.le hCD
  have hfrac : ψmaxAt m C / (k.Emax - ψmaxAt m C) < ψmaxAt m D / (k.Emax - ψmaxAt m D) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hpow := Real.rpow_lt_rpow (div_nonneg h1.le (by linarith)) hfrac
    (one_div_pos.2 k.κ_pos)
  exact mul_lt_mul_of_pos_left hpow k.EC50_pos

/-- A dose that suppresses growth at a high nutrient level also suppresses it
at any lower positive nutrient level. -/
theorem netGrowth_neg_of_le (h : log10Two * m.RK ≤ k.Emax) {C D a : ℝ} (hC : 0 < C)
    (hCD : C ≤ D) (ha : 0 ≤ a) (hD : netGrowth m k D a < 0) : netGrowth m k C a < 0 := by
  have hD' : 0 < D := hC.trans_le hCD
  rw [netGrowth_neg_iff m k h hC ha]
  rw [netGrowth_neg_iff m k h hD' ha] at hD
  exact ((zMICAt_strictMonoOn m k h).monotoneOn hC hD' hCD).trans_lt hD

end BioLib.Papers.MonodRegoes
