# Proof status

Last verified: 2026-11-11, Lean `v4.34.0`, Mathlib `v4.34.0`.

- `lake build` completes with no errors and no warnings from BioLib files.
- No `sorry`, no `axiom` declarations.
- `#print axioms` on every theorem marked ★ below reports only `propext`,
  `Classical.choice` and `Quot.sound`, the three standard axioms that Mathlib
  itself uses. The other theorems are short consequences of these or of Mathlib lemmas.

"Proved" means the Lean kernel accepted a proof of the statement from the
listed assumptions. It does not mean the assumptions hold for a real system.

## Reaction networks

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| ★ `Reaction.netChange_eq_zero_of_reactants_eq_products` | identical sides give zero net change | reactants = products | Proved |
| `Reaction.netChange_reverse` | reversing negates net change | none | Proved |
| ★ `Network.isSteadyState_zero` | zero flux satisfies `S v = 0` | finite reaction set | Proved |
| `Network.IsSteadyState.add`, `.smul` | steady-state fluxes form a linear subspace | finite reaction set | Proved |
| `Network.rateOfChange_union` | rates add in a union of networks | shared species type | Proved |
| `Network.isConservationLaw_iff` | `cᵀ S = 0` iff each reaction preserves `c · x` | finite species set | Proved |
| ★ `IsConservationLaw.dotProduct_rateOfChange` | `c · (S v) = 0` for every flux `v` | `cᵀ S = 0` | Proved |
| ★ `IsConservationLaw.dotProduct_trajectory_eq` | `c · x(t)` is constant along `ẋ = S v(t)` | `cᵀ S = 0`; `x` differentiable at all `t` with that derivative | Proved, conditional on a solution existing |
| ★ `IsConservationLaw.union`, `isConservationLaw_union_iff` | `c` conserved by a union iff conserved by both parts | shared species type | Proved |
| ★ `IsConservationLaw.dotProduct_massActionField` | conservation under mass action for any rate constants | `cᵀ S = 0` | Proved |
| `Reaction.massActionRate_nonneg` | mass-action rate is nonnegative | `k ≥ 0`, `x ≥ 0` | Proved |

### Enzyme network `E + S ⇌ ES → E + P`

| Theorem | Statement | Status |
| --- | --- | --- |
| ★ `totalEnzyme_conserved` | `E + ES` is a conservation law | Proved |
| ★ `totalSubstrate_conserved` | `S + ES + P` is a conservation law | Proved |
| ★ `freeEnzyme_not_conserved` | `E` alone is not a conservation law | Proved |
| ★ `enzyme_total_constant` | `E(t) + ES(t) = E(0) + ES(0)` on any trajectory, any fluxes | Proved, conditional on a solution existing |

## Saturation response `vmax · x / (K + x)`

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| `saturation_zero` | value 0 at `x = 0` | none | Proved |
| `saturation_half` | value `vmax / 2` at `x = K` | `K ≠ 0` | Proved |
| `saturation_nonneg` | nonnegative | `vmax ≥ 0`, `K > 0`, `x ≥ 0` | Proved |
| ★ `saturation_lt_max` | strictly below `vmax` | `vmax > 0`, `K > 0`, `x ≥ 0` | Proved |
| `saturation_le_max` | at most `vmax` | `vmax ≥ 0`, `K > 0`, `x ≥ 0` | Proved |
| ★ `saturation_strictMonoOn`, `saturation_monotoneOn` | (strictly) increasing on `x ≥ 0` | `vmax > 0`, `K > 0` | Proved |
| ★ `lt_saturation_iff` | `y < f(x) ↔ y K / (vmax − y) < x` | `K > 0`, `x ≥ 0`, `y < vmax` | Proved |

## Linear dynamics `x' = a x`

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| `hasDerivAt_expTrajectory` | `x₀ e^{a t}` solves the equation | none | Proved |
| ★ `eq_expTrajectory_of_hasDerivAt` | it is the only solution on `ℝ` | solution differentiable at all `t` | Proved |
| `expTrajectory_strictAnti`, `_strictMono` | strictly decreasing / increasing | `x₀ > 0`, `a < 0` / `a > 0` | Proved |
| ★ `tendsto_expTrajectory_atTop_zero` | tends to 0 as `t → ∞` | `a < 0` | Proved |

## Population models

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| `logisticRate_capacity` | `P = K` is an equilibrium | `K ≠ 0` | Proved |
| `logisticRate_pos`, `logisticRate_neg` | growth below capacity, decline above | `r > 0`, `0 < P < K` / `0 < K < P` | Proved |
| ★ `logisticRate_le_exponentialRate` | logistic rate ≤ exponential rate | `r ≥ 0`, `K > 0`, `P ≥ 0` | Proved |
| ★ `netGrowthRate_neg_iff` | `r − αB < 0 ↔ B > r/α` | `α > 0` | Proved |
| `netGrowthRate_pos_iff` | `r − αB > 0 ↔ B < r/α` | `α > 0` | Proved |
| `netGrowthRate_strictAnti` | net growth decreases in `B` | `α > 0` | Proved |
| `eq_expTrajectory_of_inhibited` | unique solution of `P' = (r − αB) P` | constant `B` | Proved |
| `population_strictAnti_of_netGrowthRate_neg`, `population_tendsto_zero_of_netGrowthRate_neg` | decline and extinction | `r − αB < 0`, constant `B` (`P₀ > 0` for strict decline) | Proved |
| `glvField_zero`, `glvField_eq_zero_of_balance`, `glvField_apply_eq_zero_of_absent` | equilibria of generalized Lotka–Volterra | as stated | Proved |
| ★ `glvField_unit_eq_logisticRate` | one-species Lotka–Volterra is logistic growth | none | Proved |

## Composition of Model A and Model B

Parameters: `Bmax > 0`, `K > 0` (Model A); `r > 0`, `α > 0` (Model B).
Threshold `N* = r K / (α Bmax − r)`.

| Theorem | Statement | Extra assumptions | Status |
| --- | --- | --- | --- |
| `suppressionThreshold_pos` | `N* > 0` | `α Bmax > r` | Proved |
| ★ `composedGrowth_neg_iff` | `g(B(N)) < 0 ↔ N > N*` | `α Bmax > r`, `N ≥ 0` | Proved |
| ★ `composedGrowth_neg_of_threshold_lt` | `N > N* → g(B(N)) < 0` | `α Bmax > r` | Proved |
| ★ `composedGrowth_pos_of_max_le` | `g(B(N)) > 0` for all `N ≥ 0` | `α Bmax ≤ r` | Proved |
| `population_strictAnti_of_threshold_lt` | population strictly declines | `α Bmax > r`, `N > N*` constant, `P₀ > 0` | Proved |
| ★ `population_tendsto_zero_of_threshold_lt` | population tends to 0 | `α Bmax > r`, `N > N*` constant | Proved |

## Hill function `vmax (x/K)ⁿ / (1 + (x/K)ⁿ)`

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| `hill_half` | value `vmax / 2` at `x = K` | `K ≠ 0` | Proved |
| `hill_one` | coefficient 1 gives the saturation response | `K > 0`, `x ≥ 0` | Proved |
| `hill_nonneg`, `hill_lt_max` | between 0 and `vmax` | `vmax > 0`, `K > 0`, `x ≥ 0` | Proved |
| ★ `hill_strictMonoOn` | strictly increasing on `x ≥ 0` | `vmax > 0`, `K > 0`, `n > 0` | Proved |
| ★ `lt_hill_iff` | `y < hill x ↔ K (y/(vmax−y))^(1/n) < x` | `K > 0`, `n > 0`, `x ≥ 0`, `0 ≤ y < vmax` | Proved |
| ★ `tendsto_saturation_atTop` | saturation tends to `vmax` as `x → ∞` | `K > 0` | Proved |

## Monod (1949)

Parameters: `R_K > 0`, `C₁ > 0`. Positivity is added; the source leaves it implicit.

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| ★ `growthRate_half` | rate at `C = C₁` is `R_K / 2` (Monod's description of `C₁`) | none extra | Proved |
| ★ `tendsto_growthRate` | rate tends to `R_K` as `C → ∞` (Monod's description of `R_K`) | none extra | Proved |
| `growthRate_lt_RK` | `R_K` is never attained | `C ≥ 0` | Proved |
| `growthRate_strictMonoOn` | rate increases with `C` on `C ≥ 0` | none extra | Proved |
| ★ `density_growthRate` | `x₀ 2^(R t)` has rate `R` by Monod's definition of `R` | `x₀ > 0`, `t₁ ≠ t₂` | Proved |
| ★ `density_eq_expTrajectory` | `R` divisions per unit time is rate coefficient `R ln 2` | none | Proved |

## Regoes et al. (2004)

Parameters: `ψmax > 0`, `Emax > ψmax`, `EC50 > 0`, `κ > 0`. All four constraints
are added; the source does not state them.

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| `psi_zero` | `ψ(0) = ψmax` | none extra | Proved |
| ★ `psi_zMIC` | `ψ(zMIC) = 0` for `zMIC = EC50 (ψmax/(Emax−ψmax))^(1/κ)` | none extra | Proved |
| ★ `psi_neg_iff` | `ψ(a) < 0 ↔ a > zMIC` | `a ≥ 0` | Proved |
| ★ `psi_strictAntiOn` | `ψ` strictly decreasing on `a ≥ 0` | none extra | Proved |
| `ψmin_lt_psi`, `psi_le_ψmax` | `ψmin < ψ(a) ≤ ψmax` | `a ≥ 0` | Proved |
| ★ `psi_eq_rewritten` | equation 3 follows from equations 1 and 2 | `a ≥ 0` | Proved |
| `density_strictAnti`, ★ `density_tendsto_zero` | density declines to 0 | constant `a > zMIC` (`X₀ > 0` for strict decline) | Proved |

Fidelity caveat: the display equations of this paper were not read. Equation 2
is assumed to be the standard Hill function with the parameters the text
names, and equation 3 is the form implied by the text's definitions.

## Composition of Monod (1949) and Regoes et al. (2004)

Added hypotheses, made by neither paper: the kill rate is independent of
nutrient level and growth rate; `ψmax = log₁₀ 2 · R(C)`; `log₁₀ 2 · R_K ≤ Emax`.

| Theorem | Statement | Assumptions | Status |
| --- | --- | --- | --- |
| ★ `netGrowth_neg_iff` | net growth at `(C, a)` is negative iff `a > zMIC(C)` | added hypotheses; `C > 0`, `a ≥ 0` | Proved, conditional |
| ★ `zMICAt_strictMonoOn` | `zMIC(C)` strictly increases with `C` on `C > 0` | added hypotheses | Proved, conditional |
| ★ `netGrowth_neg_of_le` | a dose that suppresses at nutrient level `D` suppresses at any `0 < C ≤ D` | added hypotheses; `a ≥ 0` | Proved, conditional |

## Dimensions and import

| Theorem | Statement | Status |
| --- | --- | --- |
| `Dimension.div_mul_cancel` and related | dimension arithmetic | Proved |
| ★ `Dimensional.netGrowthRateQ_neg_iff` | the untyped sign criterion holds for the dimension-checked model | Proved |
| ★ `ImportedEnzyme.totalEnzyme_conserved` | `E + ES` conserved in the network generated from SBML | Proved |

## Not proved, not checked

**Empirical assumptions.** That any organism's production follows a saturation
curve, or that inhibition is linear in dose. These appear only in provenance
records. Models A and B under `Papers/Examples` are illustrative and cite no publication.

**Compatibility of composed models.** That the compound in Model A is the
compound in Model B, in the same unit and compartment, and that production
equilibrates fast compared with population change.

**Provenance records.** Text only. Not checked against sources or against the
Lean definitions they describe.

**Fidelity of paper formalizations.** That `Monod1949` and `Regoes2004` match
their sources is a claim made by the module headers and reviewed by hand, not
by Lean. For Regoes 2004 the display equations were not read at all.

**The rate-independence hypothesis** of the Monod–Regoes composition. It is an
assumption, and it is known to be doubtful for many antibiotics.

**Units and logarithm bases.** Dimensions can be checked with `Quantity`, on an
opt-in basis. Units and the base of logarithmic rates are not represented.

**The SBML importer.** The Python script is not verified. Its output is
type-checked by Lean, but nothing proves the output matches the SBML file. It
has been run on one hand-written model only.

**Existence of solutions.** Trajectory theorems for reaction networks assume a
differentiable solution is given. Existence, positivity and boundedness of
solutions of mass-action systems are not proved. For the linear equation
`x' = a x` existence and uniqueness are both proved.

**Time-varying inputs.** The inhibition and composition dynamics assume the
compound and nutrient levels are constant in time.

**Numerics.** No numerical algorithm is implemented or verified. All theorems
are about exact real numbers.

