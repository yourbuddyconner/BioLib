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

## Not proved, not checked

**Empirical assumptions.** That any organism's production follows a saturation
curve, or that inhibition is linear in dose. These appear only in provenance
records. Models A and B are illustrative and cite no publication.

**Compatibility of composed models.** That the compound in Model A is the
compound in Model B, in the same unit and compartment, and that production
equilibrates fast compared with population change.

**Provenance records.** Text only. Not checked against sources or against the
Lean definitions they describe.

**Units.** Not represented in types.

**Existence of solutions.** Trajectory theorems for reaction networks assume a
differentiable solution is given. Existence, positivity and boundedness of
solutions of mass-action systems are not proved. For the linear equation
`x' = a x` existence and uniqueness are both proved.

**Time-varying inputs.** The inhibition and composition dynamics assume the
compound and nutrient levels are constant in time.

**Numerics.** No numerical algorithm is implemented or verified. All theorems
are about exact real numbers.

**Real papers.** None formalized yet.
