# Architecture

## Strategy

BioLib is a library of mathematical models and theorems about them. It is not a
database of biological facts and it does not define an ontology of biological
entities. A model is a Lean definition. A result is a Lean theorem whose
hypotheses are the model's assumptions.

Three kinds of content are kept apart:

1. **Definitions.** `def` and `structure` declarations. They assert nothing.
2. **Theorems.** Deductions from explicit hypotheses, checked by the kernel.
3. **Evidence.** Sources, parameter estimates and prose assumptions, stored as
   data in `BioLib.Evidence`. The kernel does not check them and no theorem
   depends on them.

No `axiom` declarations and no `sorry` are allowed. An empirical claim enters a
theorem only as a hypothesis, so it is visible in the theorem's statement.

## Design principles

- **Index types, not ontologies.** Species and reactions are arbitrary types
  `S` and `R`. A model chooses its own, usually a small `inductive`.
- **Reuse Mathlib.** Matrices, `mulVec`, `dotProduct`, derivatives, filters and
  order lemmas are Mathlib's. BioLib adds no linear algebra or analysis of its own.
- **One definition per mathematical form.** `saturation` is defined once and
  serves as Michaelis–Menten, Monod and Holling type II. `expTrajectory` is
  defined once and serves growth, decay and inhibition.
- **Assumptions travel with parameters.** A model's parameters live in a
  structure whose fields include the constraints (`K_pos : 0 < K`). A value of
  the structure is a parameter set that satisfies them.
- **Composition is function composition** where the models share an interface
  quantity, and network union where they share species.
- **Real numbers.** All quantities are `ℝ`. Theorems are exact statements about
  reals and do not cover numerical simulation.

## Modules

| Module | Contents | Depends on |
| --- | --- | --- |
| `Foundations.Dynamics` | `expTrajectory`, solution and uniqueness for `x' = a x`, monotonicity, decay | Mathlib |
| `Foundations.Saturation` | `saturation`, bounds, monotonicity, inversion | Mathlib |
| `Foundations.Hill` | `hill`, bounds, monotonicity, inversion | `Saturation` |
| `Foundations.Quantities` | `Dimension`, `Quantity d` | Mathlib |
| `Chemistry.Reaction` | `Reaction`, `netChange`, `reverse` | Mathlib |
| `Chemistry.Network` | `Network`, stoichiometric matrix, `rateOfChange`, `IsSteadyState`, `union` | `Reaction` |
| `Chemistry.Conservation` | `IsConservationLaw`, invariance under fluxes and along trajectories, union | `Network` |
| `Chemistry.Kinetics` | mass-action rate, flux and vector field | `Conservation` |
| `Ecology.Growth` | exponential, logistic, Monod | `Foundations` |
| `Ecology.Inhibition` | `netGrowthRate`, sign criteria, dynamics | `Foundations.Dynamics` |
| `Ecology.Competition` | generalized Lotka–Volterra field | `Ecology.Growth` |
| `Ecology.Dimensional` | dimension-checked wrappers for saturation and inhibition | `Quantities`, `Inhibition` |
| `Evidence.Provenance` | `Source`, `Assumption`, `Parameter`, `ParameterEvidence`, `ModelRecord` | none |
| `Examples.EnzymeNetwork` | `E + S ⇌ ES → E + P` and its conservation laws | `Chemistry` |
| `Papers.Examples.*` | two illustrative models and their composition | `Foundations`, `Ecology`, `Evidence` |
| `Papers.Monod1949`, `Papers.Regoes2004` | source-grounded models | `Foundations`, `Evidence` |
| `Papers.MonodRegoes` | composition of the two | both paper modules |
| `Sim.Core` | generic computable model, Euler step, relative abundance | none (no Mathlib) |
| `Sim.Run` | random pool, sampling, CSV output, on `Float` | `Sim.Core` |
| `Sim.Theorems` | properties of `Sim.Core` over the reals | `Sim.Core`, `Ecology`, `Chemistry` |
| `Imported.*` | networks generated from SBML | `Chemistry.Network`, `Evidence` |
| `Examples.ImportedEnzyme` | a theorem about a generated network | `Imported`, `Chemistry` |

`Chemistry` and `Ecology` do not import each other. Both may import
`Foundations`. `Papers` modules import domain modules and `Evidence`, never the
reverse.

## Decisions and their reasons

**Stoichiometric coefficients are natural numbers; net change is an integer.**
This matches the usual chemical reading. The matrix used with real fluxes
(`realStoichMatrix`) is the integer matrix with entries cast to `ℝ`.

**Reactions are irreversible.** A reversible reaction is two entries in the
network. `Reaction.reverse` builds the second one.

**A network is a function `R → Reaction S`.** Duplicate reactions are allowed
and count as separate columns.

**Conservation is defined by `cᵀ S = 0` with real weights.** The equivalent
reaction-by-reaction form (`isConservationLaw_iff`) is what concrete proofs use.

**Network composition requires a shared species type.** `Network.union` takes
two networks over the same `S`. Combining networks over different species types
needs an explicit map into a common type; that map is where the scientific
claim "these are the same species" lives, and it is not implemented yet.

**Trajectories are functions `ℝ → S → ℝ` with a derivative at every time.**
Results about trajectories assume a solution is given. Existence of solutions
is not proved for nonlinear systems.

**Dimensions are opt-in; units are not tracked.** Core definitions take bare
reals, so that Mathlib's lemmas about `ℝ` apply directly. `Quantity d` tags a
real with a dimension, and `Ecology.Dimensional` wraps two models with typed
signatures whose values equal the untyped functions by definition. Dimension
checking does not tell hours from seconds, and does not tell a base-2 rate from
a base-10 rate: the Monod–Regoes composition needs a factor `log₁₀ 2` between
two quantities of the same dimension. Units remain text in provenance records.

**Paper modules reconstruct, then prove.** Where a source states a derived
formula, the module defines the primitive equations and proves the derived one
(`Regoes2004.psi_eq_rewritten`). A transcription error then shows up as a
failed proof.

**Compositions name their added hypotheses.** A composition of two papers
usually needs an assumption neither paper makes. It goes in the module header
and in the theorem's hypotheses, and the result is described as conditional.

**The simulator is Lean; Python is a wrapper.** Models, the integrator, the
observation step and data generation are Lean code. Python (`python/`) only
runs the executable and hands arrays to numpy and training code.

**Executable code does not import Mathlib.** An executable that imports
Mathlib must compile all of it. `Sim.Core` and `Sim.Run` use only the Lean
core library; `Sim.Theorems` imports both `Sim.Core` and Mathlib and proves
facts about the core definitions.

**One definition, three number types.** `Sim.Core` assumes only `+ - * /` and
`0` of its number type, because `Float` is not a lawful field. The same
definition runs on `Float`, runs exactly on `Rat`, and is reasoned about on
`ℝ`. Theorems hold for exact arithmetic. For floats they are a specification,
tested by `biolib-sim --selfcheck` (float against exact rational on a small
system) and `python/test_biolib_sim.py`. Exact rational runs are limited to
about 16 steps of a quadratic model, because the size of the numbers doubles
every step. Known divergence: `0 / 0` is `0` over the reals and NaN in floats.

**States are functions in proofs and arrays at run time.** Model functions
take and return `Fin n → α`. `stepVec` evaluates one into a `Vector`, so each
step is stored and not recomputed; `stepVec_getElem` says the stored values
are the function's values.

**SBML import is stoichiometry only.** `scripts/sbml_to_lean.py` rejects what
it cannot map faithfully (non-integer stoichiometry, boundary and constant
species) and lists what it ignores (kinetic laws, compartments, rules, events)
in the generated file. Generated files live in `BioLib/Imported` and are
checked against their source by `scripts/check.sh`.

**Total division.** In Lean `x / 0 = 0`. Definitions such as `saturation` are
therefore defined everywhere, and theorems carry the hypotheses (`0 < K`,
`0 ≤ x`) that keep the denominator positive.

**Every file imports all of Mathlib.** This is simple and slow. Narrowing the
imports is listed in the roadmap.
