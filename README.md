# BioLib

Formally verified computational biology in Lean 4, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

BioLib represents biological models as reusable mathematical objects and proves
properties of them that the Lean kernel checks. The long-term aim is a body of
models, drawn from published work, that can be composed with each other to
derive new conclusions, with every conclusion traceable to the assumptions it
rests on.

**Status.** `lake build` passes on Lean `v4.34.0` with Mathlib `v4.34.0`. There
is no `sorry` and no added axiom: the main theorems depend only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The full list is
in [docs/PROOF_STATUS.md](docs/PROOF_STATUS.md). Two published models are
formalized from their sources (Monod 1949, Regoes et al. 2004).

## What a proof here does and does not mean

The library keeps three things apart:

| Category | In Lean | Checked by the kernel? |
| --- | --- | --- |
| Mathematical definitions | `def`, `structure` | Type-checked |
| Verified theorems | `theorem`, proved from explicit hypotheses | Yes |
| Empirical evidence | Provenance records (text) | No |

A theorem in BioLib says: *if* the stated assumptions hold, the conclusion
follows. It does not say the assumptions are true of any organism, and it does
not say a formalization matches the paper it cites. Those need separate evidence
and review. Results are over the mathematical real numbers and say nothing
about floating-point simulation.

## What is in the library

**Biochemical reaction networks** (`BioLib/Chemistry`)

- Reactions with nonnegative integer stoichiometric coefficients, and their net change.
- Reaction networks, the stoichiometric matrix `S`, rate of change `ẋ = S v`, steady state `S v = 0`.
- Conservation laws `cᵀ S = 0`, and the union of two networks over shared species.
- Mass-action kinetics.

**Microbial population dynamics** (`BioLib/Ecology`)

- Exponential and logistic growth, Monod nutrient-dependent growth.
- Linear inhibition by an antimicrobial compound, `dP/dt = (r - αB) P`.
- Generalized Lotka–Volterra competition.

**Shared foundations** (`BioLib/Foundations`)

- The saturation response `vmax · x / (K + x)` (Michaelis–Menten, Monod, Holling II).
- The linear ODE `x' = a x`: closed-form solution and uniqueness.

- The Hill function, defined through the saturation response.
- Dimensioned quantities (`Quantity d`), opt-in.

**Published models** (`BioLib/Papers`)

- `Monod1949`: growth rate against nutrient concentration, `R = R_K · C / (C₁ + C)`
  (Monod, *Annu. Rev. Microbiol.* 3:371, equation 2).
- `Regoes2004`: net bacterial growth rate against antibiotic concentration
  (Regoes et al., *Antimicrob. Agents Chemother.* 48:3670, equations 1 to 4).
  The paper's rewritten form (equation 3) is derived as a theorem.
- `MonodRegoes`: their composition. Under an added, explicitly stated
  hypothesis that the kill rate does not depend on growth rate, the
  concentration needed to stop growth rises strictly with nutrient level.
  This is a consequence of the hypothesis, not a finding of either paper.

Each module's header states what was taken from the source, what was added,
and what could not be checked. For Regoes 2004 the display equations could not
be read in the copy consulted and were reconstructed from the paper's text.

**Simulator** (`BioLib/Sim`, `Main.lean`, `python/biolib_sim.py`)

- A community simulator written in Lean: competitive Lotka–Volterra dynamics
  with an inhibitor, integrated by Euler steps, then measurement bias,
  relative abundance and multinomial read counts. It compiles to the
  `biolib-sim` executable, which writes CSV.
- The model definitions are generic over the number type. The executable runs
  them on floats; the theorems are about the same definitions over the reals.
- Proved: the simulated rate law is the library's Lotka–Volterra field; an
  Euler step keeps absent species absent and present species present under a
  step-size condition; relative abundance is unchanged when all abundances
  scale together, so total abundance cannot be recovered from it.
- Not proved: anything about floating-point evaluation, the random sampling
  code, or the accuracy of the Euler method.
- `python/biolib_sim.py` runs the executable and returns numpy arrays.

**SBML import** (`scripts/sbml_to_lean.py`)

- Translates species and integer-stoichiometry reactions from an SBML file
  into a `Network` with a provenance record. Kinetic laws are not imported.

**Provenance** (`BioLib/Evidence`)

- Records for sources, parameters, units, assumptions and parameter evidence.

**Worked examples**

- `BioLib/Examples/EnzymeNetwork.lean`: the mechanism `E + S ⇌ ES → E + P`.
  Total enzyme `E + ES` and total substrate `S + ES + P` are proved to be
  conservation laws, so they stay constant on every trajectory whatever the
  rate laws are. Free enzyme alone is proved not to be conserved.
- `BioLib/Papers/Examples/`: two independent illustrative models and their composition.
- `BioLib/Examples/ImportedEnzyme.lean`: a conservation law proved on a network
  generated from `examples/sbml/enzyme.xml`.

## A complete example: composing two models

Model A (`NutrientResponse`) gives the level of an antimicrobial compound as a
function of nutrient concentration:

```
B(N) = Bmax · N / (K + N)
```

Model B (`MicrobialInhibition`) gives the net growth rate of a target microbe
as a function of compound concentration:

```
g(B) = r − α · B
```

The two modules do not import each other. `Composition.lean` imports both and
composes them as functions:

```lean
noncomputable def composedGrowth (N : ℝ) : ℝ := netGrowth b (production a N)

noncomputable def suppressionThreshold : ℝ := b.r * a.K / (b.α * a.Bmax - b.r)

theorem composedGrowth_neg_of_threshold_lt (h : b.r < b.α * a.Bmax)
    (hN : suppressionThreshold a b < N) : composedGrowth a b N < 0
```

In words: if the compound can in principle overcome growth (`α · Bmax > r`),
then any nutrient level above `r · K / (α · Bmax − r)` gives negative net
growth. Neither model states this on its own. The proof uses a lemma from each
model: the inversion of the saturation curve from A, and the sign criterion
`g(B) < 0 ↔ B > r / α` from B.

The same file also proves the converse on `N ≥ 0`, that no nutrient level
suppresses growth when `α · Bmax ≤ r`, and that a population held above the
threshold declines strictly and tends to zero.

These two models are illustrative. They are not attributed to any publication.

## Install and build

You need [elan](https://github.com/leanprover/elan), the Lean toolchain
manager. It reads `lean-toolchain` and installs the pinned Lean version.

```sh
git clone https://github.com/yourbuddyconner/BioLib.git
cd BioLib
lake exe cache get   # download prebuilt Mathlib, a few minutes
lake build
```

Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. Skipping `lake exe cache get` still works, but compiles
Mathlib from source, which takes hours.

To check which axioms a theorem depends on:

```lean
import BioLib
#print axioms BioLib.Papers.Examples.Composition.composedGrowth_neg_of_threshold_lt
```

To simulate data from Python (needs numpy):

```sh
lake build biolib-sim
cd python && python3 -c "
from biolib_sim import simulate
d = simulate(species=50, samples=200, studies=3, bias_sd=0.5, seed=1)
print(d.counts.shape, d.treated.mean())"
```

Or directly: `.lake/build/bin/biolib-sim --help`.

To run the source checks (no `sorry`, no `axiom`, generated files up to date):

```sh
scripts/check.sh
```

To import an SBML model:

```sh
python3 scripts/sbml_to_lean.py model.xml ModelName > BioLib/Imported/ModelName.lean
```

## Repository layout

```
BioLib.lean                  root import
BioLib/
  Foundations/               Dynamics, Saturation, Hill, Quantities
  Chemistry/                 Reaction, Network, Conservation, Kinetics
  Ecology/                   Growth, Inhibition, Competition, Dimensional
  Evidence/                  Provenance
  Examples/                  EnzymeNetwork, ImportedEnzyme
  Imported/                  generated from SBML, do not edit
  Sim/                       Core (no Mathlib), Run (floats, sampling), Theorems
  Papers/                    Monod1949, Regoes2004, MonodRegoes
  Papers/Examples/           NutrientResponse, MicrobialInhibition, Composition
Main.lean                    biolib-sim command line
python/                      biolib_sim.py wrapper and its checks
scripts/                     sbml_to_lean.py, check.sh
examples/sbml/               SBML test model
docs/                        architecture, formalization guide, proof status, roadmap
```

## Adding a model

See [docs/FORMALIZATION_GUIDE.md](docs/FORMALIZATION_GUIDE.md). In short:

1. Put parameters and their constraints in a `structure`.
2. Define the model with existing BioLib functions where one fits.
3. State every assumption as a hypothesis or a structure field. Never as an `axiom`.
4. Add a provenance record. Use `source := none` unless the model really is the one in the paper.
5. Prove at least one property. No `sorry`.

## Documentation

- [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md): design and module boundaries.
- [docs/FORMALIZATION_GUIDE.md](docs/FORMALIZATION_GUIDE.md): how to formalize a model or paper.
- [docs/PROOF_STATUS.md](docs/PROOF_STATUS.md): theorems, assumptions, limitations.
- [docs/ROADMAP.md](docs/ROADMAP.md): what is planned and what is not started.
