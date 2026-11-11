# BioLib

Formally verified computational biology in Lean 4, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

BioLib represents biological models as reusable mathematical objects and proves
properties of them that the Lean kernel checks. The long-term aim is a body of
models, drawn from published work, that can be composed with each other to
derive new conclusions, with every conclusion traceable to the assumptions it
rests on.

> **Status: initial import. The build has not been verified yet.** This notice
> will be replaced by the verified theorem list once `lake build` passes.

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

**Provenance** (`BioLib/Evidence`)

- Records for sources, parameters, units, assumptions and parameter evidence.

**Worked examples**

- `BioLib/Examples/EnzymeNetwork.lean`: the mechanism `E + S ⇌ ES → E + P`.
- `BioLib/Papers/Examples/`: two independent models and their composition.

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

## Repository layout

```
BioLib.lean                  root import
BioLib/
  Foundations/               Dynamics, Saturation
  Chemistry/                 Reaction, Network, Conservation, Kinetics
  Ecology/                   Growth, Inhibition, Competition
  Evidence/                  Provenance
  Examples/                  EnzymeNetwork
  Papers/Examples/           NutrientResponse, MicrobialInhibition, Composition
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
