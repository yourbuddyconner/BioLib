# Roadmap

This file separates what exists from what is planned. Nothing under "Not
started" is implemented.

## Done

- Reaction networks, stoichiometric matrix, mass balance, conservation laws, mass-action kinetics.
- Saturation response and the linear ODE `x' = a x`.
- Exponential, logistic and Monod growth; linear inhibition; generalized Lotka–Volterra field.
- Lightweight provenance records.
- Composition of two independently defined models into a nutrient threshold theorem.

## Next

**Real published models.** Formalize two published models that share an
interface, each with exact source, equation numbers, assumptions, a proved
property and documented deviations. Then decide whether they compose. No real
paper has been formalized yet. The models under `Papers/Examples` are
illustrative. Candidate sources must be read and checked against the original
text before any module cites them.

**Typed units.** Units are free text today. Options are a dimension-indexed
quantity type or a dimension check at the provenance level.

**Network composition across species types.** A map from each network's species
into a common type, with conservation results for the embedded union.

**Narrower imports.** Replace `import Mathlib` with the specific modules each file needs.

## Later

**Interoperability.** Find the smallest subset of SBML that maps faithfully to
`Network` (species, reactions, integer stoichiometry). Write an importer,
probably in Python, that emits Lean source with a provenance record. Look at
BioModels and COBRA-style models as inputs. An imported model is a definition;
importing it validates nothing.

**Dynamics.** Existence and positivity of solutions for mass-action systems.
Closed-form solution and stability for logistic growth. Stability of
Lotka–Volterra equilibria. Chemostat models with explicit nutrient dynamics.

**Flux analysis.** Flux cones, elementary modes, flux balance analysis as a
linear program.

**Numerics.** If simulation is added, state the numerical method, its
assumptions and error bounds. Real-number theorems do not transfer to
floating-point code without that.

## Not started: further domains

- Gene regulation (Hill functions, toggle switches, feed-forward loops).
- Signalling networks.
- Sequence biology.
- Evolutionary dynamics (replicator equations, mutation–selection balance).
- Spatial and stochastic ecological models.

## Research questions

Open questions, not commitments:

- Can two models be composed automatically when entities, units and assumptions match?
- Can assumption dependency graphs show which conclusions rest on which estimates?
- Can incompatible mathematical assumptions across models be detected without
  treating empirical disagreement as logical contradiction?
- Can a language model translate a published model into candidate Lean and repair failed proofs?
- Can formal composition yield implications no source paper states?
- Can unmet proof obligations point to the measurement that would make a conclusion derivable?
