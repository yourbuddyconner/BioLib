# Roadmap

This file separates what exists from what is planned. Nothing under "Not
started" is implemented.

## Done

- Reaction networks, stoichiometric matrix, mass balance, conservation laws, mass-action kinetics.
- Saturation response, Hill function, and the linear ODE `x' = a x`.
- Exponential, logistic and Monod growth; linear inhibition; generalized Lotka–Volterra field.
- Lightweight provenance records.
- Composition of two independently defined illustrative models into a nutrient threshold theorem.
- Two source-grounded models, Monod (1949) and Regoes et al. (2004), and a conditional composition.
- Opt-in dimensioned quantities.
- SBML importer for stoichiometry, tested on one hand-written model.
- CI: source checks and `lake build`.

## Next

**Check Regoes 2004 against the typeset equations.** The display equations
could not be read in the copy consulted. Someone with the PDF should compare
equations 2 and 3 with `deathRate` and `psi_eq_rewritten`, and record fitted
values from Table 1 as parameter evidence.

**Growth-rate-dependent killing.** The Monod–Regoes composition assumes the
kill rate is independent of growth rate. Find a published model of how kill
rate depends on growth rate, formalize it, and replace the assumption.

**Time-varying concentration.** Regoes' equation 5 (periodic dosing with
exponential decay) and the resulting non-autonomous linear ODE.

**Units and logarithm bases.** Dimensions are tracked; units and the base of
logarithmic rates are not. Decide whether to type them.

**Network composition across species types.** A map from each network's species
into a common type, with conservation results for the embedded union.

**SBML on real models.** Run the importer on BioModels entries. Decide how to
represent boundary species, which most published models use and the importer
currently rejects. Import kinetic laws for mass-action reactions.

**Narrower imports.** Replace `import Mathlib` with the specific modules each
file needs. A first attempt with `#min_imports` did not give usable results for
downstream files.

**Toolchain.** Move to the current Lean and Mathlib release and regenerate
`lake-manifest.json` with `lake update`.

## Later

**Interoperability.** COBRA-style metabolic models, and identifier systems
(ChEBI, KEGG) as provenance for species. An imported model is a definition;
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
