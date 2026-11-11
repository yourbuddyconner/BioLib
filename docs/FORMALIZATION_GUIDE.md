# Formalization guide

How to add a biological model, or a model from a paper, to BioLib.

## Before writing Lean

Write down, on paper:

1. The equations, with the equation numbers in the source.
2. Every symbol: what it is, its unit, and whether it is a variable or a parameter.
3. Every constraint on parameters and variables. Include the ones the source
   leaves implicit, such as positivity.
4. Every assumption, sorted into three kinds:
   - **mathematical**: needed for the formulas to make sense (`K > 0`);
   - **modelling**: a simplification the authors chose (well-mixed, constant concentration);
   - **empirical**: a claim about the world (the response is saturating).
5. The property you intend to prove.

If the source is ambiguous, record the ambiguity and the reading you chose. Do
not pick one silently.

## Step 1: find what already exists

Check `Foundations`, `Chemistry` and `Ecology` for the mathematical form. A
Monod term, a Michaelis–Menten rate and a Holling type II response are all
`saturation`. A first-order process is `expTrajectory`. Define a new function
only if no existing one fits, and put it in the domain folder, not in the paper
module, if another model could use it.

## Step 2: parameters as a structure

```lean
structure Params where
  Bmax : ℝ
  K : ℝ
  Bmax_pos : 0 < Bmax
  K_pos : 0 < K
```

Constraints that the source states for all uses of the model go in the
structure. Conditions that only some theorems need (for example
`r < α * Bmax`) stay as hypotheses of those theorems.

## Step 3: the model as a definition

```lean
noncomputable def production (p : Params) (N : ℝ) : ℝ := saturation p.Bmax p.K N
```

Write it in terms of library functions so that library lemmas apply.

## Step 4: theorems

State each result with all of its assumptions as hypotheses.

```lean
theorem production_monotoneOn : MonotoneOn (production p) (Set.Ici 0) :=
  saturation_monotoneOn p.Bmax_pos p.K_pos
```

Rules:

- No `sorry`.
- No `axiom`. If a result needs an empirical fact, make the fact a hypothesis.
- Do not put a measured parameter value into a definition. Prove the theorem
  for all parameters satisfying the constraints. A specific value belongs in a
  `ParameterEvidence` record.
- Prefer a short proof from library lemmas to a long proof from first principles.

## Step 5: provenance record

Every paper module defines `record : BioLib.Evidence.ModelRecord`.

```lean
def record : ModelRecord where
  id := "BioLib.Papers.Examples.NutrientResponse"
  version := "0.1.0"
  source := none
  parameters := [ { name := "K", unit := "concentration", description := "..." } ]
  assumptions :=
    [ { name := "positive parameters", kind := .mathematical,
        statement := "Bmax > 0 and K > 0",
        formalizedAs := "Params.Bmax_pos, Params.K_pos" } ]
  applicability := "Nonnegative nutrient concentrations."
```

Conventions:

- `id` is the Lean namespace of the module.
- `source` is `none` unless the model is the one the paper actually uses. For a
  real paper, give the full citation, the DOI, and the equation numbers in `locator`.
- List every assumption from your notes. Fill `formalizedAs` when a hypothesis
  or field encodes it. An assumption with no formal counterpart is one the
  theorems do not depend on formally but the science does. List it anyway.
- Use `deviations` for every difference from the source: renamed symbols,
  dropped terms, a changed domain, a chosen reading of an ambiguous passage.
- Put measured values in `evidence`, with organism, strain and conditions in `context`.

The record is text. Lean does not check it against the paper or against the
definitions. Review it by hand.

## Step 6: module docstring

Start the file with a `/-! ... -/` block that gives the equations, says whether
the model is source-grounded or illustrative, and lists what Lean does not check.

## Composing models

Two models compose when an output of one is an input of the other.

1. Keep the two modules independent. Neither imports the other.
2. Write a third module that imports both and defines the composite by applying
   one model's function to the other's.
3. Prove the result from lemmas of the two components. If the proof needs a
   fact about one component alone, add that lemma to the component.
4. In the docstring, list the compatibility assumptions Lean cannot check: same
   quantity, same unit, same compartment, compatible time scales, compatible
   experimental context.

`BioLib/Papers/Examples/Composition.lean` is the reference example.

Reaction networks compose with `Network.union` when they share a species type.
A conservation law of both parts is a conservation law of the union
(`IsConservationLaw.union`).

## Checklist

- [ ] `lake build` passes with no warnings from your files.
- [ ] No `sorry`, no `axiom`.
- [ ] `#print axioms` on your main theorems shows only `propext`, `Classical.choice`, `Quot.sound`.
- [ ] Every assumption is a hypothesis or a structure field.
- [ ] A provenance record exists, and `source` is honest.
- [ ] `docs/PROOF_STATUS.md` lists the new theorems.
- [ ] The root file `BioLib.lean` imports the new module.
