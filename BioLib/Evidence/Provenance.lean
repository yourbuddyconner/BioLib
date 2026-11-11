/-!
# Provenance metadata

Lightweight records that tie a formal model to where it came from.

**Trust boundary.**  Everything in this file is descriptive data: strings and
enumerations.  The Lean kernel does not check that a record matches the paper it
cites, that a parameter estimate is right, or that an assumption is true of any
organism.  The only assumptions that carry logical weight are hypotheses of
theorems and fields of parameter structures.  A record lists them in prose so a
reader can trace them; it never turns an empirical claim into an axiom.

The three categories kept apart throughout the library:

* mathematical definitions: `def`s and `structure`s describing a model;
* empirical evidence: observations and estimates reported by a source, recorded
  here as data;
* verified theorems: `theorem`s proved from explicit hypotheses.
-/

namespace BioLib.Evidence

/-- A published source and where in it the relevant material is. -/
structure Source where
  /-- Full human-readable citation. -/
  citation : String
  /-- DOI, when one exists. -/
  doi : Option String := none
  /-- Equation numbers, sections, figures or tables used. -/
  locator : String := ""
  deriving Repr

/-- What kind of statement an assumption is. -/
inductive AssumptionKind
  /-- A constraint needed for the mathematics, such as `0 < K`. -/
  | mathematical
  /-- A simplification chosen by the modeller, such as constant concentration. -/
  | modelling
  /-- A claim about the world that rests on observation. -/
  | empirical
  deriving Repr, DecidableEq

/-- An assumption stated in prose, with a pointer to its formal counterpart. -/
structure Assumption where
  /-- Short name. -/
  name : String
  /-- What kind of assumption it is. -/
  kind : AssumptionKind
  /-- The assumption in words. -/
  statement : String
  /-- The Lean hypothesis or structure field that encodes it, if any. -/
  formalizedAs : Option String := none
  deriving Repr

/-- A model parameter with its unit and meaning. -/
structure Parameter where
  /-- Symbol used in the Lean definition. -/
  name : String
  /-- Unit, as free text.  Units are not checked. -/
  unit : String
  /-- What the parameter represents. -/
  description : String
  deriving Repr

/-- Reported support for a parameter value.  The value is text: it is recorded,
not used in proofs. -/
structure ParameterEvidence where
  /-- Name of the parameter concerned. -/
  parameter : String
  /-- Reported value or range, with unit. -/
  value : String
  /-- Where the value is reported. -/
  source : Source
  /-- Organism, strain, medium, temperature and other experimental conditions. -/
  context : String := ""
  deriving Repr

/-- Provenance record for one formal model. -/
structure ModelRecord where
  /-- Stable identifier, conventionally the Lean namespace of the model. -/
  id : String
  /-- Version of the formalization. -/
  version : String
  /-- The source, or `none` for an illustrative model with no publication behind it. -/
  source : Option Source
  /-- Parameters of the model. -/
  parameters : List Parameter := []
  /-- Assumptions under which the model's theorems are stated. -/
  assumptions : List Assumption := []
  /-- Experimental context the source model was developed in. -/
  context : String := ""
  /-- Conditions outside which the model should not be applied. -/
  applicability : String := ""
  /-- Evidence for parameter values. -/
  evidence : List ParameterEvidence := []
  /-- Known differences between the source's presentation and the formalization. -/
  deviations : List String := []
  deriving Repr

/-- A record is source-grounded when it cites a publication. -/
def ModelRecord.isSourced (m : ModelRecord) : Bool := m.source.isSome

end BioLib.Evidence
