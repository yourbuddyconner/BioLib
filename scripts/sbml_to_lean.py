#!/usr/bin/env python3
"""Translate a small subset of SBML into a BioLib reaction network in Lean.

Usage:
    python3 scripts/sbml_to_lean.py MODEL.xml LeanModuleName > BioLib/Imported/LeanModuleName.lean

Supported subset
    Species and reactions with constant nonnegative integer stoichiometry.
    A reaction marked reversible becomes two reactions, `r` and `r_rev`.

Rejected (the script exits with an error instead of guessing)
    Non-integer or negative stoichiometry, stoichiometryMath, stoichiometry
    set by rules (constant="false"), species with boundaryCondition="true" or
    constant="true", references to undeclared species, a model with no
    species or no reactions.

Ignored (listed in the generated file)
    Compartments, parameters, kinetic laws, rules, events, initial values,
    units, annotations.  The generated network carries stoichiometry only.

Only the Python standard library is used.  The SBML file is treated as data.
"""
import hashlib
import re
import sys
import xml.etree.ElementTree as ET

LEAN_KEYWORDS = {
    "at", "by", "do", "end", "from", "fun", "have", "if", "in", "let", "match", "then",
    "else", "with", "where", "open", "show", "Type", "Prop", "Sort", "def", "theorem",
    "import", "namespace", "section", "variable", "instance", "structure", "inductive",
    "class", "example", "axiom", "for", "return", "using", "deriving", "extends",
}
ID_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def fail(msg):
    sys.exit(f"sbml_to_lean: unsupported model: {msg}")


def local(tag):
    return tag.rsplit("}", 1)[-1]


def children(node, name):
    return [c for c in node if local(c.tag) == name]


def child(node, name):
    found = children(node, name)
    return found[0] if found else None


def lean_name(sbml_id):
    if not ID_RE.match(sbml_id):
        fail(f"identifier {sbml_id!r} is not a plain SBML SId")
    if sbml_id in LEAN_KEYWORDS or sbml_id == "_":
        return f"«{sbml_id}»"
    return sbml_id


def lean_string(text):
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", " ") + '"'


def side(reaction, list_name, species_ids, level):
    """Return {species id: coefficient} for one side of a reaction."""
    coeffs = {}
    holder = child(reaction, list_name)
    for ref in (children(holder, "speciesReference") if holder is not None else []):
        sid = ref.get("species")
        rid = reaction.get("id")
        if sid not in species_ids:
            fail(f"reaction {rid!r} refers to undeclared species {sid!r}")
        if child(ref, "stoichiometryMath") is not None:
            fail(f"reaction {rid!r} uses stoichiometryMath")
        if level >= 3 and ref.get("constant", "true") != "true":
            fail(f"reaction {rid!r} has non-constant stoichiometry for {sid!r}")
        raw = ref.get("stoichiometry", "1")
        try:
            value = float(raw)
        except ValueError:
            fail(f"reaction {rid!r} has unreadable stoichiometry {raw!r}")
        if value < 0 or value != int(value):
            fail(f"reaction {rid!r} has non-integer or negative stoichiometry {raw!r} for {sid!r}")
        coeffs[sid] = coeffs.get(sid, 0) + int(value)
    return {s: n for s, n in coeffs.items() if n != 0}


def coeff_fun(coeffs, species_ids):
    if not coeffs:
        return "fun _ => 0"
    arms = [f"| .{lean_name(s)} => {coeffs[s]}" for s in species_ids if s in coeffs]
    if len(coeffs) < len(species_ids):
        arms.append("| _ => 0")
    return "fun " + " ".join(arms)


def fintype(type_name, ids):
    elems = ", ".join("." + lean_name(i) for i in ids)
    return (f"instance : Fintype {type_name} :=\n"
            f"  ⟨{{{elems}}}, fun x => by cases x <;> simp⟩")


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    path, module = sys.argv[1], sys.argv[2]
    if not ID_RE.match(module):
        sys.exit("sbml_to_lean: module name must be a plain identifier")
    data = open(path, "rb").read()
    digest = hashlib.sha256(data).hexdigest()
    root = ET.fromstring(data)
    if local(root.tag) != "sbml":
        fail("root element is not <sbml>")
    level = int(root.get("level", "0"))
    version = root.get("version", "?")
    if level not in (2, 3):
        fail(f"SBML level {level} (only levels 2 and 3 are handled)")
    model = child(root, "model")
    if model is None:
        fail("no <model> element")

    species_list = child(model, "listOfSpecies")
    species_ids = []
    for sp in (children(species_list, "species") if species_list is not None else []):
        sid = sp.get("id")
        if sp.get("boundaryCondition", "false") == "true":
            fail(f"species {sid!r} is a boundary species")
        if sp.get("constant", "false") == "true":
            fail(f"species {sid!r} is constant")
        species_ids.append(sid)
    if not species_ids:
        fail("no species")
    if len(set(species_ids)) != len(species_ids):
        fail("duplicate species id")

    reaction_list = child(model, "listOfReactions")
    reactions = []  # (lean id, reactants, products)
    ignored_kinetics = 0
    for rx in (children(reaction_list, "reaction") if reaction_list is not None else []):
        rid = rx.get("id")
        lhs = side(rx, "listOfReactants", species_ids, level)
        rhs = side(rx, "listOfProducts", species_ids, level)
        if child(rx, "kineticLaw") is not None:
            ignored_kinetics += 1
        reactions.append((rid, lhs, rhs))
        # SBML Level 2 defaults `reversible` to true; Level 3 requires the attribute.
        default = "true" if level == 2 else "false"
        if rx.get("reversible", default) == "true":
            reactions.append((rid + "_rev", rhs, lhs))
    if not reactions:
        fail("no reactions")
    rids = [r[0] for r in reactions]
    if len(set(rids)) != len(rids):
        fail("duplicate reaction id (a reaction id collides with a generated `_rev` id)")

    ignored = []
    for name in ("listOfCompartments", "listOfParameters", "listOfRules", "listOfEvents",
                 "listOfInitialAssignments", "listOfFunctionDefinitions",
                 "listOfUnitDefinitions", "listOfConstraints"):
        node = child(model, name)
        if node is not None and len(node):
            ignored.append(f"{name} ({len(node)})")
    if ignored_kinetics:
        ignored.append(f"kinetic laws ({ignored_kinetics})")

    model_id = model.get("id") or module
    model_name = model.get("name") or model_id
    file_name = path.replace("\\", "/").rsplit("/", 1)[-1]
    out = []
    w = out.append
    w("import BioLib.Chemistry.Network")
    w("import BioLib.Evidence.Provenance")
    w("")
    w("/-!")
    w(f"# Imported SBML model `{model_id}`")
    w("")
    w("Generated by `scripts/sbml_to_lean.py`.  Do not edit by hand; regenerate instead.")
    w("")
    w(f"* Source file: `{file_name}` (SBML Level {level} Version {version})")
    w(f"* SHA-256 of source file: `{digest}`")
    w(f"* Species: {len(species_ids)}.  Reactions: {len(reactions)} (reversible reactions are split in two).")
    w("")
    w("Only stoichiometry is imported.  Not imported: "
      + (", ".join(ignored) if ignored else "nothing else was present") + ".")
    w("")
    w("Importing a model validates nothing about its biology.  The network below is a")
    w("definition; it asserts no property of any real system.")
    w("-/")
    w("")
    w(f"namespace BioLib.Imported.{module}")
    w("")
    w("open BioLib.Chemistry BioLib.Evidence")
    w("")
    w("/-- Species of the imported model, named by SBML id. -/")
    w("inductive Species")
    w("  " + " ".join("| " + lean_name(s) for s in species_ids))
    w("  deriving DecidableEq")
    w("")
    w(fintype("Species", species_ids))
    w("")
    w("/-- Reactions of the imported model, named by SBML id. -/")
    w("inductive Rxn")
    w("  " + " ".join("| " + lean_name(r) for r in rids))
    w("  deriving DecidableEq")
    w("")
    w(fintype("Rxn", rids))
    w("")
    w("/-- The stoichiometric network of the imported model. -/")
    w("def network : Network Species Rxn where")
    w("  reaction")
    for rid, lhs, rhs in reactions:
        w(f"    | .{lean_name(rid)} =>")
        w(f"      ⟨{coeff_fun(lhs, species_ids)},")
        w(f"       {coeff_fun(rhs, species_ids)}⟩")
    w("")
    w("/-- Provenance record. -/")
    w("def record : ModelRecord where")
    w(f"  id := {lean_string('BioLib.Imported.' + module)}")
    w('  version := "0.1.0"')
    w("  source := some")
    w(f"    {{ citation := {lean_string('SBML model ' + model_id + ' (' + model_name + '), file ' + file_name + ', sha256 ' + digest)}")
    w(f"      locator := {lean_string('listOfSpecies, listOfReactions')} }}")
    w("  assumptions :=")
    w('    [ { name := "stoichiometry only", kind := .modelling,')
    w('        statement := "kinetic laws, compartments, parameters, rules and events of the SBML model are not represented" } ]')
    w("  deviations :=")
    w('    [ "Each reversible SBML reaction is represented as a forward reaction and a reverse reaction." ]')
    w("")
    w(f"end BioLib.Imported.{module}")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
