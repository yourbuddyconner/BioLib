"""Compare simulated communities with real 16S data on summary statistics.

All statistics are computed on count tables rarefied to a common depth, with
taxa that are absent from every retained sample removed.  Run from the
repository root:

    scripts/fetch_reference.sh          # once
    lake build biolib-sim
    python3 python/realism.py --held-out     # fit the stochastic logistic model on
                                             # half of each cohort, compare with the rest
    python3 python/realism.py [simulator options, e.g. --species 300]

The statistics are standard community-ecology summaries.  Agreement on them is
necessary for realism, not sufficient: they say nothing about which taxa
co-occur, about phylogeny, or about response to perturbation.
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

import numpy as np

from biolib_sim import simulate

ROOT = Path(__file__).resolve().parent.parent
REF = ROOT / "data" / "reference"
DEPTH = 5000


def load_otu_table(path: Path):
    """Read a QIIME-style OTU table (taxa in rows). Returns (sample ids, samples x taxa counts)."""
    with open(path) as fh:
        header = fh.readline().rstrip("\n").split("\t")[1:]
        rows = [line.rstrip("\n").split("\t")[1:] for line in fh if not line.startswith("#")]
    return header, np.array(rows, dtype=float).astype(np.int64).T


def load_mapping(path: Path):
    with open(path) as fh:
        return {row["#SampleID"]: row for row in csv.DictReader(fh, delimiter="\t")}


def rarefy(counts: np.ndarray, depth: int, rng) -> np.ndarray:
    """Subsample each sample to `depth` reads without replacement; drop shallower samples."""
    keep = counts.sum(axis=1) >= depth
    out = np.zeros((int(keep.sum()), counts.shape[1]), dtype=np.int64)
    for k, row in enumerate(counts[keep]):
        out[k] = rng.multivariate_hypergeometric(row, depth)
    return out[:, out.sum(axis=0) > 0]


def spearman(a, b) -> float:
    ra, rb = np.argsort(np.argsort(a)), np.argsort(np.argsort(b))
    return float(np.corrcoef(ra, rb)[0, 1])


def statistics(counts: np.ndarray) -> dict:
    """Summary statistics of a rarefied samples x taxa count table."""
    n_samples, n_taxa = counts.shape
    p = counts / counts.sum(axis=1, keepdims=True)
    present = counts > 0
    richness = present.sum(axis=1)
    with np.errstate(divide="ignore", invalid="ignore"):
        shannon = -np.where(p > 0, p * np.log(p), 0.0).sum(axis=1)
    prevalence = present.mean(axis=0)
    mean, var = p.mean(axis=0), p.var(axis=0)
    ok = (mean > 0) & (var > 0)
    taylor = np.polyfit(np.log(mean[ok]), np.log(var[ok]), 1)[0]
    common = prevalence >= 0.5
    cv = np.sqrt(var[common]) / mean[common] if common.any() else np.array([np.nan])
    # Bray-Curtis dissimilarity on relative abundances, over random sample pairs.
    rng = np.random.default_rng(0)
    i, j = rng.integers(0, n_samples, 2000), rng.integers(0, n_samples, 2000)
    pairs = i != j
    bray = 0.5 * np.abs(p[i[pairs]] - p[j[pairs]]).sum(axis=1)
    return {
        "samples": n_samples,
        "taxa observed": n_taxa,
        "richness, mean": richness.mean(),
        "richness, CV": richness.std() / richness.mean(),
        "Shannon, mean": shannon.mean(),
        "Shannon, sd": shannon.std(),
        "top taxon share, median": np.median(p.max(axis=1)),
        "zero fraction": 1.0 - present.mean(),
        "taxa with prevalence < 10%": (prevalence < 0.1).mean(),
        "taxa with prevalence > 90%": (prevalence > 0.9).mean(),
        "log10 mean abundance, sd": np.log10(mean[mean > 0]).std(),
        "Taylor exponent": taylor,
        "CV of common taxa, median": float(np.median(cv)),
        "prevalence-abundance Spearman": spearman(prevalence, mean),
        "Bray-Curtis, mean": bray.mean(),
    }


def reference_tables(rng) -> dict:
    tables = {}
    ids, counts = load_otu_table(REF / "yatsunenko" / "otutable.txt")
    meta = load_mapping(REF / "yatsunenko" / "mapping-orig.txt")

    def adult(sample, country=None):
        row = meta.get(sample)
        if row is None:
            return False
        try:
            age = float(row["AGE"])
        except ValueError:
            return False
        unit = row.get("AGE_UNIT", "years").lower()
        if not unit.startswith("year") or age < 18:
            return False
        return country is None or country in row["COUNTRY"]

    mask = np.array([adult(s) for s in ids])
    tables["Yatsunenko adults"] = rarefy(counts[mask], DEPTH, rng)
    mask = np.array([adult(s, "United States") for s in ids])
    tables["Yatsunenko US adults"] = rarefy(counts[mask], DEPTH, rng)
    ids, counts = load_otu_table(REF / "gevers" / "otutable.txt")
    tables["Gevers (all)"] = rarefy(counts, DEPTH, rng)
    return tables


def parse_sim_args(argv):
    params = {"species": 200, "samples": 150, "depth": DEPTH, "seed": 1}
    it = iter(argv)
    for flag in it:
        key = flag.lstrip("-").replace("-", "_")
        value = next(it)
        params[key] = float(value) if "." in value else int(value)
    return params


def reference_table(name: str) -> np.ndarray:
    """Unrarefied counts (samples x taxa) of one reference cohort."""
    if name == "gevers":
        return load_otu_table(REF / "gevers" / "otutable.txt")[1]
    ids, counts = load_otu_table(REF / "yatsunenko" / "otutable.txt")
    meta = load_mapping(REF / "yatsunenko" / "mapping-orig.txt")

    def keep(sample):
        row = meta.get(sample)
        try:
            age = float(row["AGE"]) if row else -1.0
        except ValueError:
            return False
        if row is None or age < 18 or not row.get("AGE_UNIT", "years").lower().startswith("year"):
            return False
        return name == "yatsunenko_adults" or "United States" in row["COUNTRY"]

    return counts[np.array([keep(s) for s in ids])]


def held_out_comparison(name: str, seed: int = 0) -> None:
    """Fit the stochastic logistic model on half of a cohort and compare its
    predictions with the other half.

    The fit uses per-species moments and total read counts only.  The statistics
    in the table are predictions.  The column "half-half" shows how far two
    halves of the real data differ from each other, which is the best agreement
    any model could reach.  Two fits are shown: Taylor's exponent fixed at 2 as
    in the paper, and estimated from the data.
    """
    from fit_slm import SIMULATOR_KEYS, fit_slm

    rng = np.random.default_rng(seed)
    counts = rarefy(reference_table(name), DEPTH, rng)
    order = rng.permutation(len(counts))
    train, test = counts[order[: len(order) // 2]], counts[order[len(order) // 2:]]
    cols = {
        "held-out half": statistics(test[:, test.sum(axis=0) > 0]),
        "train half": statistics(train[:, train.sum(axis=0) > 0]),
    }
    print(f"\n== {name}: {len(train)} samples to fit, {len(test)} held out, depth {DEPTH}")
    for label, fixed in (("sim, z=2", 2.0), ("sim, z fitted", None)):
        fit = fit_slm(train, fix_exponent=fixed)
        params = {k: fit[k] for k in SIMULATOR_KEYS}
        sim = simulate(model="slm", samples=len(test), depth=DEPTH, treated_frac=0.0,
                       seed=seed + 1, **params)
        cols[label] = statistics(sim.counts[:, sim.counts.sum(axis=0) > 0])
        print(f"fit ({label}): " + ", ".join(f"{k}={v:.4g}" for k, v in params.items()))
    width = max(len(k) for k in cols["train half"])
    ref = cols["held-out half"]
    print(" " * width + f"{'held-out':>10}{'half-half':>11}" +
          "".join(f"{n:>15}{'error':>8}" for n in list(cols)[2:]))
    for key in ref:
        line = f"{key:<{width}}{ref[key]:>10.3f}{(cols['train half'][key] - ref[key]) / ref[key]:>+11.0%}"
        for n in list(cols)[2:]:
            line += f"{cols[n][key]:>15.3f}{(cols[n][key] - ref[key]) / ref[key]:>+8.0%}"
        print(line)


def reference_statistics() -> dict:
    """Statistics of the reference tables, cached in data/reference/stats.json."""
    import json

    cache = REF / f"stats_depth{DEPTH}.json"
    if cache.exists():
        return json.loads(cache.read_text())
    stats = {n: statistics(t) for n, t in reference_tables(np.random.default_rng(0)).items()}
    stats = {n: {k: float(v) for k, v in d.items()} for n, d in stats.items()}
    cache.write_text(json.dumps(stats, indent=1))
    return stats


def compare(params: dict, quiet: bool = False) -> dict:
    """Run the simulator and return statistics for the references and the simulation."""
    stats = reference_statistics()
    sim = simulate(**params)
    untreated = sim.counts[sim.treated == 0]
    untreated = untreated[untreated.sum(axis=1) > 0]
    stats["Simulated (untreated)"] = statistics(untreated[:, untreated.sum(axis=0) > 0])
    if not quiet:
        names = list(stats)
        width = max(len(k) for k in stats[names[0]])
        print(" " * width + "".join(f"{n:>24}" for n in names))
        for key in stats[names[0]]:
            cells = "".join(
                f"{stats[n][key]:>24.0f}" if key in ("samples", "taxa observed")
                else f"{stats[n][key]:>24.3f}"
                for n in names
            )
            print(f"{key:<{width}}{cells}")
        print(f"\nsimulator options: {params}")
    return stats


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--held-out":
        for name in sys.argv[2:] or ["yatsunenko_us_adults", "yatsunenko_adults", "gevers"]:
            held_out_comparison(name)
    else:
        compare(parse_sim_args(sys.argv[1:]))


if __name__ == "__main__":
    main()
