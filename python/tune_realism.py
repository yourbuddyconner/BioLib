"""Grid search of simulator options against a reference data set.

    python3 python/tune_realism.py

Scores each option set by the mean squared relative error of its summary
statistics against the reference, and prints the sets from best to worst.
This is a coarse fit of a few parameters to a dozen statistics; it shows which
statistics the model can and cannot reach, and is not a statistical estimate.
"""
import itertools
import json
import sys

from realism import REF, compare

REFERENCE = "Yatsunenko adults"
KEYS = [
    "richness, mean", "richness, CV", "Shannon, mean", "Shannon, sd",
    "top taxon share, median", "zero fraction", "taxa with prevalence < 10%",
    "log10 mean abundance, sd", "Taylor exponent", "CV of common taxa, median",
    "prevalence-abundance Spearman", "Bray-Curtis, mean",
]


def score(stats: dict) -> float:
    ref, sim = stats[REFERENCE], stats["Simulated (untreated)"]
    errs = [((sim[k] - ref[k]) / ref[k]) ** 2 for k in KEYS]
    return sum(e if e == e else 4.0 for e in errs) / len(errs)  # NaN counts as a large miss


def main():
    grid = {
        "presence": [0.2, 0.3, 0.45],
        "capacity_sd": [2.0, 2.5, 3.0],
        "env_sd": [0.6, 0.8, 1.0],
    }
    if len(sys.argv) > 1:
        grid = json.loads(sys.argv[1])
    base = {"species": 3000, "samples": 80, "depth": 5000, "seed": 1}
    results = []
    for values in itertools.product(*grid.values()):
        params = dict(base, **dict(zip(grid, values)))
        stats = compare(params, quiet=True)
        results.append((score(stats), dict(zip(grid, values)), stats["Simulated (untreated)"]))
        print(f"{results[-1][0]:.4f} {results[-1][1]}", flush=True)
    results.sort(key=lambda r: r[0])
    (REF / "tune_results.json").write_text(json.dumps(results, indent=1))
    print("\nbest:")
    for s, p, _ in results[:5]:
        print(f"  {s:.4f} {p}")
    best = results[0][2]
    ref = json.loads((REF / "stats_depth5000.json").read_text())[REFERENCE]
    print(f"\n{'statistic':<32}{'reference':>12}{'best sim':>12}")
    for k in KEYS:
        print(f"{k:<32}{ref[k]:>12.3f}{best[k]:>12.3f}")


if __name__ == "__main__":
    main()
