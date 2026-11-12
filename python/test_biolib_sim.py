"""Checks of the simulator's output against properties proved in Lean.

Run from the repository root after `lake build biolib-sim`:

    python3 python/test_biolib_sim.py
"""
import numpy as np

from biolib_sim import self_check, simulate


def main():
    data = simulate(species=20, samples=60, studies=2, depth=5000, seed=7, bias_sd=0.3)
    assert data.counts.shape == (60, 20)
    # Every sample has exactly `depth` reads, so relative abundances sum to one
    # (compare `BioLib.Sim.sum_relAbundance`).
    assert (data.counts.sum(axis=1) == 5000).all()
    assert np.allclose(data.relative_abundance().sum(axis=1), 1.0)
    assert set(np.unique(data.treated)) <= {0, 1}
    assert set(np.unique(data.study)) == {0, 1}

    # Same seed, same output; different seed, different output.
    again = simulate(species=20, samples=60, studies=2, depth=5000, seed=7, bias_sd=0.3)
    assert (again.counts == data.counts).all()
    other = simulate(species=20, samples=60, studies=2, depth=5000, seed=8, bias_sd=0.3)
    assert (other.counts != data.counts).any()

    # A species absent at the start stays absent (`eulerStep_glvRate_absent`):
    # with presence probability 0 every state is zero, so no reads are assigned.
    empty = simulate(species=5, samples=3, depth=100, presence=0.0)
    assert (empty.counts == 0).all() and (empty.total == 0).all()

    # With no inhibitor, treated and untreated samples follow the same model.
    # With one, total abundance drops in treated samples.
    dosed = simulate(species=20, samples=200, seed=3, dose=1.0)
    assert dosed.total[dosed.treated == 1].mean() < dosed.total[dosed.treated == 0].mean()

    # Floating point agrees with exact rational arithmetic on a small system.
    assert self_check(16) < 4.0

    print("python checks passed")


if __name__ == "__main__":
    main()
