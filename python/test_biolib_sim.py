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
    empty = simulate(model="glv", species=5, samples=3, depth=100, presence=0.0)
    assert (empty.counts == 0).all() and (empty.total == 0).all()

    # With no inhibitor, treated and untreated samples follow the same model.
    # With one, total abundance drops in treated samples.
    for model in ("slm", "glv"):
        dosed = simulate(model=model, species=20, samples=200, seed=3, dose=1.0)
        assert dosed.total[dosed.treated == 1].mean() < dosed.total[dosed.treated == 0].mean()

    # Stochastic logistic model: untreated abundances follow the gamma law, so the
    # squared coefficient of variation of each species is 1/beta (Taylor's law,
    # `BioLib.Papers.Grilli2020`).  Checked through sampling noise at high depth.
    slm = simulate(species=30, samples=4000, depth=200000, beta=2.0, mad_sigma=0.3,
                   treated_frac=0.0, sampling="poisson", seed=5)
    p = slm.counts / 200000
    assert abs(p.sum(axis=1).mean() - 1.0) < 0.02  # mean abundances sum to one
    cv2 = p.var(axis=0) / p.mean(axis=0) ** 2
    assert abs(np.median(cv2) - 0.5) < 0.05, np.median(cv2)

    # Floating point agrees with exact rational arithmetic on a small system.
    assert self_check(16) < 4.0

    print("python checks passed")


if __name__ == "__main__":
    main()
