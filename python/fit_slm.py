"""Estimate the parameters of the stochastic logistic model from a count table.

The model (Grilli 2020, `BioLib/Papers/Grilli2020.lean`) as used by the
simulator has four parameters for cross-sectional data:

  beta, taylor_exponent   gamma shape of abundance fluctuations: a species of
                          mean abundance m has shape beta * (m / 1e-3)^(2 - z).
                          The paper's law is z = 2 (one shape for all species).
  mad_sigma               standard deviation of log mean abundance across species
  species                 number of species, including those never observed

Estimation uses the sampling model of the paper (Eq. 7: Poisson counts at
depth N given abundance) and makes stated choices where the paper's details
are in Supplementary Notes that were not consulted.

* Shape.  E[n] = N x and E[n (n - 1)] = N^2 E[x^2], so the mean and variance
  of abundance are recovered from factorial moments of the counts.  Taylor's
  law, variance = a * mean^z, is fitted by least squares on logarithms over
  species with mean abundance above `min_abundance`.  (Choices: the threshold
  and least squares.)  With `fix_exponent=2.0` the paper's law is imposed.
* Mean abundance distribution.  Summed over T samples, the reads of a species
  with mean abundance m are negative binomial with shape T * beta(m) and mean
  T N m.  With m lognormal(mu, sigma), the distribution of a species' total
  reads is a mixture, and (mu, sigma) are fitted by maximum likelihood to the
  totals of observed species, conditional on the total being at least one.
  This uses every observed species and needs no abundance cutoff.
* Species.  Observed species divided by the fitted probability of being observed.

`implied_total_abundance` is species * exp(mu + sigma^2 / 2).  The model's
mean abundances should sum to one, so values far from one indicate misfit.
All samples must have the same depth (rarefy first).
"""
from __future__ import annotations

import numpy as np
from scipy import optimize, stats

REF_ABUNDANCE = 1e-3  # must equal `betaRefAbundance` in BioLib/Sim/Run.lean


def fit_slm(counts: np.ndarray, min_abundance: float = 1e-4, fix_exponent=None) -> dict:
    depth = counts.sum(axis=1)
    assert (depth == depth[0]).all(), "rarefy to a common depth first"
    N, T = float(depth[0]), len(counts)
    mean = counts.mean(axis=0) / N
    var = (counts * (counts - 1)).mean(axis=0) / N**2 - mean**2
    use = (mean > min_abundance) & (var > 0)
    log_m, log_v = np.log(mean[use]), np.log(var[use])
    if fix_exponent is None:
        z, log_a = np.polyfit(log_m, log_v, 1)
    else:
        z, log_a = float(fix_exponent), float(np.mean(log_v - fix_exponent * log_m))

    def shape(m):
        return m ** (2.0 - z) / np.exp(log_a)

    totals = counts.sum(axis=0)
    totals = totals[totals > 0]
    values, multiplicity = np.unique(totals, return_counts=True)

    def mixture(mu, sigma):
        """Log-probabilities of the observed totals, and of a total of zero."""
        eta = np.linspace(mu - 8 * sigma, min(0.0, mu + 8 * sigma), 800)
        weight = stats.norm.pdf(eta, mu, sigma)
        weight /= weight.sum()
        m = np.exp(eta)
        r = T * shape(m)
        p = r / (r + T * N * m)
        pmf = stats.nbinom.pmf(values[:, None], r[None, :], p[None, :]) @ weight
        zero = float(stats.nbinom.pmf(0, r, p) @ weight)
        return np.log(np.maximum(pmf, 1e-300)), zero

    def negative_log_likelihood(theta):
        mu, sigma = theta[0], np.exp(theta[1])
        log_pmf, zero = mixture(mu, sigma)
        return -(multiplicity * (log_pmf - np.log1p(-zero))).sum()

    start = [np.log(mean[mean > 0]).mean(), np.log(np.log(mean[mean > 0]).std())]
    best = optimize.minimize(negative_log_likelihood, start, method="Nelder-Mead",
                             options={"xatol": 1e-4, "fatol": 1e-6, "maxiter": 600})
    mu, sigma = float(best.x[0]), float(np.exp(best.x[1]))
    _, zero = mixture(mu, sigma)
    species = int(round(len(totals) / (1.0 - zero)))
    return {
        "beta": float(shape(REF_ABUNDANCE)),
        "taylor_exponent": float(z),
        "mad_sigma": sigma,
        "species": species,
        "mad_mu": mu,
        "implied_total_abundance": float(species * np.exp(mu + sigma**2 / 2)),
        "species_observed": int(len(totals)),
        "species_used_for_shape": int(use.sum()),
    }


SIMULATOR_KEYS = ("beta", "taylor_exponent", "mad_sigma", "species")
