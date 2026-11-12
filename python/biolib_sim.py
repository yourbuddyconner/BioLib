"""Python wrapper around the `biolib-sim` executable.

The simulator itself is written in Lean (`BioLib/Sim`).  This module only runs
the compiled program and parses its CSV output, so that the results can be used
with numpy, pandas or a training pipeline.

Build the executable first:

    lake build biolib-sim

Example:

    from biolib_sim import simulate
    data = simulate(species=50, samples=200, studies=3, bias_sd=0.5, seed=1)
    data.counts      # (samples, species) integer array of read counts
    data.treated     # (samples,) 0/1 labels
    data.study       # (samples,) study index
    data.total       # (samples,) true total abundance, not recoverable from counts
"""
from __future__ import annotations

import csv
import io
import subprocess
from dataclasses import dataclass
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BINARY = REPO_ROOT / ".lake" / "build" / "bin" / "biolib-sim"

# Python keyword argument -> command-line flag.
_FLAGS = {
    "species": "--species",
    "samples": "--samples",
    "studies": "--studies",
    "depth": "--depth",
    "steps": "--steps",
    "dt": "--dt",
    "seed": "--seed",
    "treated_frac": "--treated-frac",
    "dose": "--dose",
    "sensitive_frac": "--sensitive-frac",
    "presence": "--presence",
    "connectance": "--connectance",
    "strength": "--strength",
    "capacity_sd": "--capacity-sd",
    "env_sd": "--env-sd",
    "bias_sd": "--bias-sd",
    "model": "--model",
    "beta": "--beta",
    "taylor_exponent": "--taylor-exponent",
    "sampling": "--sampling",
    "mad_sigma": "--mad-sigma",
}


@dataclass
class SimulatedData:
    """Output of one simulator run."""

    counts: np.ndarray  # (samples, species), int64 read counts
    treated: np.ndarray  # (samples,), 0 or 1
    study: np.ndarray  # (samples,), study index
    total: np.ndarray  # (samples,), true total absolute abundance
    params: dict  # the arguments the simulator was called with

    def relative_abundance(self) -> np.ndarray:
        """Observed relative abundance: counts divided by sequencing depth."""
        return self.counts / self.counts.sum(axis=1, keepdims=True)

    def to_frame(self):
        """Return a pandas DataFrame (requires pandas)."""
        import pandas as pd

        frame = pd.DataFrame(
            self.counts, columns=[f"sp{i}" for i in range(self.counts.shape[1])]
        )
        frame.insert(0, "total_abundance", self.total)
        frame.insert(0, "treated", self.treated)
        frame.insert(0, "study", self.study)
        return frame


def _format(value) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, bool):
        raise TypeError("simulator options are numbers, not booleans")
    if isinstance(value, int):
        if value < 0:
            raise ValueError("simulator options must be nonnegative")
        return str(value)
    value = float(value)
    if value != value or abs(value) == float("inf"):
        raise ValueError("simulator options must be finite")
    # The Lean argument parser reads plain decimals, not exponent notation.
    return f"{value:.12f}"


def simulate(binary: str | Path | None = None, **params) -> SimulatedData:
    """Run the Lean simulator and return its output as arrays.

    Keyword arguments are the simulator's options; see `biolib-sim --help`.
    Unspecified options take the simulator's defaults.
    """
    exe = Path(binary) if binary is not None else DEFAULT_BINARY
    if not exe.exists():
        raise FileNotFoundError(f"{exe} not found; run `lake build biolib-sim` first")
    args = [str(exe)]
    for key, value in params.items():
        if key not in _FLAGS:
            raise TypeError(f"unknown simulator option {key!r}; known: {sorted(_FLAGS)}")
        args += [_FLAGS[key], _format(value)]
    done = subprocess.run(args, capture_output=True, text=True)
    if done.returncode != 0:
        raise RuntimeError(f"biolib-sim failed: {done.stderr.strip()}")

    rows = list(csv.reader(io.StringIO(done.stdout)))
    header, body = rows[0], rows[1:]
    first_species = header.index("sp0")
    return SimulatedData(
        counts=np.array([r[first_species:] for r in body], dtype=np.int64).reshape(
            len(body), len(header) - first_species
        ),
        treated=np.array([r[header.index("treated")] for r in body], dtype=np.int64),
        study=np.array([r[header.index("study")] for r in body], dtype=np.int64),
        total=np.array([r[header.index("total_abundance")] for r in body], dtype=float),
        params=dict(params),
    )


def self_check(steps: int = 16, binary: str | Path | None = None) -> float:
    """Largest Float-vs-exact-rational difference, in units of machine epsilon."""
    exe = Path(binary) if binary is not None else DEFAULT_BINARY
    done = subprocess.run(
        [str(exe), "--selfcheck", str(steps)], capture_output=True, text=True, check=True
    )
    return float(done.stdout.split()[0])
