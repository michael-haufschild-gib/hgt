#!/usr/bin/env python3
"""Out-of-sample check for feedback-locked prime flow spectra."""

from __future__ import annotations

import importlib.util
import pathlib
import sys

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-prime-flow-feedback-lockin.py")
spec = importlib.util.spec_from_file_location("prime_feedback", BASE)
mod = importlib.util.module_from_spec(spec)
sys.modules["prime_feedback"] = mod
spec.loader.exec_module(mod)


def train_test_mse(x: np.ndarray, y: np.ndarray, train_n: int) -> tuple[float, float]:
    a, b = np.polyfit(x[:train_n], y[:train_n], 1)
    fit = a * x + b
    scale = max(float(np.std(y)), 1e-12)
    train = float(np.mean(((fit[:train_n] - y[:train_n]) / scale) ** 2))
    test = float(np.mean(((fit[train_n:] - y[train_n:]) / scale) ** 2))
    return train, test


def main() -> None:
    n = 50
    logp = np.log(mod.first_primes(n))
    zeros = mod.zero_ordinates(n - 1)
    print("STEP12: out-of-sample kill gate for prime-built feedback spectra")
    print("sigma beta entropy lock train_mse test_mse spacing_mse test_over_train")
    for sigma in [0.3, 0.5, 0.8, 1.1]:
        for beta in [0.0, 1.0, 2.0, 4.0, 7.0, 10.0]:
            q, pi = mod.reversible_generator(logp, sigma=sigma, beta=beta, ell=0.85)
            eig = np.sort(-np.linalg.eigvals(q).real)
            eig = eig[eig > 1e-9][: n - 1]
            train, test = train_test_mse(eig, zeros[: len(eig)], train_n=18)
            spacing = mod.spacing_mse(eig, zeros[: len(eig)])
            lock = float(pi.max() / np.median(pi))
            print(
                f"{sigma:.1f} {beta:04.1f} {mod.entropy(pi):.3f} {lock:.2f} "
                f"{train:.3f} {test:.3f} {spacing:.3f} {test / max(train, 1e-12):.2f}"
            )
        print()


if __name__ == "__main__":
    main()
