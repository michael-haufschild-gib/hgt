#!/usr/bin/env python3
"""
NODE test: Mean squared displacement can misclassify transport when
trajectory-level heterogeneity is ignored.

The constraint tested here is not a transport law. It is a classification
constraint: an ensemble MSD exponent is valid evidence about individual
transport only when the per-trajectory time-averaged MSD distribution is
also tight enough to self-average.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621
N_TRAJ = 7000
N_STEPS = 720
LAGS = np.array([1, 2, 4, 8, 16, 32, 64, 128])
TA_LAG = 32


def simulate_diffusion(rng: np.random.Generator, diffusivities: np.ndarray) -> np.ndarray:
    scales = np.sqrt(2.0 * diffusivities)[:, None]
    increments = rng.normal(0.0, 1.0, size=(diffusivities.size, N_STEPS)) * scales
    return np.cumsum(increments, axis=1)


def ensemble_msd(paths: np.ndarray, lags: np.ndarray) -> np.ndarray:
    values = []
    for lag in lags:
        disp = paths[:, lag:] - paths[:, :-lag]
        values.append(float(np.mean(disp * disp)))
    return np.array(values)


def ta_msd(paths: np.ndarray, lag: int) -> np.ndarray:
    disp = paths[:, lag:] - paths[:, :-lag]
    return np.mean(disp * disp, axis=1)


def fit_alpha(lags: np.ndarray, msd: np.ndarray) -> float:
    coeff = np.polyfit(np.log(lags), np.log(msd), 1)
    return float(coeff[0])


def summarize_model(name: str, diffusivities: np.ndarray, rng: np.random.Generator) -> dict[str, float | str]:
    paths = simulate_diffusion(rng, diffusivities)
    emsd = ensemble_msd(paths, LAGS)
    tam = ta_msd(paths, TA_LAG)
    alpha = fit_alpha(LAGS, emsd)
    eb = float(np.var(tam) / (np.mean(tam) ** 2))
    q10, q50, q90 = np.quantile(tam, [0.10, 0.50, 0.90])
    ensemble_d = float(emsd[LAGS == TA_LAG][0] / (2.0 * TA_LAG))
    indiv_d_hat = tam / (2.0 * TA_LAG)
    outside_factor2 = float(np.mean((indiv_d_hat < ensemble_d / 2.0) | (indiv_d_hat > 2.0 * ensemble_d)))
    msd_label = "normal" if 0.90 <= alpha <= 1.10 else "anomalous"
    heterogeneity_flag = eb > 0.35 or (q90 / max(q10, 1e-12)) > 4.0 or outside_factor2 > 0.25
    return {
        "name": name,
        "mean_D": float(np.mean(diffusivities)),
        "alpha": alpha,
        "emsd_lag32": float(emsd[LAGS == TA_LAG][0]),
        "ta_mean": float(np.mean(tam)),
        "ta_median": float(q50),
        "q90_q10": float(q90 / max(q10, 1e-12)),
        "eb": eb,
        "outside_factor2": outside_factor2,
        "msd_label": msd_label,
        "heterogeneity_flag": "yes" if heterogeneity_flag else "no",
        "msd_only_misclassifies": "yes" if msd_label == "normal" and heterogeneity_flag else "no",
    }


def lognormal_diffusivities(rng: np.random.Generator, sigma: float) -> np.ndarray:
    raw = rng.lognormal(mean=-0.5 * sigma * sigma, sigma=sigma, size=N_TRAJ)
    return raw / np.mean(raw)


def two_population_diffusivities() -> np.ndarray:
    slow = np.full(int(N_TRAJ * 0.8), 0.10)
    fast = np.full(N_TRAJ - slow.size, 4.60)
    return np.concatenate([slow, fast])


def print_summary(summary: dict[str, float | str]) -> None:
    print(
        "MODEL {name}: mean_D={mean_D:.4f} alpha={alpha:.4f} "
        "emsd32={emsd_lag32:.4f} ta_mean={ta_mean:.4f} ta_median={ta_median:.4f} "
        "q90/q10={q90_q10:.4f} EB={eb:.4f} outside_factor2={outside_factor2:.4f} "
        "msd_label={msd_label} heterogeneity_flag={heterogeneity_flag} "
        "msd_only_misclassifies={msd_only_misclassifies}".format(**summary)
    )


def main() -> None:
    rng = np.random.default_rng(SEED)
    print("NODE: ensemble MSD classifier versus trajectory-level heterogeneity")
    print(f"seed={SEED} n_traj={N_TRAJ} n_steps={N_STEPS} lags={LAGS.tolist()} ta_lag={TA_LAG}")
    print("constraint: normal ensemble MSD is insufficient unless time-averaged MSD self-averages")

    models = [
        ("homogeneous_D1", np.ones(N_TRAJ)),
        ("two_population_same_meanD", two_population_diffusivities()),
        ("lognormal_sigma1_same_meanD", lognormal_diffusivities(rng, 1.0)),
    ]

    print("\nexistence/absence test")
    for name, diffusivities in models:
        print_summary(summarize_model(name, diffusivities, rng))

    print("\ndriving-force sweep: diffusivity heterogeneity sigma")
    for sigma in [0.0, 0.25, 0.50, 0.75, 1.00, 1.25, 1.50, 2.00]:
        diffusivities = lognormal_diffusivities(rng, sigma)
        summary = summarize_model(f"lognormal_sigma_{sigma:.2f}", diffusivities, rng)
        print(
            "SIGMA {sigma:.2f}: alpha={alpha:.4f} q90/q10={q90_q10:.4f} "
            "EB={eb:.4f} outside_factor2={outside_factor2:.4f} "
            "misclassifies={msd_only_misclassifies}".format(sigma=sigma, **summary)
        )

    print("\ncriterion")
    print("If alpha remains near 1 while EB/q90-q10/outside-factor2 grow, MSD-only transport classification fails.")


if __name__ == "__main__":
    main()
