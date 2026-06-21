#!/usr/bin/env python3
"""NODE test: boundary effects and domain geometry in anomalous diffusion.

NODE:
    Considering boundary effects and domain geometry in crowded or confined
    systems.

Constraint:
    An apparent anomalous exponent is interpretable only after the observation
    domain and boundary condition are fixed. The same microscopic Brownian step
    law can look normal, subdiffusive, or survival-biased depending on geometry.
"""

from __future__ import annotations

import numpy as np


SEED = 20260621
N_TRAJ = 9000
N_STEPS = 420
SIGMA_STEP = 1.0
FIT_TIMES = np.arange(8, N_STEPS + 1)


def fit_alpha(times: np.ndarray, msd: np.ndarray, lo: int, hi: int) -> float:
    mask = (times >= lo) & (times <= hi) & (msd > 1e-12)
    return float(np.polyfit(np.log(times[mask]), np.log(msd[mask]), 1)[0])


def unbounded(rng: np.random.Generator) -> np.ndarray:
    steps = rng.normal(0.0, SIGMA_STEP, size=(N_TRAJ, N_STEPS))
    return np.cumsum(steps, axis=1)


def reflecting(rng: np.random.Generator, half_width: float) -> np.ndarray:
    x = np.zeros(N_TRAJ, dtype=float)
    out = np.zeros((N_TRAJ, N_STEPS), dtype=float)
    for k in range(N_STEPS):
        x = x + rng.normal(0.0, SIGMA_STEP, size=N_TRAJ)
        over = x > half_width
        x[over] = 2.0 * half_width - x[over]
        under = x < -half_width
        x[under] = -2.0 * half_width - x[under]
        x = np.clip(x, -half_width, half_width)
        out[:, k] = x
    return out


def absorbing_conditional(rng: np.random.Generator, half_width: float) -> tuple[np.ndarray, np.ndarray]:
    x = np.zeros(N_TRAJ, dtype=float)
    alive = np.ones(N_TRAJ, dtype=bool)
    out = np.full((N_TRAJ, N_STEPS), np.nan, dtype=float)
    survival = np.zeros(N_STEPS, dtype=float)
    for k in range(N_STEPS):
        x[alive] = x[alive] + rng.normal(0.0, SIGMA_STEP, size=np.count_nonzero(alive))
        alive &= np.abs(x) <= half_width
        out[alive, k] = x[alive]
        survival[k] = float(np.mean(alive))
    return out, survival


def msd_from_paths(paths: np.ndarray) -> np.ndarray:
    return np.nanmean(paths * paths, axis=0)


def summarize(name: str, msd: np.ndarray, survival: np.ndarray | None = None) -> None:
    times = np.arange(1, len(msd) + 1)
    a_early = fit_alpha(times, msd, 8, 60)
    a_all = fit_alpha(times, msd, 8, N_STEPS)
    a_late = fit_alpha(times, msd, 160, N_STEPS)
    plateau_ratio = float(msd[-1] / max(msd[59], 1e-12))
    surv = 1.0 if survival is None else float(survival[-1])
    print(
        f"{name:22s} alpha_early={a_early:.4f} alpha_all={a_all:.4f} "
        f"alpha_late={a_late:.4f} msd60={msd[59]:.4f} msd_end={msd[-1]:.4f} "
        f"plateau_ratio={plateau_ratio:.4f} survival_end={surv:.4f}"
    )


def geometry_sweep(rng: np.random.Generator) -> None:
    print("\nGEOMETRY SIZE SWEEP")
    print("half_width reflect_alpha_all reflect_alpha_late reflect_plateau absorb_alpha_all absorb_survival")
    for half_width in [6.0, 9.0, 12.0, 18.0, 30.0, 60.0]:
        refl = reflecting(rng, half_width)
        refl_msd = msd_from_paths(refl)
        abs_paths, survival = absorbing_conditional(rng, half_width)
        abs_msd = msd_from_paths(abs_paths)
        print(
            f"{half_width:10.1f} "
            f"{fit_alpha(FIT_TIMES, refl_msd[7:], 8, N_STEPS):17.4f} "
            f"{fit_alpha(FIT_TIMES, refl_msd[7:], 160, N_STEPS):18.4f} "
            f"{float(refl_msd[-1]/max(refl_msd[59],1e-12)):15.4f} "
            f"{fit_alpha(FIT_TIMES, abs_msd[7:], 8, N_STEPS):16.4f} "
            f"{float(survival[-1]):15.4f}"
        )


def main() -> None:
    rng = np.random.default_rng(SEED)
    print("NODE: boundary/domain geometry changes apparent anomalous diffusion")
    print(f"seed={SEED} n_traj={N_TRAJ} n_steps={N_STEPS} sigma_step={SIGMA_STEP}")
    print("criterion: same microscopic step law should fit different exponents under different boundaries")

    summarize("unbounded", msd_from_paths(unbounded(rng)))
    summarize("reflecting_L9", msd_from_paths(reflecting(rng, 9.0)))
    abs_paths, survival = absorbing_conditional(rng, 9.0)
    summarize("absorbing_L9_cond", msd_from_paths(abs_paths), survival)
    summarize("reflecting_L30", msd_from_paths(reflecting(rng, 30.0)))
    abs_paths2, survival2 = absorbing_conditional(rng, 30.0)
    summarize("absorbing_L30_cond", msd_from_paths(abs_paths2), survival2)
    geometry_sweep(rng)


if __name__ == "__main__":
    main()
