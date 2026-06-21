#!/usr/bin/env python3
import numpy as np


def make_network(rng, n=90, jurisdictions=3):
    jur = np.repeat(np.arange(jurisdictions), n // jurisdictions)
    rng.shuffle(jur)
    exposure = rng.gamma(1.4, 0.037, size=(n, n))
    np.fill_diagonal(exposure, 0.0)
    exposure *= rng.random((n, n)) < 0.10
    exposure /= np.maximum(1.0, exposure.sum(axis=1, keepdims=True) / 0.78)
    capital = rng.uniform(0.055, 0.115, size=n)
    return jur, exposure, capital


def cascade(jur, exposure, capital, recovery, delay_loss, seed):
    n = len(capital)
    equity = capital.copy()
    defaulted = np.zeros(n, dtype=bool)
    pending = np.zeros(n)
    equity[seed] = -1.0
    losses_by_step = []
    for _ in range(18):
        new_default = equity < 0.0
        shockers = np.flatnonzero(new_default & ~defaulted)
        if len(shockers) == 0 and np.all(pending <= 1e-12):
            break
        defaulted |= new_default
        current_loss = pending.copy()
        pending[:] = 0.0
        for i in shockers:
            for j in range(n):
                if exposure[j, i] <= 0.0:
                    continue
                loss = exposure[j, i] * (1.0 - recovery[jur[i], jur[j]])
                if jur[i] == jur[j]:
                    current_loss[j] += loss
                else:
                    pending[j] += loss * delay_loss[jur[i], jur[j]]
                    current_loss[j] += loss * (1.0 - delay_loss[jur[i], jur[j]])
        equity -= current_loss
        losses_by_step.append(float(current_loss.sum()))
    return int(defaulted.sum()), float(np.sum(capital - np.maximum(equity, 0.0))), losses_by_step


def summarize(label, recovery, delay_loss, reps=320):
    rng = np.random.default_rng(20260621)
    defaults = []
    losses = []
    front_loaded = []
    for _ in range(reps):
        jur, exposure, capital = make_network(rng)
        seed = int(rng.integers(0, len(jur)))
        d, loss, steps = cascade(jur, exposure, capital, recovery, delay_loss, seed)
        defaults.append(d)
        losses.append(loss)
        total = sum(steps) + 1e-12
        front_loaded.append(sum(steps[:2]) / total)
    print(
        f"{label:18s} {np.quantile(defaults,0.5):13.6f} {np.quantile(defaults,0.9):13.6f} "
        f"{np.quantile(losses,0.5):12.6f} {np.quantile(losses,0.9):12.6f} "
        f"{np.quantile(front_loaded,0.5):18.6f}"
    )


def main():
    uniform_recovery = np.ones((3, 3)) * 0.42
    uniform_delay = np.zeros((3, 3))
    fragmented_recovery = np.array(
        [
            [0.52, 0.18, 0.28],
            [0.24, 0.50, 0.14],
            [0.30, 0.20, 0.55],
        ]
    )
    fragmented_delay = np.array(
        [
            [0.00, 0.72, 0.35],
            [0.60, 0.00, 0.78],
            [0.40, 0.70, 0.00],
        ]
    )
    harsh_cross = np.ones((3, 3)) * 0.12
    np.fill_diagonal(harsh_cross, 0.55)
    harsh_delay = np.ones((3, 3)) * 0.80
    np.fill_diagonal(harsh_delay, 0.0)
    print("NODE: cross-border legal/resolution differences alter loss propagation")
    print("case defaults_q50 defaults_q90 loss_q50 loss_q90 front_loaded_loss_q50")
    summarize("uniform_rules", uniform_recovery, uniform_delay)
    summarize("fragmented_rules", fragmented_recovery, fragmented_delay)
    summarize("harsh_crossborder", harsh_cross, harsh_delay)


if __name__ == "__main__":
    main()
