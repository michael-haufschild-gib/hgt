# Penrose R34 - state-law abscissa passport

Status: `[EXPERIMENTAL FINDING / BRIDGE-CANDIDATE]`

Random path:

- Seed RandomNode: `The Griffiths region is bounded by the clean critical point and the disordered critical point, not just by the observed transition temperature`.
- Step 1 topic rng `13`: `Spin-glass analogies in neural population dynamics`.
- Step 4 NODE rng `3`: neural states are rarely binary spins; firing rates, timing, bursting, adaptation, and latent variables change the mapping.
- Standing target: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; target rng `15` -> `Abscissa of a.s. convergence`.

NODE constraint:

The state representation is load-bearing. In the NODE validation script, the same simulated neural population gave different participation dimensions and frustration fractions under binary spikes, smoothed rates, timing-since-spike, and adaptation variables.

Transfer:

For the random Euler observable

```text
L(sigma) = sum_p -log(1 - X_p p^-sigma),
```

the usual theorem uses `X_p` uniform on `U(1)`, so every nonzero power moment `E[X_p^k]` vanishes. Replacing the prime state law by binary signs or rate-like variables changes the deterministic drift even when the variance wall remains at `sigma=1/2`.

Main data:

- U(1)-phase log encoding: mean growth stays zero; variance growth is visible near `sigma=1/2`.
- Rademacher/binary log encoding: variance wall remains at `1/2`, but even powers create deterministic drift born at the same seam.
- Positive rate encoding: a nonzero first moment adds a separate mean wall at `sigma=1`.
- Root-of-unity battery: `q=2` has drift at the seam; `q>=3` moves the first deterministic moment below the variance wall, so the total wall stays `1/2`.

Stripped rule:

Let `k0` be the first positive integer with `E[X^k0] != 0` for the prime-state law in the full log Euler observable. The deterministic mean wall is `sigma = 1/k0`; the centered fluctuation wall is `sigma = 1/2`. The total convergence wall predicted by this state passport is

```text
max(1/2, 1/k0),
```

with continuous `U(1)` acting as `k0 = infinity`.

Promptability audit:

A generic transfer from neural state representation would predict that changing the prime-state law matters. The nontrivial content here is the moment-order classification: binary signs are not merely a coarser U(1); they create an even-power drift exactly at the variance seam, while `q>=3` root-state laws and continuous `U(1)` keep deterministic drift below the variance wall.

Interpretation:

The critical-line abscissa theorem is not just a variance theorem; it has a hidden state-law hypothesis. The seam `1/2` is robust for centered fluctuations, but the source-pure random Euler model needs enough phase moment cancellation to prevent a separate deterministic drift wall from contaminating the interpretation.

Files:

- `computations/2026-06-21-penrose-r34-node-neural-state-representation.py`
- `computations/2026-06-21-penrose-r34-abscissa-state-encoding-map.py`
- `computations/2026-06-21-penrose-r34-step11-moment-spectrum-abscissa.py`
- `computations/2026-06-21-penrose-r34-step12-state-law-battery.py`
