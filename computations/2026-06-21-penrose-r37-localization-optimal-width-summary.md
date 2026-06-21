# Penrose R37 - optimal localization width for off-line curvature

Status: `[EXPERIMENTAL FINDING / CONJECTURE]`

Random path:

- Seed RandomNode: `Downstream filtering can erase resonance visible at upstream signaling nodes`.
- Step 1 topic rng `2`: `Stochastic resonance in weak-signal detection`.
- Step 4 NODE rng `1`: useful noise has a narrow optimum; more noise is not better.
- Standing target: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; target rng `23` -> `positivity/localization axis`.

NODE constraint:

The NODE validation showed a narrow stochastic-resonance optimum: detection score rose from `0` to a peak `25.05080` at noise `0.46`, then declined at larger noise.

Transfer:

R36 showed that broad downstream filters erase the off-line quartet curvature core. R37 tested the reverse rule: for noisy measurements of the target kernel

```text
C_a(tau)=2(a^2-tau^2)/(a^2+tau^2)^2,
```

there is a scale-matched Gaussian localization width. More smoothing is not better.

Main data:

For `a=0.10` and measurement noise `0.35 * raw_peak`, detection z-score peaked at Gaussian width `0.50a`:

```text
width/a: 0.05 0.08 0.12 0.18 0.25 0.35 0.50 0.75 1.00 1.50 2.00 3.00 4.00 6.00 8.00
z-score: 33.81 42.37 50.93 60.00 66.74 71.75 73.43 69.84 64.23 53.93 46.24 36.29 30.30 23.46 19.62
```

Step 11 monotonicity battery over `a=0.05,0.08,0.12,0.20` and noise ratios `0.2,0.35,0.6` found the same peak `width/a=0.50` in every row, with the sampled curve increasing on the left and decreasing on the right.

Interpretation:

The positivity/localization axis has a scale passport. If an off-line quartet has half-width `a=|beta-1/2|`, a Gaussian localizer that is much narrower wastes SNR on measurement noise, while a broader one washes the positive core into the negative wings. The matched width is approximately `a/2` for this detector family.

Files:

- `computations/2026-06-21-penrose-r37-node-narrow-resonance-optimum.py`
- `computations/2026-06-21-penrose-r37-localization-optimal-filter.py`
- `computations/2026-06-21-penrose-r37-step11-filter-unimodality.py`
