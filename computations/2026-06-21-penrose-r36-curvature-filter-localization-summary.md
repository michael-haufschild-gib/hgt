# Penrose R36 - downstream filtering and the positivity/localization axis

Status: `[EXPERIMENTAL FINDING / CONJECTURE]`

Random path:

- Seed RandomNode: `The Parisi order parameter is a full function q(x), not a single Edwards-Anderson parameter`.
- Step 1 topic rng `7`: `Stochastic resonance in disordered biochemical signaling`.
- Step 4 NODE rng `12`: downstream filtering can erase resonance visible at upstream signaling nodes.
- Standing target: file rng `2` -> `docs/consolidated/01-landscape-and-geometry.md`; target rng `23` -> `positivity/localization axis`.

NODE constraint:

An upstream threshold event stream can show a resonance-like peak while a many-period downstream low-pass readout suppresses or shifts it. The NODE validation found upstream SNR peaking around noise `0.48` (`24.42398`) while the downstream broad-filter SNR had already collapsed to `2.71110`.

Transfer:

The target's off-line quartet curvature contribution is

```text
C_a(tau) = 2(a^2 - tau^2)/(a^2 + tau^2)^2.
```

This is a localized positive core with negative wings and zero whole-line signed area. Broad positive downstream filters erase the positive core; the signal is not a scalar weld/constraint average.

Main data:

- For Gaussian filter width `8a`, the centered filtered peak was only `0.015929` of the raw peak, independent of `a` across `0.05, 0.08, 0.12, 0.20`.
- For width `4a`, the ratio was `0.046795`; for width `2a`, `0.140455`.
- Reversing the test, a centered sign-changing matched filter recovered the off-line core and kept a purely negative on-line curvature model negative at the center.

Interpretation:

The positivity/localization axis is a matched-localization problem. An off-line zero-pair can be invisible to broad downstream readouts because its curvature kernel cancels at large scale. A faithful RH detector must preserve the sign-changing local curvature profile, not only the constraint/weld average.

Files:

- `computations/2026-06-21-penrose-r36-node-downstream-filtering.py`
- `computations/2026-06-21-penrose-r36-curvature-filter-dependency.py`
- `computations/2026-06-21-penrose-r36-step11-reverse-filter.py`
