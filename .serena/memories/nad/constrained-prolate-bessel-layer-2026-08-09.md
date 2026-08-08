# Bessel + passage layer for the constrained-prolate card (2026-08-09)

Card: `docs/drafts/pipeline/2-fully-proven/nad/constrained-prolate-continuous-polar-charge-law.md`.
All modules wired into their umbrellas, all axiom-clean, both umbrellas build green.

## What the corpus already owned (do not rebuild)

- `RHTower/BesselJZeroEnvelope.lean` — `besselJ0` via `(1/pi) int_0^pi cos(u sin θ)dθ`,
  `besselJ0_eq_two_div_pi_mul`, `besselPhase` + derivatives, the two van der Corput blocks with
  amplitude `1`, `abs_besselJ0_le_one`, and
  `abs_besselJ0_le_envelope : |J_0(u)| <= 72 sqrt 2 / sqrt u` for `u >= 1`.
- `RHTower/BesselJZeroODE.lean` — `besselJ0Deriv`, `besselJ0SecondDeriv`, differentiation under the
  integral, `integral_sin_mul_sin_eq`, `besselJ0_ode`.
- `RHTower/VanDerCorput.lean` — `firstDerivTest`, `secondDerivTest`, general C¹ amplitude, both
  requiring `phi'' >= 0`.
- `HTGeometry/CompactIntervalL2Pairing.lean` — `IntervalL2`, `inner_toIntervalL2` (pairing = explicit
  integral).  `RHTower/CCMGalerkinDiagonalTransfer.tendstoUniformlyOn_inner_of_tendsto`.
- mathlib has **no** Bessel functions at all.

## What I built

- `RHTower/BesselJOneRecurrence.lean` — `besselJ1 := -besselJ0Deriv`, `besselJ1_zero`,
  `besselJ1_eq_mul`, **`hasDerivAt_mul_besselJ1`** (`(u J_1)' = u J_0`, every real `u`),
  `hasDerivAt_mul_besselJ1_scaled`, `abs_besselJ1_le` (`|J_1(u)| <= |u|/2`).
- `RHTower/BesselJOneEnvelope.lean` — `besselAmp` + budget, `integral_besselAmp_eq_neg_im`,
  `besselJ1_eq_two_div_pi_mul`, the two blocks for the nonconstant amplitude,
  **`abs_besselJ1_le_envelope`**, `abs_besselJ1_le_min` = the card's `(44)`.
- `RHTower/BesselWeightedPrimitive.lean` — `continuous_besselJ0/J1`,
  **`abs_besselJ1_le_sqrt`** and **`abs_besselJ0_le_sqrt`** (`C/sqrt u` at *every* `u > 0`),
  `abs_mul_besselJ1_scaled_le`,
  **`abs_integral_mul_besselJ0_le`** = `(45)` (`<= 648 M / (c sqrt c)`, `0<=R<=2`, uniform in `R`),
  **`integral_abs_mul_besselJ0_le`** = `(46)` (`<= 288 M / sqrt c`).
- `RHTower/VanDerCorputIBP.lean` — the `(50)` mechanism, no monotone-phase hypothesis:
  `norm_integral_cexp_le_of_antiderivative`, `norm_antiderivative_le`,
  `norm_integral_cexp_le_of_frequency_lower_bound`.
- `HTGeometry/L2PairingLimit.lean` — the two passage steps of `(11)`:
  `norm_inner_le_of_tendsto`, `norm_inner_tsum_le`, `norm_inner_le_tsum_of_tendsto`.

## Mathematical findings

1. The card's `(45)`/`(46)` proofs split at `r = c^(-1)` (amplitude regime vs decay regime).
   **The split is unnecessary.**  `|J_1(u)| <= C/sqrt u` and `|J_0(u)| <= C/sqrt u` hold at every
   `u > 0`, because below `u = 1` the right side is already `>= C`.  One integration by parts on all
   of `[0,R]` suffices and the origin boundary term vanishes since `r J_1(cr)` does.
2. Every pre-existing van der Corput test in the corpus assumes `phi'' >= 0`.  The card's `(49)`
   gives only bounded variation of `1/xi'`, so none applies to `(50)`.

## Still open on this branch

Dunster's exterior expansion `(48)` (the `a_(eps,n,c)` amplitudes), then `(47)`, `(50)`, `(51)`.
Also the exterior estimate `(16)` that supplies the `k`-channel majorant for `(11)`.

## Traps

- `Real.pi_lt_315` does not exist; use `Real.pi_le_four`.
- `Complex.ofReal_mul_im` does not exist; use `Complex.mul_im` + `Complex.ofReal_re/im`.
- Bare `simp` on `(↑(Real.sin θ)).re` rewrites via `Complex.ofReal_sin` and leaves junk; use `rw`.
- `le_or_lt` is `le_or_gt` here.
- `ContinuousOn.intervalIntegrable` wants `uIcc`; do not `▸` to `Icc` first.
- `lake env lean` reads imports' **oleans**: after appending to a module, `lake build` it before a
  dependent file will see the new declaration.
- Several `HTGeometry/*Bures*` and `RHTower/*Coalescing*` modules are unreachable from the umbrellas
  **and do not compile** — they are other agents' in-progress work.  Do not wire them in; the
  umbrella build goes red.
