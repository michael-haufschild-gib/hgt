# The square-root critical-line census: N₀(T) ≫ √T/(1+log T)²

- **ID:** HARDY-SQRT-CENSUS
- **Stage:** 3-formalized
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 94
- **STATUS:** MUST-615
- **Supersedes in strength:** `exists_twoSeventhRoot_le_xiPosCriticalZeroCount` (`T^{2/7}/(1+log T)⁹`).

## Theorems [L]

Module `formal/GaloisForLFunctions/RHTower/HardySquareRootCensus.lean` (wired, standard axioms).

- `exists_many_distinct_line_zeros_dyadic_sqrt`: at least `c√T/(1+log T)²` distinct ordinates in `(T, 2T]` carry critical-line zeros of `ζ`.
- `exists_sqrtRoot_le_xiPosCriticalZeroCount`: `N₀(T) ≥ c√T/(1+log T)²` for large `T`. The `_sub` form gives the dyadic difference.
- Reusable lemmas:
  - `integral_abs_hardyZ_eq_abs_integral` — constant sign on zero-free windows;
  - `exists_zeroWindows_of_firstMoment` — the first-moment window census;
  - `exists_le_integral_abs_hardyZ` — `∫_T^{2T}|Z| ≥ 3T/4`;
  - `exists_integral_hardyZ_sq_dyadic_le` — `∫Z² ≪ T(1+log T)²`, from the fourth moment by Cauchy–Schwarz.

## Mechanism

- **Windows.** Cut `[T,2T]` into `K ≍ √T` windows.
- **Zero-free windows are cheap.** On them `∫_W|Z| = |∫_W Z| ≤ ME`. Here `ME` is the corpus resonance-graded mean with cutoff `x = 16QT`, and `K·ME ≤ 3T/8`.
- **The first moment forces mass elsewhere.** It is `≥ 3T/4`, so the windows with zeros carry `≥ 3T/8`.
- **Count.** Cauchy–Schwarz with `(∫_W|Z|)² ≤ H∫_W Z²` and the global second moment gives `#windows ≫ K/(1+log T)²`.

The two-sevenths census needed a per-window fourth-moment Hölder gap `ME²·M4 < (T/8K)³`, which forces `K ≲ T^{2/7}`. The first-moment averaging needs only `K·ME ≲ T`, which allows `K ≍ √T`.

## Ceiling and next layer

- `√T` is the barrier of the dual edge in the window mean: `√x + HT/x` balances at `(HT)^{1/3}`.
- Going beyond needs the oscillatory reflected-edge bound, or the shifted second moment of short window integrals (Hardy–Littlewood's `∫|∫_t^{t+H}Z|² ≪ TH`). That would give `N₀ ≫ T/(1+log T)²` with this same census lemma.

## Plan for the next layers (cycle 95, paper)

1. **`T^{3/4}` census.** Needs a sharp window mean for the dual edge.
   - Use the τ-dependent weights `smoothAFEZetaDualWeight τ ((n+1)x)` with `x ≍ √T`.
   - Apply the first-derivative test with variable amplitude (`firstDerivTestOn` with `A'` from `exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale`). Alternatively, telescope the frozen cells of `HardyZFrozenDualEdgeCellBound`.
   - Then `ME = O(T^{1/4}log T + H T^{−1/4})`, `K ≍ T^{3/4}/log T`, and `N₀ ≫ T^{3/4}/log³T`.
2. **`T/log²T` census.**
   - Need `∫_T^{2T}|∫_t^{t+H}Z|² dt ≪ TH`.
   - Direct edge: block-frozen MVT. The coefficients are `a_n·g_n(t)` with `Σ|a_n g_n|² ≪ H`; the near-resonance band `|n−√(t/2π)| ≤ √t/H` contributes `≍ H`.
   - The dual edge is the mirror.
   - Then pick a grid offset `s` with `Σ_k|I(T+s+kH)|² ≤ CT`. Windows without zeros carry `≤ T√(C/H)`, so `N₀ ≫ T/(H log²T)`.
   - The Euler–Maclaurin length-`T` approximant does not work: its off-diagonal is `H²T log T`.

## Note (2026-10-01, loop cycle 102): superseded in strength

`Zeta23` (pinned dependency; transported in `R:LamzouriMontgomeryTaylorXiDensity`) already gives `N₀ˢ(T) ≥ (0.6725−ε)N(T)` unconditionally. The `√T` census stands as an independent elementary proof, but it is not a frontier result. The `T^{3/4}` and `T/log²T` plans of cycle 95 are retired.
