# Square-Root Threshold: frontier (SRT-4, SRT-5)

- **ID:** srt-frontier
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the proved items; CONJECTURE for the open targets
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md §5
- **Statement:** Locate, at height `T` and prime length `X = e^{2a}`, the information in localized
  Weil forms that makes a zero of depth `δ` visible, and prove the unconditional ranges.

## Goal
Map the plane (height `T`, prime length `X`, height-window length `ℓ`) into regions where
positivity of localized Weil forms of `ζ` is (a) proved unconditionally, (b) equivalent to a
zero-free region of a given depth, or (c) RH-strength.

## Gates
- [x] 0 → 1  in-progress: well-posed; SRT-1 to SRT-3 proved in Lean
- [ ] 1 → 2  fully-proven: complete paper proofs of the frontier items below
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Proved (Lean, unconditional, standard axioms only)
- SRT-1 `isolatedPairConfig_weil_nonneg_iff`: exact visibility law; depth-`δ` pair visible at
  `X ≈ (4δL)^{1/δ}`.
- SRT-2 `re_windowedW_nonneg_of_aperture_nonneg`, `exists_offLine_lattice_windowed_nonneg`: window
  averages at resolution `r` see only aperture-`r` positivity; off-line configurations pass them.
- SRT-3 `windowedW_eq_integral_heightShift`, `zetaZeroConfig_re_W_nonneg_of_small_aperture`
  (aperture `e^{−50}`), `re_integral_heightShift_zetaZeroConfig_nonneg`: windows of length
  `≳ e^{50}` give nonnegative height averages for `ζ` at every aperture.
- SRT-5a `exists_zetaZeroConfig_re_W_heightShift_nonneg`, `zetaZeroConfig_re_W_heightShift_ge`:
  for a fixed profile, single-height positivity holds for `X ≲ (log T/68)²`. This range matches
  the visibility range of depth-`½` zeros (`X ≈ 4L²`).

- SRT-4a `integral_pairTransform_mul_normSq_expSum`, `integral_normSq_mul_normSq_dirichletSum`
  (module `WindowedMeanValueDiagonalLaw`): exact windowed mean value, diagonal for `2rX ≤ 1`.
- SRT-4b `zetaZeroConfig_W_heightShift_eq_sub`, `integral_windowed_sq_deviation_eq`,
  `exists_primeVariance_le`, `lintegral_bad_heights_le_of_height` (module
  `ZetaLocalizedFormWindowedVarianceLaw`): exact variance law for `ζ` below the threshold. The
  proportion of negative heights is `O((log X/log T)²)`.

- SRT-5b′ `re_W_modulatedTest_le_of_depthGap`, `zeta_weil_positive_forces_deep_companion`
  (module `DepthGapVisibilityLaw`): a zero is visible once `2(δ − δ')a ≳ log(A₀ log γ₀)`, where
  `δ'` bounds the depth of its neighbours. Weil positivity forces deep companions.

- SRT-4c (module `WindowedOffDiagonalBeyondThreshold`):
  * `integral_pairTransform_mul_normSq_expSum_eq_diag_add` — exact diagonal/off-diagonal split;
  * `integral_normSq_mul_normSq_expSum_le`, `card_close_log_le`, `integral_windowed_sq_deviation_le`
    — the windowed mean value bound `1 + X(e^{2r} − e^{−2r})` at every length;
  * `le_integral_normSq_mul_normSq_expSum_of_nonneg` — sharpness for aligned phases;
  * `integral_pairTransform_mul_integral_windowed_eq` — height averages give prime-pair correlations.
- SRT-5c (module `PrimeTailCouplingCriterion`):
  * `riemannHypothesis_iff_primePolynomial_le_archPart` — the coupled criterion;
  * `exists_archPart_zero_lt_primePolynomial`, `re_primePolynomial_zero_neg` — the coupling is
    necessary, and the primes must cancel the pole;
  * `primePolynomial_le_archPart_iff_poleCompression` — the minimal rank-two form;
  * `primePolynomial_le_archPart_of_zetaStronglyRecurrent` — the Bagchi comparison.

## Status of the targets
1. SRT-4a — proved.
2. SRT-4b — proved.
3. **SRT-4c — reduced to an open problem.**
   * Corpus target: `RHTower/ZetaThreeQuartersOfSurplus`. The surplus of off-diagonal prime pairs
     at bandwidth `4/3` must be `≤ 1/18` of the normalisation; the random-matrix value is `−1/144`.
   * Exchange rate: `RHTower/PairCorrelationExchangeRate`. Any finite bound `B` on the pair
     correlation just above `1` beats `2/3`.
   * No known unconditional method gives such a bound; see the no-go closure below.
4. SRT-5b, SRT-5b′ — corpus (isolated form) and Lean (depth-gap law).
5. **SRT-5c — solved.** The coupled criterion is equivalent to RH; the coupling is necessary; the
   minimal form is the corpus rank-two pole compression, i.e. the prime number theorem error at
   square-root scale; strong recurrence implies the criterion.

## No-go closure (SRT-4c, routes using known methods)
- **Exact barrier theorems or mechanisms.**
  1. *Size-only methods* (mean value theorem, large sieve): the excess `O(rX)·diag` is attained
     for aligned phases. This is proved in Lean as
     `le_integral_normSq_mul_normSq_expSum_of_nonneg`.
  2. *Upper-bound sieve for prime pairs*: it controls `Σ Λ(n)Λ(n+h) w(n)` only for `w ≥ 0`. At
     height `T` the pair kernel (Zeta23 `Aminus`, an integral over `t ∈ [T, 2T]`) carries the
     sign-changing phase `(m/n)^{it}`. So the sieve reduces to route 1, and using the oscillation
     needs prime-pair asymptotics with error terms: the parity problem.
  3. *Zero side*: an off-line zero of depth `δ` has weight `T^{2λδ}` at bandwidth `λ`. Absorbing
     it needs `N(½ + δ, T) ≪ T^{1 − 2λδ + ε}`. The density hypothesis is exactly `λ = 1`, so
     beyond `X = T` the zero side needs zero-density estimates stronger than the density
     hypothesis.
- **Strongest positive survivor.**
  * The exact off-diagonal law (diagonal plus the `k_η k_ω`-weighted prime-pair correlation at
    multiplicative distance `< 2 min(r, ρ)`).
  * The windowed mean value bound at every `X`, sharp in the size-only class.
  * The identification of the remaining input with boundedness of the pair correlation on
    `(1, λ)`. Through the corpus exchange rate this already improves `2/3` for any finite bound.
- **New insight.** `X = T` is simultaneously the diagonal threshold of the mean value theorem,
  the threshold at which upper-bound sieves lose the height phase, and the density-hypothesis
  threshold of the zero side. All three routes meet the same wall.
- **Status.** The positive survivors are proved in Lean (standard axioms). The remaining input,
  Montgomery's pair correlation just above `α = 1`, is open even under RH. SRT-4c stays in
  `1-in-progress` as a reduced open target.

## Log
- 2026-10-19 — created; SRT-1 to SRT-3 and SRT-5a proved and wired into
  `GaloisForLFunctions.SquareRootThreshold`.
- 2026-10-19 — SRT-4a and SRT-4b proved (standard axioms only). Next: SRT-5b (converse visibility
  for `ζ`), then SRT-4c.
- 2026-10-19 — SRT-5b found in the corpus (isolated form). Isolation cannot be dropped: an
  off-line neighbour of depth `δ'` inflates its odd-part contribution by `cosh²(δ'a)`, the same
  order as the pair term when `δ' ≈ δ`. Open: SRT-5b′ (depth-gap law), SRT-4c (`X > T`, the
  Zeta23 `λ = 1` wall), SRT-5c (prime–tail coupling inequality).
- 2026-10-19 — SRT-5b′ depth-gap law proved (standard axioms). Remaining open: SRT-4c
  (`X > T`, Zeta23 `λ = 1` wall) and SRT-5c (prime–tail coupling inequality).
- 2026-10-19 — SRT-4c and SRT-5c worked through. SRT-5c solved in Lean. SRT-4c reduced to the
  pair correlation just above `α = 1`, with three barrier mechanisms and the corpus exchange rate.
