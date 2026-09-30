# Slice positivity at bounded orders for almost every height, stretched-exponential rate

- **ID:** XI-SLICE-BOUNDED-ORDER-STRETCHED
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route LA); sharpens MUST-577/583
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 58
- **STATUS:** MUST-585

## Theorem [L]

`RHTower.eventually_volume_xiSliceCoeff_nonpos_bounded_order_stretched_le`: there is `C` such that
for every `K ≥ 1` and all large `T`,

`|{t ∈ [T, 2T] : c_{2k}(t) ≤ 0 for some k ≥ K}| ≤ C T e^{−√K/6}`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

1. **Scale-dependent length.** At scale `R`, with `κ = R log T` and `s = √κ`, the explicit-formula
   length is `x = T^{1/s}`.
   - Its hypotheses hold: `(log T + 3)^{40} ≤ e^{4√(log T)} ≤ x` because `s ≤ √(log T)/4`, and
     `36 R log x = 36 s ≥ 1`. The window-sum hypothesis is `6 log x/log T = 6/s ≤ 1/4800`.
   - The four terms (`lorentz_term_sqrt_le`, `far_term_sqrt_le`, `window_term_sqrt_le`) decay like
     `e^{−s/4}/ε`.
2. **Moment order growing with the scale.** Take `m = ⌊s/4⌋`. Then `2m/s ≤ ½`, so
   `N_x^m ≤ 2^m T^{1/2}` and `8N^m(1+log N^m) ≤ T` (`polyLength_pow_term_sqrt_le`), since
   `8·2^m(1+m)(L+3) ≤ e^{L/2}` for `16m ≤ √L` (`eight_two_pow_le_exp`).
   The prime moment gives `m!(1280/(ε²s⁴))^m ≤ (320/(ε²s³))^m ≤ e^{−m} ≤ 3e^{−s/4}`
   (`factorial_mul_pow_le_exp_sqrt`).
3. **One scale.** `exists_volume_not_zetaLogDerivScaleData_le_sqrt`: measure
   `≤ C T e^{−√κ/4} + C T^{1/2}` for `κ ≥ max(9·10⁸, 1000/ε²)`.
4. **Dyadic assembly.** Take `κ₀ = K/2`. Since `√(2^jκ₀) ≥ (1+2j/5)√κ₀`
   (`one_add_mul_sqrt_le_sqrt_two_pow_mul`, Bernoulli with ratio `7/5`), scale `j` costs
   `C T e^{−√κ₀/4} 2^{−j}`, and the sum is `≤ 2C T e^{−√κ₀/4}`. Then
   `e^{−√(K/2)/4} ≤ e^{−√K/6}`. Orders `≥ (log t)/16` and the `T^{1/2}` terms cost
   `≤ ¾ T e^{−√K/6}` for large `T`.

## Lean modules (in `formal/GaloisForLFunctions/RHTower/`, wired in `RHTower.lean`)

- `ZetaLogDerivTypicalBoxScaledLength`: `lorentz_term_sqrt_le`, `far_term_sqrt_le`,
  `window_term_sqrt_le`, `polyLength_pow_term_sqrt_le`, `factorial_mul_pow_le_exp_sqrt`,
  `eventually_log_add_pow_le_exp_sqrt`, `sqrt_scale_facts`, `eight_two_pow_le_exp`,
  `sqrt_length_facts`, `ninetySix_div_le`, `sqrt_terms_combine`,
  `exists_volume_not_zetaLogDerivScaleData_le_sqrt`.
- `XiSliceBoundedOrderStretchedRate`: `one_add_mul_sqrt_le_sqrt_two_pow_mul`,
  `exp_neg_sqrt_two_pow_le`, `volume_dyadic_scale_sqrt_le`, `exp_neg_sqrt_half_le`,
  `eventually_volume_xiSliceCoeff_nonpos_bounded_order_stretched_le`.

Leaf builds with `--old`; axioms standard; `.ilean` collision sweep clean.

## Limits

- **Why `√K`.** The left-zero terms need `R log x → ∞`; the moment needs `m log x ≤ ¼ log T`; the
  moment gain is `(C m/κ²)^m`. With `log x = θ log T` this forces `θκ → ∞` and `m ≲ 1/θ`, so
  `m ≲ κ/(θκ)`. Taking `θκ ≍ √κ` balances the two at `e^{−c√κ}`.
- **Beyond.** An exponential rate `e^{−cK}` would need either the left zeros at fixed `R log x` (a
  Lorentzian bound without the `e^{−R log x/4}` decay), or large values of `P_x` beyond the
  mean-value range `N^m ≤ T` (splitting `P_x` into short prime ranges).
- **Fixed `K`.** Density zero at a fixed `K` is still the average-distance problem.
