# Slice positivity at bounded orders for almost every height, with a polynomial rate

- **ID:** XI-SLICE-BOUNDED-ORDER-RATE
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route LA); sharpening of XI-SLICE-BOUNDED-ORDER
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 57; sharpens MUST-577
- **STATUS:** MUST-583

## Theorem [L]

`RHTower.eventually_volume_xiSliceCoeff_nonpos_bounded_order_pow_le`: for every `1 ≤ m ≤ 7500`
there is `C` such that for every `K ≥ 1` and all large `T`,

`|{t ∈ [T, 2T] : c_{2k}(t) ≤ 0 for some k ≥ K}| ≤ C T / K^{2m}`.

Here `c_n(t)` are the Taylor coefficients of `ξ(½+x+it)ξ(½−x+it)`. MUST-577 had an unspecified
rate; this gives `K^{−15000}`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

1. **Split of Selberg's polynomial.** `D_x = P_x + H_x`: `P_x = Σ_{p ≤ N} Λ(p)W_x(p)p^{−s}` and
   `H_x` = the proper prime powers. On `Re s ≥ ½ + δ`, `0 < δ ≤ 1`:
   `|H_x(s)| ≤ Σ_{p, k≥2} log p · p^{−k(½+δ)} ≤ 4 Σ_p log p · p^{−1−2δ} ≤ 36/δ`.
   Proof: the pairs `(p, k)` are injected, a geometric series with ratio `≤ 3/4` is summed, and
   Chebyshev's bound `Σ Λ(n)n^{−σ} ≤ 6σ/(σ−1)` is applied.
   On the box (`δ ≥ 3R/4`) this is `≤ 48/R ≤ εL/8` once `κ ≥ 384/ε`, so large values of `D_x` are
   large values of `P_x` (`largeNearBox_selbergVonMangoldtPoly_subset_prime`).
2. **Moments of prime-supported convolutions.** Let `a` be supported on the primes `≤ N` and `w ≥ 0`
   completely multiplicative. Then `Σ_{n ≤ N^m} |a^{⋆m}(n)|² w(n) ≤ m! (Σ_{n ≤ N} |a(n)|² w(n))^m`
   (`wMass_pow_le`).
   - `a^{⋆m}` lives on `Ω(n) = m` (`support_pow_prime`), so `(a^{⋆m} ⋆ a)(n)` has at most `m+1`
     nonzero terms (`normSq_mul_prime_le`).
   - Cauchy–Schwarz and the reindexing `n = de` (`sum_Icc_sum_divisorsAntidiagonal`) finish.
3. **High moments on vertical lines.** `E_a^m = E_{a^{⋆m}}` on `[1, N^m]` (`edPoly_pow_eq`). The
   mean value theorem then gives
   `∫|E_a(½+δ+iτ)|^{2m} ≤ (T₂−T₁ + 8N^m(1+log N^m)) m! (5/δ²)^m`
   (`integral_norm_edPoly_pow_displaced_le`, `integral_norm_selbergPrimePoly_pow_le`).
4. **Large values.** Apply the area mean value on discs of radius `R/4` to `P_x^m` at threshold
   `M^m`: measure `≤ 1380 m!(20/R²)^m (T + 17R + 8N^m(1+log N^m))/(π M^{2m})`
   (`volume_largeNearBox_selbergPrimePoly_le`). With `x = T^{1/30000}` and `m ≤ 7500`,
   `N^m ≤ 2^m T^{1/2}`, so at `M = εL/8` the term is `≤ (4140/π) T m! (1280/(ε²κ²))^m`.
5. **One scale.** `exists_volume_not_zetaLogDerivScaleData_le_pow` bounds the measure by
   `C T (e^{−κ/120000}/ε + m!(1280/(ε²κ²))^m) + C T^{1/2}`. The refactored box theorem
   `volume_not_zetaLogDerivScaleData_le_of_largeNearBox` keeps the `D_x` measure abstract.
6. **Dyadic assembly.** Use `κ₀ = K/2` and `e^{−u} ≤ (2m)!/u^{2m}`. Each scale costs
   `≤ A T 2^{−j}/κ₀^{2m}` (`volume_dyadic_scale_pow_le`), and the sum is `≤ 2^{2m+1} A T/K^{2m}`.
   Orders `≥ (log t)/16` cost `≤ T/(2K^{2m})` for large `T`. For `K` below the threshold the trivial
   bound `T` is absorbed into `C`.

## Lean modules (all in `formal/GaloisForLFunctions/RHTower/`, wired in `RHTower.lean`)

- `PrimeSupportedConvolutionMoments`: `wMass`, `sum_Icc_sum_divisorsAntidiagonal`,
  `support_pow_prime`, `normSq_mul_prime_le`, `wMass_pow_le`.
- `SelbergPrimePolynomialHighMoments`: `support_pow_le`, `edPoly_pow_eq`,
  `integral_norm_edPoly_pow_displaced_le`, `selbergPrimeCoeff`, `selbergPrimePoly`,
  `selbergPrimePowerPoly`, `selbergVonMangoldtPoly_eq_prime_add`, `sum_nonprime_vonMangoldt_rpow_le`,
  `norm_selbergPrimePowerPoly_le`, `volume_largeNearBox_selbergPrimePoly_le`.
- `ZetaLogDerivTypicalBoxHighMoments`: `largeNearBox_selbergVonMangoldtPoly_subset_prime`,
  `polyLength_pow_term_le`, `primePoly_term_le`, `scale_terms_pow_le`,
  `exists_volume_not_zetaLogDerivScaleData_le_pow`.
- `XiSliceBoundedOrderPolynomialRate`: `scale_bound_pow_le`, `volume_dyadic_scale_pow_le`,
  `eventually_volume_xiSliceCoeff_nonpos_bounded_order_pow_le`.
- `ZetaLogDerivTypicalBoxDensity` (edited): new `volume_not_zetaLogDerivScaleData_le_of_largeNearBox`;
  the old four-term theorem now derives from it.

Leaf builds with `--old`; axioms standard; `.ilean` collision sweep clean. One lemma was renamed to
`exp_neg_le_factorial_div_pow_of_pos` to avoid `EisensteinRowSumMajorant`.

## Limits and live residuals

- **Order cap.** `m ≤ 7500` comes from `N_x^m ≤ T^{1/2}` at `x = T^{1/30000}`. Taking `x = T^θ` with
  `θ → 0` as `κ` grows (`m ≍ 1/θ`) conflicts with the Lorentzian term. That term needs
  `R log x = κθ → ∞`. The best balance, `θ ≍ κ^{−1/2}`, suggests a stretched-exponential rate
  `e^{−c√K}`, which is not formalized.
- **Fixed `K`.** Density zero at a fixed `K` is not reached. The zero-shadow part is genuine: pairs
  with `β−½ = b ≪ 1/L` make `c₂ < 0` on `|t−γ| < b`. It is the average-distance quantity
  `Σ(β−½)⁺/T`.
