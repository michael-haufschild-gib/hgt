# Formalization certificate: two prime theta-interval anomalies generate the Xi normal module

- **ID:** `hedenmalm-two-prime-theta-interval-normal-frame-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `hedenmalm-two-prime-theta-interval-normal-frame.md`

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/EntireInterpolation.lean
formal/GaloisForLFunctions/HTGeometry/EntireBezout.lean
formal/GaloisForLFunctions/HTGeometry/PrincipalConormal.lean
formal/GaloisForLFunctions/HTGeometry/KroneckerApproxRecurrence.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmIntervalAnomaly.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaIntervalTransform.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeNormalFrame.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeBezout.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeIdeal.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeChannels.lean
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPrimeFrameObstruction.lean
```

All eleven are reachable from `GaloisForLFunctions.HTGeometry` and `GaloisForLFunctions.RHTower`.

## What was new infrastructure

Three of the modules are general analysis, built here because neither mathlib nor the corpus had
them, and reusable well beyond this card.

* `exists_entire_interpolation` — **Mittag-Leffler interpolation**.  Given an entire `F` whose
  zeros `w i` are simple, nonzero and escape to infinity, and arbitrary target values `c i`, there
  is an entire `b` with `b (w i) = c i`.  The interpolant is the series
  `sum_i c i * (z / w i) ^ N i * dslope F (w i) z / deriv F (w i)`.  Each term is entire because
  `dslope` removes the singularity; each vanishes at every other node; the exponents `N i` are
  chosen index by index so that the `i`-th term is dominated by a summable majorant on the disc of
  radius `‖w i‖ / 2`, and on a fixed disc that domination holds for all but finitely many `i`.

* `exists_entire_quotient` — **analytic division**.  If the analytic order of `f` dominates that of
  a nonzero entire `g` at every point, then `f = q g` with `q` entire.  The quotient is the
  meromorphic normal form of the pointwise quotient, analytic because its divisor is non-negative;
  the factorization propagates from a punctured neighbourhood of a non-zero of `g` by the identity
  theorem.

* `exists_entire_bezout` — **Wedderburn's lemma** for entire functions, obtained by interpolating
  `1/g` at the zeros of `f` and dividing the residual `1 - a g` by `f`.

* `principalCotangentEquiv` — for a cancellable `g` in a commutative ring, multiplication by `g`
  identifies `R / (g)` with the conormal module `(g)/(g)^2`.

## Formal theorem chain

Namespace `RHTower.HedenmalmThetaSource` unless stated otherwise.

| # | card statement | Lean declaration |
|---|---|---|
| `(3)` | the rank-one anomaly vectors | `HedenmalmPrimeTranslation.integerAnomaly` |
| `(4)` | exact interval transgression | `HedenmalmIntervalAnomaly.integerAnomaly_eq_intervalMass` |
| `(5)` | `hat r_n = q_n Xi_C` | `integral_integerAnomaly_sourceChar` |
| `(5a)` | multiplicative Wess--Zumino law | `HedenmalmIntervalAnomaly.integerAnomaly_mul` |
| `(6)` | the centered window is positive, even, integrable | `HedenmalmIntervalAnomaly.centeredWindow_pos`, `centeredWindow_neg`, `integrable_centeredWindow` |
| `(7)` | **`hat c_n = a_n Xi_C`** | `integral_centeredWindow_sourceChar` |
| `(7)` | closed trigonometric form of `a_n` | `centeredMultiplier_eq_sin` |
| `(7)` | the entire representative and its value `n^{-1/2} log n` at the origin | `centeredMultiplierE`, `differentiable_centeredMultiplierE`, `centeredMultiplierE_at_zero` |
| `(8)` | `a_n` is even and real | `centeredMultiplierE_neg`, `centeredMultiplierE_conj` |
| `(9)` | the zero set is `2 pi k / log n`, `k` a nonzero integer | `centeredMultiplierE_eq_zero_iff` |
| `(9)` | the zeros are simple, injectively indexed, escaping | `deriv_centeredMultiplierE_ne_zero`, `analyticOrderAt_centeredMultiplier_eq_one`, `injective_centeredZero`, `tendsto_norm_centeredZero_cofinite` |
| `(10)` | prime-2 / prime-3 have no common zero, by unique factorization | `HedenmalmIntervalAnomaly.no_common_zero_centered_two_three` |
| `(11)` | the conormal module of the Xi divisor | `xiConormalEquiv`, `GaloisForLFunctions.HTGeometry.principalCotangentEquiv` |
| `(12)` | the two window classes generate `I/I^2` | `windowCotangent`, `span_windowCotangent_eq_top` |
| `(13)` | **the Bezout identity `b_2 a_2 + b_3 a_3 = 1`** | `exists_two_prime_bezout`, `exists_entire_two_prime_bezout` |
| `(14)` | **`(hat c_2, hat c_3) = (Xi_C)` as ideals** | `span_entireCenteredWindow_eq_xiIdeal` |
| `(15)`,`(16)` | a nonvanishing multiplier retains the exact analytic order of `Xi_C` | `analyticOrderAt_centeredWindowTransform`, `two_prime_retains_analyticOrder`, `two_prime_retains_divisor` |
| `(17)` | the two bounded self-adjoint prime channels | `channelOperator`, `channelOperator_inner` |
| `(17)` | the common real symbol zero set is the real Xi divisor | `channelSymbol_eq_zero_iff` |
| `(17)` | **the analytic cokernel is `O(C)/(Xi_C)`** | `windowRow`, `range_windowRow`, `twoPrimeCokernelEquiv` |
| `(18)`,`(19)` | the compact reciprocal multiplier | `compactNormalMultiplier`, `compactNormalMultiplier_eq` |
| `(20)` | `A_n(-1/zeta) = a_n(zeta)` on every root block | `compactNormalMultiplier_root` |
| `(21)` | the essential pair does not annihilate a nonzero root mode | `essential_pair_ne_zero` |
| `(22)`,`(23)` | the frame symbol and the `1/abs t` decay | `frameSymbol`, `mul_centeredMultiplier_eq_frameSymbol`, `norm_centeredMultiplier_le`, `tendsto_norm_centeredMultiplier_atTop` |
| `(24)` | the pointwise ceiling `b_p(t)^2 <= 4/p` | `sq_frameSymbol_le_four_div` |
| `(25)` | the finite-prime Kronecker obstruction | `exists_gt_sum_sq_frameSymbol_lt` |
| `(26)`,`(27)` | the summably weighted all-prime obstruction | `exists_gt_tsum_weighted_frameSymbol_lt` |
| — | Kronecker recurrence at arbitrarily large times | `GaloisForLFunctions.kronecker_approx_atTop` |

## Two Lean-level clarifications

The corpus definition `centeredMultiplier` divides by `I * z` and therefore carries Lean's junk
value `0` at the origin, not the true removable value `n^{-1/2} log n`.  Every statement that needs
an entire function — the Bezout identity, the ideal generation, the conormal generation — uses
`centeredMultiplierE`, the difference quotient `dslope (sinPhase n) 0`, which agrees with
`centeredMultiplier` off the origin (`centeredMultiplierE_eq`) and takes the correct value there.

The ambient ring is the corpus algebra `RHTower.DeningerEntire` of entire functions, with its
principal ideal `deningerEntireXiIdeal`.  That it is an integral domain is itself a theorem here
(`deningerEntire_cancel`), proved from the identity theorem, and it is what makes the conormal
identification `(11)` correct.

## Verification

```bash
cd formal
lake env lean GaloisForLFunctions/HTGeometry/EntireInterpolation.lean
lake env lean GaloisForLFunctions/HTGeometry/EntireBezout.lean
lake env lean GaloisForLFunctions/HTGeometry/PrincipalConormal.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeNormalFrame.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeBezout.lean
lake env lean GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeIdeal.lean
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeIdeal
```

All clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.
