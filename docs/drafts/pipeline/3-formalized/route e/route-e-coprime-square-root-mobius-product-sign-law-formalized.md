# Route E coprime square-root Möbius product-sign law — Lean certificate

- **ID:** ROUTE-E-COPRIME-SQRT-MOBIUS-PRODUCT-SIGN-001
- **Stage:** 3-formalized
- **Paper proof:** [route-e-coprime-square-root-mobius-product-sign-law.md](route-e-coprime-square-root-mobius-product-sign-law.md)
- **Capstone module:** `GaloisForLFunctions.RHTower.Sieve.RouteECoprimeSignAllWindows`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` clean on every module below; targeted `lake --old build`;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every capstone. No computation.

## The card's statements

Namespace `RHTower.Sieve`.  `coprimeSignClassCount x h s` is `R_s(x,h)` of `(2)` (pairs of
`balancedPairs x h` with `μ(n₁)μ(n₂) = s` and `gcd(n₁,n₂) = 1`), `squarefreeDensity = D = 6/π²`,
`RHTower.coprimeSharedPrimeDensity = A = ∑_p (p+1)^{-2}`.

| Card item | Lean theorem |
|-|-|
| **(3)** for every window law with `h/log log(3x) → ∞` (no upper bound on `h` needed): for every `ε > 0`, eventually `D²/2 − D²A − ε ≤ R_s(x,h)/(h√x log 2)` | `route_e_sign_density_all_windows` |
| margin `D²(1/2 − A) > 0` (`(13)`) | `route_e_margin_pos`, `RHTower.coprimeMargin_pos` |
| both sign classes eventually nonempty | `route_e_signClass_nonempty_all_windows` |
| **(4)** every large `[x, x+h(x)√x]` contains `m₊` with `μ(m₊) = 1` and `m₋` with `μ(m₋) = −1` | `exists_moebius_pos_and_neg_all_windows` |
| the example `h = (log log 3x)^{1+η}` | `tendsto_logLog_rpow_div_logLog`, `exists_moebius_pos_and_neg_logLog_window` |
| `(6)`–`(12)`, `(14)`: pair algebra, shared-prime sectors, tail, collision normalisation | previously formalized (`RouteEMain`, `RouteEAveraged`, `SharedPrimeTail*`, `MobiusCoprimeEulerMargin`, `MobiusCoprimeProductSignExtraction`) |

## The analytic input `(5)`, replaced by what the proof uses

The card applies Matomäki–Radziwiłł's bilinear theorem `(5)` to `f = μ, μ², μ²1_{p∤·}`.  The
formalization uses exactly those three consequences, as averaged fibre mean squares
(`route_e_sign_density_of_meanSquare`), and proves them unconditionally in two regimes glued by the
window laws `min(h, √x)` and `max(h, √x)` (`tendsto_min_div_logLog`):

**`h ≤ √x` — Matomäki–Radziwiłł for `μ` at every length.**
`averagedMeanSquare_moebius_of_tendsto` (`Sieve/MoebiusAveragedMeanSquareAllLengths`): for every
`h → ∞` with `h ≤ √x`, `AveragedMeanSquare μ h`.  The head window `W = M/√h` over
`M = ⌊√x + h⌋` is bounded by

| piece | Lean |
|-|-|
| Ramaré decomposition over a ladder of prime ranges, first-small frequency sets, amplification by a large block of the previous range | `Sieve/MoebiusMultiRangeWindow` (`integral_Icc_normSq_logPoly_moebius_le_multiRange`, `setIntegral_normSq_le_sum_amplified`) |
| sharp ladder error `≤ 2(5π/2·W + 5e/2·⌊M(1+η)⌋)(ηM + 6M/Q)` | `Sieve/RamareLadderErrorSharp` (`integral_normSq_ramareLadderError_le_sharp`) |
| Lemma 13: mean square of `Q_B^ℓ·C` by gcd-coincidence counting | `Sieve/PrimeBlockPowerCofactorMeanSquare` |
| amplified cofactor cost `15(8ℓ+8)^ℓ S M² T^{2α−2β}`; first-range mean-value cost `15M²S^{−2α}` | `Sieve/MoebiusMultiRangeCofactorBounds`, `Sieve/MoebiusMultiRangeLowCost` |
| schedule `ν_j = ν^{2^j}`, `R_j = ⌈exp ν_j⁴⌉`, `η_j = e^{−ν}/2^j`, `L_j = ⌈2ν_j⁵/η_j⌉`, `α_j = 1/4 − 1/(8·2^j)` | `Sieve/MoebiusRangeLadderSchedule` |
| each range costs `≤ 1500M²/(2^j log ν)` (harmonic mass `≥ ½ log ν_j`, rough class by Turán, error, cofactor), all ranges `≤ 3000M²/log ν` | `Sieve/MoebiusRangeLadderCosts`, `Sieve/MoebiusRangeLadderWindow` (`rangeLadder_sum_le`) |
| exceptional set at the last range `ν_K ∈ [T, T²]`: `√W·|U| ≤ M·exp(−T⁴⁰/(8 log T))` | `Sieve/MoebiusRangeLadderExceptional` (`sqrt_mul_measureReal_rangeLadder_exceptional_le`) |
| high range (Route T up to the frequency top `2√x`) | `Sieve/HighRangeRouteTWindowTop` (`exists_top_high_bound`) |
| assembly and the relative budget `→ 0` | `Sieve/MoebiusHeadWindowAllLengths` (`integral_head_le_ladder`), `Sieve/MoebiusAveragedMeanSquareAllLengths` (`tendsto_headBudget`) |

The `μ²` and `μ²1_{p∤·}` inputs below `√x` are the corpus's truncation machinery
(`maximalWindowDevMeanSquare_moebius_sq`, `maximalWindowDevMeanSquareAt_coprime`).

**`h ≥ √x` — the prime number theorem and the square-divisor count.**
`Sieve/RouteELongWindow`: every fibre window starts below its own length, so
`maxWindowAbs μ ≤ 2·mertensSup(3h)` (`maximalWindowFirstMoment_moebius_long_window`) and the
squarefree deviations are `≤ 6(H+1)^{3/2}`, `≤ 8(H+1)^{3/2}`
(`maxWindowDevSq_moebius_sq_le_long`, `maxWindowDevSq_coprime_le_long`, from
`sum_count_sq_dvd_window_le`); `maximalWindowDevMeanSquareAt_of_long` turns these into the three
inputs (`routeE_longWindow_inputs`, `route_e_sign_density_long_windows`).
