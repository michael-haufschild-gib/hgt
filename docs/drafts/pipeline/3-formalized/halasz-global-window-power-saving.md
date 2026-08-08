# The large-value window is global: a power saving for the mean modulus

- **ID:** halasz-global-window
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every multiplicative `f` with `|f| ≤ 1`, every `z` with `logLog z ≥ 5(C+1)`
  and every `0 < T ≤ 1` with `T log z ≥ 1`, at `σ = 1 + 1/log z`
  `∫_{|t| ≤ T} |∑_n f(n) n^{-σ-it}| dt ≤ (64e^{11/2} + 4e^{9/2+C})·(T log z)^{4/5}`,
  below the trivial bound `≍ T log z`.

## Goal

The corpus's Halász integral bound was vacuous, and this says why and repairs it. Its window estimate
`abs_sub_le_of_norm_gt` needs the spacing hypothesis `|t − u|·log z ≤ π`, so
`volume_halaszLargeValues_le` covers `[−T, T]` by `2T log z/π` cells of that width. The per-cell
diameter is `≍ δ/log z`, so the product is `≍ T·δ` — worse than the trivial `2T` for every
`δ > 1/(2√2)`, hence for every `δ` in the range `δ² ≍ logLog z` where the damping matters. The whole
window gain was being spent on the cell count.

The distance growth law needs no relation between `t − u` and `log z`. So the confinement is global:
all large values on `[−T, T]` lie in a single window, and the cell factor disappears.

## The mechanism

Two frequencies at which the series exceeds the damped level are both within `δ` of `f`, so by the
triangle inequality for the Granville–Soundararajan distance

`𝔻(n^{it}, n^{iu}; z) ≤ 2δ`,   hence   `charSepLower z (t − u) ≤ 4δ²`.

`charSepLower z v = logLog z − log(5 + 1/|v|) − C₀` increases with `|v|`, so `|t − u| < Δ` for every
`Δ` with `4δ² < charSepLower z Δ`; since `5 + 1/Δ ≤ 6/Δ` for `Δ ≤ 1`, the choice
`Δ = e^{4δ²+C+1}/log z` is admissible as soon as `4δ² + C + 1 ≤ logLog z`. The measure of the
large-value set is then `2Δ`, with no cell factor, and the split at the damped level gives

`∫_{|t| ≤ T} ≤ (1 + 1/(σ−1))e^{7/2+2(σ−1)(log z+log 4)−δ²}·2T + (1 + 1/(σ−1))e^{7/2}·2Δ`.

At `σ − 1 = 1/log z` the two terms are `≍ (log z)e^{−δ²}T` and `≍ e^{4δ²}`. They balance at
`δ² = log(T log z)/5`, both equal to `(T log z)^{4/5}`.

## Where the exponent comes from

The `4` in `e^{4δ²}` is the square of the triangle-inequality factor `2`: two distances of `δ` bound a
character separation of `2δ`, whose square is `4δ²`. The balance of `Le^{−x}` against `e^{4x}` is at
`e^{5x} = L`, so the exponent is `4/5` for exactly this reason, and no dyadic refinement improves it —
levels `δ_j² = j` contribute `(log z)e^{−j}·e^{4j}/log z = e^{3j}`, dominated by the top level. The
truth for the integral is `≍ log(T log z)`; reaching it needs the `1/|t−t₀|` pointwise decay, where
the cross term `2√(δ² logLog z)` of the triangle inequality is the loss to remove.

## Lean

| Statement | Module |
|---|---|
| `charSepLower_mono_abs` | `RHTower/Sieve/HalaszGlobalUniqueClose.lean` |
| `card_filter_close_le_one_of_separation` | `RHTower/Sieve/HalaszGlobalUniqueClose.lean` |
| `sum_norm_smoothMulSum_le_of_separation` | `RHTower/Sieve/HalaszGlobalUniqueClose.lean` |
| `sqrt_mulDistSqPair_le_of_norm_gt` | `RHTower/Sieve/HalaszGlobalLargeValueWindow.lean` |
| `abs_sub_lt_of_both_close` | `RHTower/Sieve/HalaszGlobalLargeValueWindow.lean` |
| `abs_sub_lt_of_norm_gt` | `RHTower/Sieve/HalaszGlobalLargeValueWindow.lean` |
| `volume_halaszLargeValues_le_window` | `RHTower/Sieve/HalaszGlobalLargeValueWindow.lean` |
| `integral_norm_tsum_twistedSummand_le_of_volume` | `RHTower/Sieve/HalaszGlobalIntegralBound.lean` |
| `integral_norm_tsum_twistedSummand_le_window` | `RHTower/Sieve/HalaszGlobalIntegralBound.lean` |
| `lt_charSepLower_of_lt`, `four_mul_sq_lt_charSepLower_exp` | `RHTower/Sieve/HalaszGlobalWindowExplicit.lean` |
| `window_balance_le` | `RHTower/Sieve/HalaszGlobalWindowExplicit.lean` |
| `integral_norm_tsum_twistedSummand_le_power_saving` | `RHTower/Sieve/HalaszGlobalWindowExplicit.lean` |

All unconditional: `#print axioms` gives `[propext, Classical.choice, Quot.sound]` throughout.

`integral_norm_tsum_twistedSummand_le_of_volume` is the universal form of the split — the measure of
the large-value set is a parameter, so the existing `integral_norm_tsum_twistedSummand_le` is its
instance at the cell-covering value of `W`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3  Lean theorems above, `lake build` green, axioms clean
- [ ] 3 → 4

## Log
- 2026-08-08 — created in 3-formalized; the cell covering identified as the loss, the global window law
  proved, and the balanced power saving `(T log z)^{4/5}` formalized.

## The first moment is better served by the mean square

The affine mean square `integral_Icc_normSq_LSeries_le_general_affine` plus Cauchy–Schwarz against `1`
gives, with no distance and no exceptional frequency,

`∫_{|y| ≤ T} ‖L(a,σ+iy)‖ dy ≤ √(2T(Q₁ + Q₀T))`,   `Q₁ = 5πe∑_n n‖a_n n^{-σ}‖²`, `Q₀ = (5π/2)∑_n ‖a_n n^{-σ}‖²`,

and for `|f| ≤ 1` truncated at `N` with `σ ≥ 1` the masses are `Q₁ ≤ 5πe(1 + log N)` and `Q₀ ≤ 5π`:

`∫_{|y| ≤ T} ‖L(f_{≤N},σ+iy)‖ dy ≤ √(2T(5πe(1 + log N) + 5πT))`.

At `T ≍ 1` this is `≍ √(log N)`, below the window route's `(log N)^{4/5}` and far below the trivial
`≍ log N`. So for the *first moment* the square root of the mean square is the stronger of the two
mechanisms, and the window law's value lies elsewhere: it is the only one of the two that locates the
exceptional frequency, which is what a Halász-type dichotomy — as opposed to a mean bound — requires.

| Statement | Module |
|---|---|
| `integral_Icc_norm_LSeries_le_sqrt_general_affine` | `RHTower/Sieve/AffineMeanSquareL1.lean` |
| `norm_truncSeq_mul_rpow_sq_le` | `RHTower/Sieve/AffineMeanSquareL1.lean` |
| `generalMeanSquareRate_truncSeq_le`, `generalMeanSquareConst_truncSeq_le` | `RHTower/Sieve/AffineMeanSquareL1.lean` |
| `integral_Icc_norm_LSeries_truncSeq_le` | `RHTower/Sieve/AffineMeanSquareL1.lean` |

## The Cesàro chain, distance-free

The arithmetic half of the Cesàro route never sees the analytic estimate, so the assembly holds with
the vertical integral as a parameter, and `‖s‖ ≥ σ` on the line turns a first moment into a bound for
the Cesàro integral:

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n) + (1/2π)·(x^σ/σ²)·√(2T(5πe(1+log N) + 5πT))`

for every `|f| ≤ 1`, `1 ≤ σ ≤ 2`, `T ≥ 1`, `x ≥ N`. The analytic term is `≍ x^σ√(log N)` where the
pointwise route gives `≍ x^σ log N` — a whole square root of the mass, with no distance hypothesis,
no sieve level and no exceptional frequency. It is still `≫ x^σ`, so it does not reach `o(N)`; the
Euler-bound wall is untouched. What it removes is the *logarithm*, not the wall.

| Statement | Module |
|---|---|
| `norm_sum_Icc_mul_log_div_le_cesaro_of_integral` | `RHTower/Sieve/CesaroLogWeightL1.lean` |
| `integral_symm_norm_cesaro_le_of_l1` | `RHTower/Sieve/CesaroLogWeightL1.lean` |
| `norm_sum_Icc_mul_log_div_le_cesaro_l1` | `RHTower/Sieve/CesaroLogWeightL1.lean` |

## The kernel is its own weight

Cauchy–Schwarz against the kernel `x^σ/‖s‖²` instead of against `1` replaces the range length `2T` by
the kernel mass `x^σπ/σ`:

`∫_{|t| ≤ T} ‖L(g,σ+it)x^s/s²‖ dt ≤ x^σ√(πQ/σ³)`   whenever `∫_{|t| ≤ T}‖L(g,σ+it)‖² ≤ Q`,

which beats the unweighted `(x^σ/σ²)√(2TQ)` for every `T > π/2` and carries no `√T` in front. With the
explicit mean square `Q ≤ 5πe(1 + log N) + 5πT` the Cesàro chain becomes

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n) + (1/2π)·x^σ√(π(5πe(1+log N) + 5πT)/σ³)`.

| Statement | Module |
|---|---|
| `integral_symm_norm_cesaro_le_of_meanSquare` | `RHTower/Sieve/CesaroWeightedL1.lean` |
| `integral_Icc_normSq_LSeries_truncSeq_le` | `RHTower/Sieve/CesaroWeightedL1.lean` |
| `norm_sum_Icc_mul_log_div_le_cesaro_meanSquare` | `RHTower/Sieve/CesaroWeightedL1.lean` |

## The analytic side is height-free

Cauchy–Schwarz pays the mean square of the whole range, so it keeps a `√(Q + κT)`. The dyadic split
pays it once per block against a kernel constant that decays with the block: for the second-order
kernel `x^σ/‖σ+it‖² ≤ (x^σ/(σ2^m))/|t|` on `σ2^m ≤ |t| ≤ σ2^{m+1}`, so both geometric sums have ratio
`≤ 1/2` and the height disappears:

`∫_{|t| ≤ T} ‖L(g,σ+it)x^s/s²‖ dt ≤ 8x^σ√Q + 12x^σ√κ`   for every `T`, `1 ≤ σ ≤ 2`.

This is `integral_symm_norm_mul_kernel_var_le` of `HTGeometry/VerticalKernelBlockConstants.lean`
instantiated at the Cesàro kernel — the machine was already there; only the block constants were
missing. For `|f| ≤ 1` truncated at `N` the Cesàro chain becomes

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ ∑_{n ≤ N} E(σ,T,x/n)
    + (1/2π)(8x^σ√(5πe(1+log N)) + 12x^σ√(5π))`,

so the three analytic terms of the route now stand as

| route | analytic term |
|---|---|
| pointwise Euler bound | `x^σ log N` |
| Cauchy–Schwarz against `1` | `x^σ√(T + log N)` |
| dyadic blocks, kernel constant per block | `x^σ√(log N)`, uniformly in `T` |

Since `T` may now be taken as large as one likes at no analytic cost, the arithmetic error
`∑_{n ≤ N} E(σ,T,x/n) ≍ N(log T)/T + x^σ(log N)/T` is free. What remains is `x^σ√(log N) ≫ x^σ`: the
Euler-bound wall, untouched by any of the three.

| Statement | Module |
|---|---|
| `sqrt_two_le_three_halves`, `sum_range_block_kernel_le` | `RHTower/Sieve/CesaroDyadicMeanSquare.lean` |
| `integral_symm_norm_cesaro_le_of_meanSquare_dyadic` | `RHTower/Sieve/CesaroDyadicMeanSquare.lean` |
| `norm_sum_Icc_mul_log_div_le_cesaro_dyadic` | `RHTower/Sieve/CesaroDyadicMeanSquare.lean` |
