# The mean square of a Dirichlet polynomial is affine in the height

- **ID:** dirpoly-affine-mean-square
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every `a : Fin N → ℂ` and `T ≥ 1`,
  `∫_{|t| ≤ T} |∑_{m < N} a_m (m+1)^{it}|² dt ≤ 5πe∑_{m < N}(m+1)|a_m|² + (5π/2)T∑_{m < N}|a_m|²`.

## Goal

`DirichletDiagonal.lean` reduced the mean square to its off-diagonal sum and named the missing input a
Hilbert inequality for the frequencies `log n`; `DirichletIntegralMeanValue.lean` then bounded that sum
term by term, which charges the largest frequency gap to every coefficient and costs `4N(1 + log N)`
times the plain mass. That claim of a missing input was stale: `GeneralAffineMeanSquare.lean` already
proves the affine mean square for an *arbitrary* finitely supported Dirichlet series, via the
almost-diagonal mean value theorem and the integer neighbour count. What was missing was only the
identification of a Dirichlet polynomial as such a series.

## The bridge

Read `a` as the coefficient sequence indexed from `1` with abscissa `0`. Then
`L(a, i(−t)) = dirPoly N a t` (`LSeries_dirSeq_eq_dirPoly`), since `n^{-(0+iy)} = e^{-iy log n}`, and
the mean square is even in the frequency (`integral_Icc_normSq_comp_neg`). The two masses of the
affine estimate become the `n`-weighted and plain coefficient masses.

`∑_m (m+1)|a_m|² ≤ N∑_m|a_m|²` always, so the affine form is never worse than the previous bound and
better by the whole logarithm — and by a factor `N/k` whenever the mass sits below `k`.

## Consequences

* `volume_largeValues_le_affine` — Chebyshev on the level set with the affine mean square, replacing
  `(T + 4N(1 + log N))∑|a_m|²`;
* `integral_norm_dirPoly_halasz_affine` — the Halász mean-value bound `V·T + M·(mean square)/V²` with
  the affine mean square, the form the large-values and sixth-moment routes consume.

## Lean

| Statement | Module |
|---|---|
| `dirSeq`, `dirSeq_succ`, `dirSeq_support`, `twistedTruncCoeff_dirSeq` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `LSeries_dirSeq_eq_dirPoly` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `integral_Icc_normSq_dirPoly_le_affine` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `volume_largeValues_le_affine` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `integral_norm_dirPoly_halasz_affine` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |

All unconditional: `[propext, Classical.choice, Quot.sound]`.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3
- [ ] 3 → 4

## Log
- 2026-08-08 — created in 3-formalized; the stale "missing Hilbert inequality" claim in
  `DirichletDiagonal.lean` corrected to point at the affine mean square.

## The twisted series: a factor `L`

`HalaszMeanSquare.integral_norm_dirPoly_twisted_halasz` feeds the sup bound `damped + trunc` into the
`(T + 4L(1 + log L))∑|a_m|²` mean square. With the affine mean square and the explicit coefficient
masses — `∑_m (m+1)‖a_m‖² ≤ 1 + log L` and `∑_m ‖a_m‖² ≤ 2` for `|f| ≤ 1` and `σ ≥ 1`, since
`∑_n n·n^{-2σ} ≍ log L` where `∑_n n^{-2σ} ≍ 1` —

`∫_0^T ‖F_L(σ+iu)‖ du ≤ V·T + (damped + L^{1−σ}/(σ−1))·(5πe(1 + log L) + 5πT)/V²`

(`integral_norm_dirPoly_twisted_halasz_affine`). The mean-square factor drops from `L log L + T` to
`log L + T`: a whole factor `L`. This is the form the large-values and sixth-moment routes consume, and
it is not touched by the modulus-first no-go
(`docs/drafts/pipeline/5-failed/modulus-first-vertical-integral-no-go.md`), which concerns the vertical
integral of a *contour* representation, not the mean value of a Dirichlet polynomial.

| Statement | Module |
|---|---|
| `norm_sq_twistedTruncCoeff_le` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `sum_norm_sq_twistedTruncCoeff_le_two` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `sum_mul_norm_sq_twistedTruncCoeff_le` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |
| `integral_norm_dirPoly_twisted_halasz_affine` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |

## The regime that changes

With `σ − 1 = A/log L` both parts of the sup are `≍ log L` — the damped size because
`1 + 1/(σ−1) ≍ log L/A`, and the truncation error `L^{1−σ}/(σ−1) = e^{−A}(log L)/A` because the tail of
the twisted series past `L` does not decay in `L` at that abscissa. Optimising `V` in `V·T + K/V²`
gives `≍ (K T²)^{1/3}`, so

* affine mean square: `K ≍ (log L)(log L + T)`, optimum `≍ ((log L)(log L + T)T²)^{1/3}`, which beats
  the trivial `T log L` for every `T ≳ log L`;
* previous mean square: `K ≍ (log L)(T + L log L)`, optimum `≍ (L(log L)²T²)^{1/3}` for `T ≤ L log L`,
  which beats `T log L` only for `T ≳ L/log L`.

So the bound moves from a height range no Perron truncation uses to the range they all use. The
`√T`-free `max T 1` form (`integral_Icc_normSq_dirPoly_le_affine_max`) removes the last constraint
`T ≥ 1`.

## The first moment: Cauchy–Schwarz dominates the cell-maximum route

`DirichletFirstMomentLargeValues.integral_norm_dirPoly_le_largeValues` bounds `∫‖F‖` by discretising
into cells, splitting the cell maxima into two `Δ`-separated families and applying the *discrete* mean
value, which costs the harmonic factor `(1/Δ + 2 log N)`. Unwinding its parameters at `T = 2nΔ` and
`Δ ≤ 1/log N` gives `≍ √(T(T + 4N log N)∑|a_i|²)`. Plain Cauchy–Schwarz against the affine mean square
gives

`∫_{|t| ≤ T}‖dirPoly N a t‖ dt ≤ √(2T(5πe∑_m(m+1)|a_m|² + (5π/2)T∑_m|a_m|²))`

(`integral_Icc_norm_dirPoly_le_sqrt_affine`) — the same shape with no logarithm and with the
`n`-weighted mass in place of `N` times the plain mass. So the discretisation buys nothing for the
first moment; its value lies only in *counting* large values, where the rarity of the exceptional set
is the point. The reflection identity used here is stated once for an arbitrary integrand
(`HTGeometry.integral_Icc_comp_neg`), with the mean-square version as its instance.

## Gallagher's base case

`GallagherMeanValue.lean` calls its short-interval bound "the base case that every arithmetic
improvement is measured against", and it consumes the frequency mean square of the Gallagher polynomial
through `gallagher_split_integral`, which takes that mean square as a parameter. Since
`logPoly a (Icc 1 N) w = dirPoly N a' (2πw)`, the frequency mean square is a rescaled
Dirichlet-polynomial mean square — an identity now stated on its own
(`integral_Icc_normSq_logPoly_eq`), with the old bound as one instance and the affine one as another:

`∫_{|w| ≤ W}‖logPoly a w‖²dw ≤ (2π)⁻¹(5πe∑_m(m+1)|a_{m+1}|² + (5π/2)(∑_m|a_{m+1}|²)max(2πW,1))`,

against `(2πW + 4N(1 + log N))/π·∑_m|a_{m+1}|²`. The height-linear parts agree up to a constant; the
height-free parts are `∑(m+1)|a_{m+1}|²` against `N(1 + log N)∑|a_{m+1}|²` — a whole logarithm for
coefficients of constant size. Gallagher's bound inherits it verbatim
(`gallagher_meanValue_le_affine`).

| Statement | Module |
|---|---|
| `integral_Icc_normSq_logPoly_eq` | `RHTower/Sieve/LogPolyDirPoly.lean` |
| `integral_Icc_normSq_logPoly_le_affine` | `RHTower/Sieve/GallagherAffineMeanSquare.lean` |
| `gallagher_meanValue_le_affine` | `RHTower/Sieve/GallagherAffineMeanSquare.lean` |
| `integral_Icc_norm_dirPoly_le_sqrt_affine` | `RHTower/Sieve/DirichletPolyAffineMeanSquare.lean` |

## Gallagher's dyadic tail: the last logarithm

`GallagherDyadicTail.gallagher_split_integral_dyadic` already takes the affine majorant `α·T + β` of the
frequency mean square as a hypothesis, so it inherits the improvement directly. Its previous instance
used `α = 2∑|a_m|²`, `β = (4N(1 + log N)/π)∑|a_m|²`; the affine one gives

`α = (5π/2)∑_m|a_{m+1}|²`,  `β = (5e/2)∑_m(m+1)|a_{m+1}|² + (5/4)∑_m|a_{m+1}|²`

(`gallagher_meanValue_dyadic_le_affine`, with the majorant form
`integral_Icc_normSq_logPoly_le_affine_majorant` obtained from `max(2πT,1) ≤ 2πT + 1`, so no condition
on `W` beyond positivity is needed).

Balancing over `W` turns `α·δ + β·δ²` into the two contributions, so for coefficients bounded by `1` on
`[1,N]` the bound is `≍ δN + δ²N²` where the previous instance gave `≍ δN + δ²N²log N`. Against the
trivial `δ(∑|a_n|)² ≍ δN²`, the old form was an improvement only for `δ ≪ 1/log N`; the affine form is
an improvement for every `δ ≪ 1`. That logarithm was the one the dyadic tail had left behind.

## Large values: where the discretisation earns its keep

For *counting* large values the discrete estimate is the right tool, and it too was carrying the lossy
factor. Its proof — Gallagher's reduction of the discrete sum to `∫‖F‖²` and `∫2‖F‖‖F'‖`, then the AM–GM
split at the balancing parameter `log N` — uses nothing about the two energies beyond their values, so
it is now stated with them as parameters (`largeValues_dirPoly_of_energy`):

`∑_{r ≤ R}‖F(λ_r)‖² ≤ δ^{-1}E + (log N)E + (log N)^{-1}E'`   for `∫_0^T‖F‖² ≤ E`, `∫_0^T‖F'‖² ≤ E'`.

`largeValues_dirPoly` is its instance at the mean value theorem's energies; the affine instance
(`largeValues_dirPoly_affine`) gives

`∑_{r ≤ R}‖F(λ_r)‖² ≤ (δ^{-1} + 2 log N)(5πe∑_m(m+1)|a_m|² + (5π/2)(∑_m|a_m|²)max(T,1))`,

using `∑_m(m+1)‖(dirDerivCoeff a)_m‖² ≤ (log N)²∑_m(m+1)|a_m|²`
(`sum_mul_normSq_dirDerivCoeff_le`, the `n`-weighted companion of the existing plain-mass bound). So the
whole large-values chain — count, measure, Halász mean value — now runs on the `n`-weighted mass.

## The count and the first moment need only the bound

`card_largeValues_le` and `sum_norm_dirPoly_le_sqrt` carried six hypotheses each — `2 ≤ N`, `0 < δ`,
`0 ≤ T`, the gap condition, and the two endpoint conditions — none of which their proofs use: those
hypotheses exist only to produce the discrete mean-square bound. Stated with the bound as a parameter,

* `card_largeValues_le_of_bound` — `(R+1)V² ≤ B` from `∀ r, V ≤ ‖F(λ_r)‖` and `∑_r‖F(λ_r)‖² ≤ B`;
* `sum_norm_dirPoly_le_sqrt_of_bound` — `∑_r‖F(λ_r)‖ ≤ √((R+1)B)` from `∑_r‖F(λ_r)‖² ≤ B`;

each keeps one hypothesis. The originals are the instances at the mean value theorem, and
`card_largeValues_le_affine` / `sum_norm_dirPoly_le_sqrt_affine` are the instances at the affine mean
square. Nothing downstream changed statement.

## The symmetric range, which is the one Gallagher needs

Gallagher's identity integrates over `|w| ≤ W`, so the level-set measure has to be available there.
`volume_largeValues_symm_le` and its sixth-power form both consumed the lossy symmetric mean square;
Chebyshev uses nothing but a bound, so they are now instances of

* `volume_largeValues_symm_le_of_bound` — `V²·|{t ∈ [-T,T] : V ≤ ‖F(t)‖}| ≤ B` from
  `∫_{[-T,T]}‖F‖² ≤ B`;
* `volume_largeValues_sixth_symm_le_of_bound` — the same with `V⁶` from a mean-square bound for the
  cube,

and both shed the hypothesis `0 ≤ T`, which neither proof used. The affine instance
(`volume_largeValues_symm_le_affine`) needs no hypothesis on `T` at all.

## Prime support: the `n`-weighted mass is a constant

For a weight supported on the primes of `[1,M]` with `‖a_k‖ ≤ A log k`, *both* masses of the affine mean
square are prime sums the dyadic Chebyshev cap bounds independently of `M`:

`∑_p p^{-2σ}(log p)² ≤ cap(2σ)`,   `∑_p p·p^{-2σ}(log p)² = ∑_p p^{-(2σ-1)}(log p)² ≤ cap(2σ-1)`,

the second needing only `σ > 1` — the very hypothesis the prime routes already carry. Cauchy–Schwarz
then gives

`∫_{|y| ≤ T}‖L(a,σ+iy)‖dy ≤ √(2T(5πe·A²·cap(2σ−1) + (5π/2)·A²·cap(2σ)·T))`

(`integral_Icc_norm_LSeries_prime_le_affine`), where `GhsInnerFirstMoment.integral_norm_LSeries_prime_le`
carries `M(1 + log M)` inside the root. So for prime-supported weights — the ones the GHS and Halász
routes actually use — the improvement is a factor `√(M log M)` throughout the range `T ≤ M log M`, not
merely a logarithm. That is the sharpest consequence of the whole sweep.

| Statement | Module |
|---|---|
| `rpow_neg_sq_eq`, `mul_rpow_neg_sq_eq` | `RHTower/Sieve/PrimeAffineFirstMoment.lean` |
| `generalMeanSquareRate_prime_le`, `generalMeanSquareConst_prime_le` | `RHTower/Sieve/PrimeAffineFirstMoment.lean` |
| `integral_Icc_norm_LSeries_prime_le_affine` | `RHTower/Sieve/PrimeAffineFirstMoment.lean` |
