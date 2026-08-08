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
