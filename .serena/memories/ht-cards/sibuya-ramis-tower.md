# The Sibuya–Ramis tower for ht card 3 — built layers and the roadmap

Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity` has ONE open item: the
Sibuya–Ramis exact Newton-slope theorem.  `(4)`–`(6)` are closed at every genus (see
`mem:ht-cards/session-2026-08-14-closures`).

## Built (all wired, axiom-clean)

| module | content |
|---|---|
| `HTGeometry/GevreyFormalSeries` | `IsGevreySeries r F` (`‖aₙ‖ ≤ C Aⁿ (n!)^r`); mono, `C`, add, **mul**, **derivativeFun**; bridge to the sequence notion; `barnesTailSeries s` with **exact order `s`** for irrational `s` |
| `HTGeometry/FormalAnalyticADE` | pow/sum/prod closure, `iterate_derivative`, `IsAnalyticDifferentialPolynomial`, `IsFormalAnalyticADESolution`, `isGevreySeries_aeval_of_analytic`, the `SibuyaRamisRationalExactOrder` interface + its consequence for `barnesTailSeries` |
| `HTGeometry/FormalEulerOperator` | `eulerOp` (`θ = t d/dt`), `eulerLinearOp`, **`shiftPolynomial B μ`**, `coeff_eulerLinearOp` (one convolution), **`shiftPolynomial_zero_mul_coeff`** (the recursion) |
| `HTGeometry/ShiftPolynomialBounds` | `exists_lower_bound_eval_natCast`; `exists_bound_shiftPolynomial` (uniform); **`exists_bound_shiftPolynomial_newton`** (`‖Φ_μ(k)‖ ≤ Cρ^μ(k+1)^{d+rμ}` under the polygon condition) |
| `HTGeometry/MailletLinearGevrey` | `factorial_ratio_le`, `pow_succ_mul_factorial_le_factorial`, `shiftFactor_le`, **`shiftFactor_newton_le`**, `geom_shift_sum_le`, **`isGevreySeries_of_eulerLinearOp_eq`** (crude Maillet, order `m - deg Φ₀`), **`isGevreySeries_of_eulerLinearOp_eq_newton`** (sharp upper bound from the polygon), **`isGevreySeries_zero_of_eulerLinearOp_eq`** (no positive slope ⟹ convergent) |

## Two proof ideas worth keeping

1. In the Euler basis `L = ∑ B_j θ^j` acts on coefficients by ONE convolution,
   `coeff_n(LF) = ∑_{i+k=n} Φ_i(k) f_k`.
2. The shift factor collapses with no case analysis:
   `k!/n! ≤ (k+1)^{-(n-k)}` (the `n-k` factors of `n!/k!` are each `≥ k+1`), so under the polygon
   condition `j ≤ d + rμ`, `(k+1)^{d+r(n-k)}(k!/n!)^r ≤ (k+1)^d ≤ (n+1)^d`.

## Roadmap for the remaining (sharp lower) half

The exact order must be `0` or a slope ratio.  Structure of the classical argument, in the shape the
built layers can consume:

1. **Newton factorization** `L = L_< · L_≥` over `ℂ[[t]][θ]`, splitting the ratios at a chosen
   `r_i < s < r_{i+1}`.  Purely algebraic; obtained by an iteration in the operator ring.
2. `G := L_≥ F` solves `L_< G = 0`, so `G` is Gevrey of order `r_i`
   (**already available**: `isGevreySeries_of_eulerLinearOp_eq_newton`).
3. **Surjectivity**: `L_≥` maps `ℂ[[t]]_{r_i}` onto itself when all its ratios exceed `r_i`.  This is
   the analytic core; the recursion is driven by the TOP shift rather than by `Φ_0`, so it needs a
   "reverse" version of the built recursion.
4. Then `F - F' ∈ ker L_≥` for some `F' ∈ ℂ[[t]]_{r_i}`, and an induction on the number of slopes
   shows kernel elements have order among the ratios of `L_≥`.  Hence the exact order of `F` is
   never strictly between two consecutive ratios.

Also still open: the **nonlinear reduction** (linearize at a truncation `F_N` of the solution — its
coefficients are polynomials, hence convergent, so the linear theorems apply; the quadratic remainder
needs a majorant estimate).

A counterexample to keep in mind: the Euler equation `tθF + F = t` has a divergent solution with
convergent right-hand side, so "`L` with positive slopes is invertible on Gevrey-`0`" is FALSE — the
kernel is what makes step 4 necessary.
