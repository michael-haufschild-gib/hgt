# The Sibuya–Ramis tower for ht card 3 — what is built and what the next brick is

Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity` has ONE open item: the
Sibuya–Ramis exact Newton-slope theorem.  `(4)`–`(6)` are closed at every genus (see
`mem:ht-cards/session-2026-08-14-closures`).

## Built (all wired, axiom-clean)

| module | content |
|---|---|
| `HTGeometry/GevreyFormalSeries` | `IsGevreySeries r F` (`‖aₙ‖ ≤ C Aⁿ (n!)^r`); mono, `C`, add, **mul**, **derivativeFun**; bridge to the sequence notion; `barnesTailSeries s` with **exact order `s`** for irrational `s` |
| `HTGeometry/FormalAnalyticADE` | pow/sum/prod closure, `IsGevreySeries.iterate_derivative`, `IsAnalyticDifferentialPolynomial`, `IsFormalAnalyticADESolution`, `isGevreySeries_aeval_of_analytic`, the `SibuyaRamisRationalExactOrder` interface and the consequence for `barnesTailSeries` |
| `HTGeometry/FormalEulerOperator` | `eulerOp` (`θ = t d/dt`), `eulerLinearOp`, **`shiftPolynomial B μ`**, `coeff_eulerLinearOp` (the convolution), **`shiftPolynomial_zero_mul_coeff`** (the recursion) |
| `HTGeometry/ShiftPolynomialBounds` | `exists_lower_bound_eval_natCast` (nonzero polynomial ≥ `c(n+1)^deg` on ℕ), `exists_bound_shiftPolynomial` (`‖Φ_μ(k)‖ ≤ C ρ^μ (k+1)^m`) |
| `HTGeometry/MailletLinearGevrey` | `factorial_ratio_le`, **`shiftFactor_le`** (`(k+1)^m (k!/n!)^r ≤ (n+1)^d`, `r = m-d`), `geom_shift_sum_le`, **`isGevreySeries_of_eulerLinearOp_eq` = MAILLET, linear case** |

## The proof idea that made Maillet short

In the Euler basis `L = ∑ B_j θ^j` acts on coefficients by ONE convolution,
`coeff_n(LF) = ∑_{i+k=n} Φ_i(k) f_k`.  Divide by `Φ_0(n) ≳ c(n+1)^d`.  Each term of the tail is
`≤ Cb ρ^{n-k}(k+1)^m · C A^k (k!)^r`, and the whole shift factor collapses:
`(k+1)^m (k!/n!)^r ≤ n^m·n^{-r} ≤ n^d ≤ (n+1)^d` for `k < n`, using only `k+1 ≤ n` and
`k!/n! ≤ 1/n`.  So the tail is `(n+1)^d` times a geometric series in `ρ/A`, which a large `A` kills.
No split of the summation range is needed.

## Next bricks

1. **Nonlinear Maillet.**  Linearize at a TRUNCATION `F_N` of the formal solution (not at `F`): the
   coefficients of that linearization are polynomials, hence convergent, so the linear theorem
   applies.  Substituting `F = F_N + t^{N+1}H` turns the ADE into `L_N H + (quadratic in H) = -R_N`
   with `R_N` convergent; for `N` large the quadratic part does not change the recursion's dominant
   balance.
2. **The sharp half (the real Sibuya–Ramis).**  The exact order is one of the slope ratios, not just
   below the largest.  Routes: Malgrange's index theorem for `L` on Gevrey spaces plus a nonlinear
   fixed point; or the Levelt–Turrittin formal classification (exponential parts of a formal linear
   ODE are ramified by an INTEGER, so the exponential scales `x^{1/s}` of the Stokes jump force
   `1/s ∈ ℚ`).  Both are mathlib-scale.

An upper bound alone is NOT enough: a series of exact irrational order lies in every larger rational
Gevrey class.
