# The Sibuya–Ramis tower for ht card 3 — built layers and the roadmap

Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity` has ONE open item: the
Sibuya–Ramis exact Newton-slope theorem.  `(4)`–`(6)` are closed at every genus (see
`mem:ht-cards/session-2026-08-14-closures`).

## Built (all wired, axiom-clean)

| module | content |
|---|---|
| `HTGeometry/GevreyFormalSeries` | `IsGevreySeries r F`; mono, `C`, add, **mul** (via the quantitative `norm_coeff_mul_le`), **derivativeFun**; bridge to the sequence notion; `barnesTailSeries s` with **exact order `s`** for irrational `s` |
| `HTGeometry/FormalAnalyticADE` | closure lemmas, `IsAnalyticDifferentialPolynomial`, `isGevreySeries_aeval_of_analytic`, the `SibuyaRamisRationalExactOrder` interface + its consequence for `barnesTailSeries` |
| `HTGeometry/FormalEulerOperator` | `eulerOp`, `eulerLinearOp`, **`shiftPolynomial B μ`**, `coeff_eulerLinearOp`, **`shiftPolynomial_zero_mul_coeff`** (the recursion) |
| `HTGeometry/ShiftPolynomialBounds` | `exists_lower_bound_eval_natCast`; `exists_bound_shiftPolynomial`; **`exists_bound_shiftPolynomial_newton`** |
| `HTGeometry/MailletLinearGevrey` | `shiftFactor_le`, **`shiftFactor_newton_le`**, `geom_shift_sum_le`, **`isGevreySeries_of_eulerLinearOp_eq`** (Maillet), **`…_newton`**, **`isGevreySeries_zero_of_eulerLinearOp_eq`** |
| `HTGeometry/NewtonBoundRational` | **`exists_rat_least_newtonBound`**, `exists_rat_isGevreySeries_of_eulerLinearOp_eq`, `exactOrder_le_rat_of_eulerLinearOp_eq` |
| `HTGeometry/EulerADELinearization` | `eulerJetVector`, `IsFormalEulerADESolution`, `linearizationCoeff`, **`aeval_eulerJetVector_add`**, `taylorDefect_mem_sq_X_pow`, `eulerLinearOp_linearization_eq` |
| `HTGeometry/EulerADETruncation` | `truncSeries`, `isGevreySeries_zero_truncSeries`, `X_pow_dvd_sub_truncSeries`, `isGevreySeries_aeval_eulerJetVector`, **`isGevreySeries_zero_linearizationCoeff`**, **`X_pow_dvd_aeval_truncSeries`** |
| `HTGeometry/MvPolynomialQuadraticDefect` | **`exists_taylorDefect_repr`** — `defect = ∑_{a,b} L_a L_b Q_{ab}(S,L)`, the quantitative form of the corpus's `taylorDefect_mem_sq` |

## Corpus pieces to REUSE (do not rebuild)

`JacobianDomainCriterion.algebraicIndependent_of_domain_jacobian`;
`MvPolynomialFirstOrderTaylor` (`taylorDefect`, `taylorDefect_mem_sq`, `taylorDefect_mul_X`,
`aeval_add_eq_add_sum_pderiv_mod_sq`).  See `mem:corpus-search-before-building`.

## Ideas worth keeping

1. In the Euler basis `L = ∑ B_j θ^j` the operator acts on coefficients by ONE convolution,
   `coeff_n(LF) = ∑_{i+k=n} Φ_i(k) f_k`.
2. `k!/n! ≤ (k+1)^{-(n-k)}`, so under the polygon condition `j ≤ d + rμ`,
   `(k+1)^{d+r(n-k)}(k!/n!)^r ≤ (k+1)^d ≤ (n+1)^d` — no case analysis.
3. **Use the EULER basis, not `d/dt`**: `θ` preserves the order of a series, so a perturbation and
   all of its jets stay divisible by the same power of `t`.

## Remaining

### A. Nonlinear Maillet — only the final quantitative induction is left
For each `N`: `L_N(H) = -P(jets F_N) - defect`, with `L_N` convergent, `P(jets F_N)` convergent of
order `≥ N+1`, and `defect = ∑ L_a L_b Q_{ab}` of order `≥ 2N+2`.  NEXT BRICK: a Gevrey predicate
with EXPLICIT constants (`GevreyBound C A r F`) so the defect's constant can be seen to carry `C_H²`;
then the strong induction of `isGevreySeries_of_eulerLinearOp_eq` with the defect as an extra term,
`N` chosen so large that `C_H ≤ 1` and the forcing term is small.

### B. The sharp lower half (the real Sibuya–Ramis)
1. Newton factorization `L = L_< · L_≥` over `ℂ[[t]][θ]`.
2. `G := L_≥ F` solves `L_< G = 0`, so `G` is Gevrey of order `r_i` (**available**).
3. A REVERSE recursion (driven by the top shift): if all ratios of `L` exceed `s'`, then
   `LF ∈ ℂ[[t]]_{s'}` and `F ∈ ℂ[[t]]_s` force `F ∈ ℂ[[t]]_{s'}`.
4. Induction on the number of slopes confines the exact order to `{0} ∪ {ratios}`.

Counterexample: `tθF + F = t` has a divergent solution with convergent right-hand side, so an
operator with positive slopes is NOT invertible on Gevrey-`0`; step 3 must be a quotient statement.
