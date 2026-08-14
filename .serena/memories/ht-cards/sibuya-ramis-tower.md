# The Sibuya–Ramis tower for ht card 3 — built layers and the roadmap

Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity` has ONE open item: the
Sibuya–Ramis exact Newton-slope theorem.  `(4)`–`(6)` are closed at every genus (see
`mem:ht-cards/session-2026-08-14-closures`).

## Built (all wired, axiom-clean)

| module | content |
|---|---|
| `HTGeometry/GevreyFormalSeries` | `IsGevreySeries r F`; mono, `C`, add, **mul** (via the quantitative `norm_coeff_mul_le`), **derivativeFun**; bridge to the sequence notion; `barnesTailSeries s` with **exact order `s`** for irrational `s` |
| `HTGeometry/FormalAnalyticADE` | pow/sum/prod closure, `IsAnalyticDifferentialPolynomial`, `isGevreySeries_aeval_of_analytic`, the `SibuyaRamisRationalExactOrder` interface + its consequence for `barnesTailSeries` |
| `HTGeometry/FormalEulerOperator` | `eulerOp`, `eulerLinearOp`, **`shiftPolynomial B μ`**, `coeff_eulerLinearOp` (one convolution), **`shiftPolynomial_zero_mul_coeff`** (the recursion) |
| `HTGeometry/ShiftPolynomialBounds` | `exists_lower_bound_eval_natCast`; `exists_bound_shiftPolynomial`; **`exists_bound_shiftPolynomial_newton`** |
| `HTGeometry/MailletLinearGevrey` | `shiftFactor_le`, **`shiftFactor_newton_le`**, `geom_shift_sum_le`, **`isGevreySeries_of_eulerLinearOp_eq`** (Maillet), **`…_newton`** (sharp upper bound), **`isGevreySeries_zero_of_eulerLinearOp_eq`** (no positive slope ⟹ convergent) |
| `HTGeometry/NewtonBoundRational` | `NewtonBoundedBy`, **`exists_rat_least_newtonBound`** (the least level is RATIONAL and least), `exists_rat_isGevreySeries_of_eulerLinearOp_eq`, `exactOrder_le_rat_of_eulerLinearOp_eq` |
| `HTGeometry/EulerADELinearization` | `eulerJetVector`, `IsFormalEulerADESolution`, `linearizationCoeff`, **`aeval_eulerJetVector_add`** (`P(jets(Y+H)) = P(jets Y) + L_Y H + defect`), `taylorDefect_mem_sq_X_pow`, `eulerLinearOp_linearization_eq` |
| `HTGeometry/EulerADETruncation` | `truncSeries`, `isGevreySeries_zero_truncSeries`, `X_pow_dvd_sub_truncSeries`, `isGevreySeries_aeval_eulerJetVector`, `isAnalyticDifferentialPolynomial_pderiv`, **`isGevreySeries_zero_linearizationCoeff`**, **`X_pow_dvd_aeval_truncSeries`** |

## Corpus pieces to REUSE (do not rebuild)

- `HTGeometry/JacobianDomainCriterion.algebraicIndependent_of_domain_jacobian`
- `HTGeometry/MvPolynomialFirstOrderTaylor`: `taylorDefect`, **`taylorDefect_mem_sq`**,
  `aeval_add_eq_add_sum_pderiv_mod_sq`.  I duplicated this once — see
  `mem:corpus-search-before-building`.

## Ideas worth keeping

1. In the Euler basis `L = ∑ B_j θ^j` the operator acts on coefficients by ONE convolution,
   `coeff_n(LF) = ∑_{i+k=n} Φ_i(k) f_k`.
2. The shift factor collapses with no case analysis: `k!/n! ≤ (k+1)^{-(n-k)}`, so under the polygon
   condition `j ≤ d + rμ`, `(k+1)^{d+r(n-k)}(k!/n!)^r ≤ (k+1)^d ≤ (n+1)^d`.
3. **Use the EULER basis, not `d/dt`**: `θ` preserves the order of a series, so a perturbation and
   all its jets stay divisible by the same power of `t`.  That is what makes the truncation
   reduction work.

## Remaining

### A. Nonlinear Maillet — only the final induction is left
For each `N`, `L_N(H) = -P(jets F_N) - defect` with `L_N` convergent (`isGevreySeries_zero_…`),
`P(jets F_N)` convergent of order `≥ N+1` (`X_pow_dvd_aeval_truncSeries`), and the defect of order
`≥ 2N+2`, so its level-`n` coefficient involves only `H` below level `n-N`.  The strong induction of
`isGevreySeries_of_eulerLinearOp_eq` then applies once the quadratic constant `C²` is beaten — which
is where `N` is chosen large, the forcing term being `O(t^{N+1})`.

### B. The sharp lower half (the real Sibuya–Ramis)
1. Newton factorization `L = L_< · L_≥` over `ℂ[[t]][θ]` splitting the ratios at `r_i < s < r_{i+1}`.
2. `G := L_≥ F` solves `L_< G = 0`, so `G` is Gevrey of order `r_i` (**available**).
3. A REVERSE recursion (driven by the top shift, not by `Φ_0`): if all ratios of `L` exceed `s'`,
   then `LF ∈ ℂ[[t]]_{s'}` and `F ∈ ℂ[[t]]_s` force `F ∈ ℂ[[t]]_{s'}`.
4. Induction on the number of slopes confines the exact order to `{0} ∪ {ratios}`.

Counterexample to keep in mind: `tθF + F = t` has a divergent solution with convergent right-hand
side, so an operator with positive slopes is NOT invertible on Gevrey-`0`; step 3 must be phrased on
the quotient.
