# Actual Gauss–Mayer trace and the first periodic points

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [three approaches, A](argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual global determinant](../3-formalized/gauss-mayer-source-fredholm-determinant.md).

## Target

For the actual coefficient trace `t(w)=Σₖ Mₖₖ(w)` of the certified Mayer
realization, prove, when `Re w>0`, `w≠1`,

`t(w)=ζ(w)+Σₙ≥1 [aₙ^(−w)/(1+aₙ^(−2))−n^(−w)]`,

where `aₙ=(n+sqrt(n²+4))/2`. The inverse branch `z↦1/(n+z)` has the
positive fixed point `xₙ=aₙ⁻¹` and derivative `−aₙ⁻²` there.

Prove the corrected scalar series converges locally uniformly for
`Re w>−1`. Its sum plus `ζ(w)` then continues the actual first trace to
that larger half-plane, away from `w=1`.

## Proposed proof

The existing weighted-composition trace theorem evaluates each actual
branch trace at its fixed point. The constant projection has trace one.
To interchange the Cauchy diagonal sum and the regularized branch sum,
use the actual monomials. On `|z−1|≤1`,

`|(z−1)^k−(−1)^k|≤k|z|`.

Together with inverse-branch geometry and the principal-power estimates,
this gives a bound of the form

`|αₖ,R((branchₙ−n^(−w)P)eₖ)| ≤ R^(−k)(A(w)k+B(w)) n^(−Re w−1)`.

Both factors are summable. The branch fixed-point formula and Fubini then
identify the actual coefficient trace with the displayed scalar series.

For continuation, `n≤aₙ≤n+1/n` and `aₙ⁻¹≤1/n`. The weight difference
and the factor `(1+aₙ⁻²)⁻¹−1` give

`|aₙ^(−w)/(1+aₙ⁻²)−n^(−w)|≤C(w)n^(−Re w−2)`.

Uniform constants on compact parameter discs give normal convergence for
`Re w>−1`. No hypothetical trace formula is assumed.

## Corpus boundary

`HTGeometry/WeightedCompositionTrace.hasSum_coeff_diag` proves the exact
single-branch residue formula. `AnalyticMarkovTransferMatrix.itrace_mat`
handles finitely many branches; it does not discharge the countable Gauss
sum or its rank-one correction. Higher trace powers, primitive geodesic
coding and the Selberg/scattering identity remain further obligations.

No paper proof or Lean certificate is claimed yet.
