# Adjacent arithmetic cancellation and cubic Gram cost

Status: FORMALIZED. Paper argument and exact Lean receivers are verified.
Evidence: local Lean corpus only. No web, papers, or numerics.

## Conjecture

For adjacent arithmetic indices n,n+1 (n≥2), the coefficient direction (1,-1)
forces every normalized finite Gram certificate to have cost at least c n³.
For one common cost normalization, singleton certificates retain quadratic
upper cost. Thus clustering logarithmic shifts creates an extra conditioning
loss beyond the singleton transport cost.

## Local ingredients audited

- RiemannKernelCuspSeries: hasDerivAt_riemannKernelDeriv,
  riemannKernelDeriv_zero, and the real cusp-series representation.
- WeilWorkExposingRayDifferentialParity:
  ExposingRayDifferential.kernel_derivative_upper_subcritical, all derivative
  orders, with envelope B exp(-a exp(2|x|)) exp(-|x|), for 0<a<π.
- WeilFullConeMinorantRigidity: integral definition of riemannAutocorr and
  integrable_riemannKernelReal_mul.
- WeilLogShiftFiniteGramCostGrowth: normalized certificate and signed witness
  cost argument.
- WeilLogShiftSingletonGramCost: two singleton tests with uniform quadratic cost.

## Paper proof

Choose a=1 in the derivative envelope. Since exp(2r)≥2r for r≥0, derivative
orders zero and one have bounds C exp(-3|x|), D exp(-3|x|).
The real kernel inherits its derivative from the complex cusp-series kernel.
For |h|≤1, every point between x and x+h has absolute value at least |x|-1.
The mean value inequality yields
|Phi(x+h)-Phi(x)| ≤ D exp(3) exp(-3|x|) |h|.

Subtract the two absolutely convergent autocorrelation integrals. The product
bound and |y|≤|t|+|t-y| give
|K(y+h)-K(y)| ≤ E |h| exp(-2|y|),
where E=C D exp(3) times the finite integral of exp(-|t|).
A harmless positive enlargement of E avoids proving a sharp integral constant.
This statement requires |h|≤1, a condition discharged for the native log gap.

Let delta=log(n+1)-log(n). Then 0≤delta≤1/n≤1. Apply the preceding bound at
y+log(n) with h=delta, and at y-log(n) with h=-delta. The triangle inequality
|log(n)|≤|y|+|y±log(n)| yields
|P_(n+1)(y)-P_n(y)| ≤ 2E exp(2|y|) n^(-3).

On support {k,k+1}, n=k+2, the coefficient vector (1,-1) has norm one and
potential P_n-P_(n+1). Finite-sum triangle inequalities bound every Gram form
by its cost (with B=2E, enlarged positive if needed) times n^(-3).
A normalized certificate supplies distinct tests for this vector and its negative;
each costs more than n³. Sum nonnegativity then gives total cost >2n³.

Cost is linear in its positive normalization B. Rescaling this cubic bound to
the B supplied by the singleton theorem gives a common metric with quadratic
singleton upper cost and cubic adjacent-pair lower cost.

No new analytic hypothesis is used. Constants need not be optimal. No cubic
upper bound for adjacent pairs is claimed; that remains a separate question.

## Work plan

1. Formalize local exponential translation bound for the actual autocorrelation.
2. Specialize to adjacent logarithms and certify the cubic cost obstruction.
3. Wire leaves; native Lean audits; all public-declaration axiom audit; index; lint.

The full research goal remains active.


## Verified result — 2026-10-09

All three work-plan steps are complete. Two new leaves:
- formal/GaloisForLFunctions/RHTower/RiemannAutocorrWeightedTranslation.lean
- formal/GaloisForLFunctions/RHTower/WeilLogShiftAdjacentGramCost.lean

Public declarations, all verified:
1. exists_riemannKernelDeriv_cubic_exp_envelope
2. exists_riemannKernelReal_translation_envelope
3. exists_riemannAutocorr_translation_envelope
4. exists_pairedLogKernel_adjacent_inverseCube_envelope
5. exists_adjacentWeilGram_cubic_cost_lower_bound
6. exists_singleton_adjacentWeilGram_cost_separation

The final receiver supplies B,C,D>0 in one common cost metric: every index
k has an exactly-two-test singleton certificate costing at most C(k+2)²,
whereas every certificate on {k,k+1} costs more than D(k+2)³.
This is a proved cubic LOWER bound for adjacent pairs; no matching adjacent
upper bound or optimal constant is asserted. Finite certificate existence is
already supplied for every support by the imported corpus theorem.

New insight: resolving two nearby logarithmic shifts imposes an additional
conditioning loss beyond the quadratic singleton cost, even with only two
arithmetic coefficients. The positive analytic ingredient is the decaying
translation modulus of the actual Riemann autocorrelation, proved from actual
cusp-series derivatives without new analytic hypotheses.

Verification:
- Both native leaf compilations exit 0 with no diagnostics.
- All six public declarations depend exactly on propext, Classical.choice,
  Quot.sound; no new axioms, admissions, or analytic premises.
- Scratch mathlib API checks, including explicit have := @Name terms, pass.
- Both leaves and direct dependencies have current olean artifacts.
- Both leaves wired into RHTower umbrella; index refresh exits 0.
- Authoritative lint exits 1 only for eight unrelated umbrella reachability
  errors: RHTower.RepPointPairEigen, RepPointPairLaplacian, RepPointPairOperator,
  RepPointPairRegularity, RepPointPairSymmetry; HTGeometry.PaperIntegralAntisymmetrization,
  PaperUniversalVandermondeRegular, QKrawtchoukCompanionTriangular.
- No owned jobs remain running. No full builds, web, external papers, or numerics.

Audit files: /tmp/hgt-adjacent-translation-build.log,
/tmp/hgt-adjacent-cost-build.log, /tmp/hgt-adjacent-final-audit.log,
/tmp/hgt-adjacent-final-api.log, /tmp/hgt-adjacent-cost-index.log,
/tmp/hgt-adjacent-cost-lint.log.

## Next conjecture

Is the cubic lower rate sharp for adjacent supports? A possible upper construction
uses two moving sampling offsets where K and its derivative give an invertible
two-row response, followed by signed two-point Gram tests. This requires a
uniform lower determinant estimate as the logarithmic gap shrinks; it is NOT
proved by the current corpus results inspected here. Audit local Lean before
adopting any determinant or regularity premise. Alternatively, expose the general
logarithmic-gap lower bound already suggested by the translation modulus, then
transport certificates along inclusions of finite supports.

Full research goal remains active; this completes one mathematical increment.
