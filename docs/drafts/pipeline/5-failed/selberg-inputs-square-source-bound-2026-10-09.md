# Coarse Selberg inputs do not control square-source sums

Status: FAILED as an abstract discharge of the quadratic square-source bound.
Positive survivor: exact half-power classification, paper proof complete and formalized.
Date: 2026-10-09.

## Proposed deduction and obstruction

The square-source RH criterion requires a uniform upper bound B*N^2 for the sum
of psiRemainder(s^2), over 1 <= s < N. The attempted deduction was to obtain that
bound from the first and second coarse Selberg inequalities, possibly strengthened
by requiring the first Selberg response to be o(N).

This deduction fails for abstract remainder sequences. The existing tuned model
from PMSelbergSublinearPowerBoundary supplies 0 < c < 1 and

r(n) = c*n^(3/4) - (1+c)*1_{n=1}.

It has first Selberg response o(N), satisfies the first inequality with constant
400 and the second inequality with constants 800 and 2900, yet no B bounds its
square-source sum by B*N^2 for all N >= 2. The model is not the arithmetic
Chebyshev remainder. This does not refute RH and does not rule out using stronger
arithmetic identities.

## Exact positive survivor and paper proof

For every sigma > 0 and c > 0, the model
r(n) = c*n^sigma - (1+c)*1_{n=1}
has a quadratic upper bound for its square-source sum if and only if sigma <= 1/2.

For N >= 2 the sum is exactly
c*sum_{1 <= s < N} s^(2*sigma) - (1+c).
When sigma <= 1/2, s^(2*sigma) <= s for s >= 1, so the sum is bounded by c*N^2.
When sigma > 1/2, the dyadic block n <= s < 2n contributes at least
n*n^(2*sigma). A quadratic upper bound would force n^(2*sigma-1) to remain
bounded. Its exponent is positive, so it tends to infinity, a contradiction.
Positive scaling and the fixed endpoint correction preserve this classification.

This is the replacement boundary exposed by the obstruction: the abstract
Selberg response can be tuned to o(N) while the source power remains above the
critical half-power threshold. A source-specific argument must exclude that
possibility rather than infer exclusion from the response estimate alone.

## Lean status and verification

Module: formal/GaloisForLFunctions/RHTower/PMSelbergSquareSampleBoundary.lean.
Wired into formal/GaloisForLFunctions/RHTower.lean.

Six public theorems proved:

- pmSquarePowerSum_dyadic_lower
- pmSquarePowerSum_quadratic_upper_iff
- sum_pmScaledPowerRemainder_squares
- pmScaledPowerRemainder_squareSum_quadratic_upper_iff
- pmCancellingPower_no_squareSum_quadratic_upper
- exists_selberg_sublinear_squareSum_counterexample

Direct final leaf compilation with lake --old env lean and explicit output
artifact passed without diagnostics. All six public theorems passed a /tmp
#print axioms audit: propext, Classical.choice, Quot.sound only. Scoped whitespace
checks emitted no diagnostics. All three owned scratch files removed afterward.

Global formal lint exited 1 for ten unrelated unreachable modules:
RHTower.SincSeparatorContour, RHTower.SincSeparatorMellin,
RHTower.StretchedBoseDefect, RHTower.StretchedBoseSeparator,
HTGeometry.ApertureConeCalculus, HTGeometry.ApertureConeWinding,
HTGeometry.ApertureLogTranslation, HTGeometry.ApertureOpenHistoryIdeal,
HTGeometry.BoundaryCoronaCStarAlgebra, HTGeometry.ComplexRateGammaIntegral.
No diagnostic concerned this module.

Research reads used only Lean-corpus output from scripts/formal_tools.py research.
No numerical experiment was used. The main RH goal remains active and unresolved.
