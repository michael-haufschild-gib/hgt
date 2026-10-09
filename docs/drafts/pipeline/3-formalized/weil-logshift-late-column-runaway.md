# Every sufficiently late fixed inverse column runs away

Status: formalised and audited, 2026-10-09. Local Lean corpus only. Global lint has six unrelated import-reachability errors, recorded below.

## Exact result

There exists a natural threshold K such that, for every fixed history coordinate k>=K and every real shift y,

`|weilLogShiftRecoveryMomentResponse y n k| -> infinity` as n->infinity.

Consequently, every such fixed response column is nonsummable at every real shift. This is a statement about each fixed column; it does not follow merely from the previously proved growth of the moving inverse diagonal.

Write g(k,n)=Inv(unit(k))(n)-Inv(0)(n). A stronger coefficient comparison is proved: one can choose K>=625 such that for every k>=K and k+2<=j<=n,

`exp((j+1)*(n-j))*|g(k,j)| <= |g(k,n)|`.

The seed is exactly g(k,k+2)=1/W(k+2,k+2)>0. Hence each such column has a positive exponential lower envelope with rate k+3.

## Dependency-closed argument

1. On a central interval where the two opposite smooth cutoff factors equal1, retain only the two facing factors. The elementary bound S(a)>=exp(-1/a)/2 yields an explicit two-edge lower bound for truncated autocorrelation.
2. Extend the existing edge upper estimate to every reciprocal overlap scale. For every 0<a<pi, obtain C>0 with |W(n,j)|<=C*exp(-a*j-4*j/(n+1-j)) throughout 2<=j<=n.
3. The first subdiagonal has exactly one surviving truncated-kernel term. Integrating over a shrinking central interval gives A/(n+1)^2 times exp(-(pi+20/9)*(n+1)) as a positive lower envelope for W(n+1,n). Every strict rate b>pi+20/9 absorbs the quadratic prefactor.
4. Choose a=99*pi/100, b=pi+9/4. The exact exponent gap for j>=625 bounds each older damped entry by one row-length share of half the adjacent entry, uniformly beyond a common threshold. Independently, W(n+1,n)>=2*exp(n+1)*W(n+1,n+1) eventually.
5. The impulse column has zero coefficients before its seed, a positive seed, and homogeneous triangular equations in later rows. Sum the older-entry bound using cardinality<=n+1. Reverse triangle inequality and the adjacent amplification force |g(k,n+1)|>=exp(n+1)*|g(k,n)|. Induction proves the two-index comparison above.
6. Every real-shift critical kernel rate is below 2*pi+1, while the column rate k+3 is much larger. The native paired-kernel lower envelope and sqrt(n)<=n+1 give a positive exponential-over-linear lower envelope for the absolute moment response. It tends to infinity; summability would force the terms to zero.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/WeilLogShiftTwoEdgeLower.lean`: three public transition/central lower bounds.
- `formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryRowBounds.lean`: five public full-row bounds and exponent comparison.
- `formal/GaloisForLFunctions/RHTower/WeilLogShiftSubdiagonalAmplification.lean`: five public adjacent-envelope, amplification and older-tail domination theorems.
- `formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryColumns.lean`: centered coefficient-column definition and six exact seed/recurrence/normalization theorems.
- `formal/GaloisForLFunctions/RHTower/WeilLogShiftLateColumnRunaway.lean`: four public growth, fixed-column runaway and nonsummability theorems; one private finite-tail estimate.

Main APIs:

- `exists_weilLogShiftRecoveryCoefficientColumn_growth`
- `exists_weilLogShiftRecoveryCoefficientColumn_exponential_lower`
- `exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway`
- `exists_weilLogShiftRecoveryMomentResponse_fixed_column_not_summable`

## Verification

- All five final leaves compiled/exported with `lake --old env lean <leaf> -o <object>`; exit0 and no diagnostics on final source versions.
- All 23 public theorem axiom sets checked exhaustively in a /tmp scratch: exactly `[propext, Classical.choice, Quot.sound]`; audit exit0 without diagnostics. The private tail estimate is transitively covered.
- Five unique umbrella imports; scoped source-gap, raised-limit and whitespace checks passed. Exported objects are newer than final sources; source hashes match the audit manifest.
- Index refresh exit0: five changed modules, none removed. All 24 public API rows checked for exact kind, module, source path and line, without duplicates.
- Global lint exit1 solely for six unrelated unreachable modules: `RHTower.HorizontalIsolationCrossPairDecay`; `HTGeometry.PaperFrameDualNumberBoundary`, `PaperOriginalDiscreteValuation`, `PaperOriginalValuation`, `PaperSL2PolynomialLift`, `QKrawtchoukCompanionWeakLimit`. No diagnostic names an affected leaf. Unrelated files were not changed.
- All owned jobs terminal; all ten explicit scratch/log/manifest files removed and absence verified. Final source hashes and unique imports rechecked before cleanup.

## Limits and continuation

K is existential, with a proved lower bound in the growth theorem; no claim that K=625. Coordinate-zero response remains open. No conclusion is asserted for every early column.

The arbitrary-precision, single-coordinate payoff is now formalised and audited in `docs/drafts/pipeline/3-formalized/weil-logshift-arbitrary-precision-impulse.md`: at most one exceptional amplitude on each late impulse line, then strictly upward single-error witnesses preserving any finite prefix and every other observation under every positive error envelope. Genericity for arbitrary envelopes is the next open extension.

Further exposed strengthening targets: strict alternating signs and a quadratic-exponent coefficient lower bound. Neither is currently claimed as proved.
