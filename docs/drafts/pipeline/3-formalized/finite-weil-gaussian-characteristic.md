# Gaussian characteristic functions for the joint edge/correction fluctuation

Status: in progress. Sources restricted to local Lean corpus and installed Lean dependencies.
Previous rank-one increment revalidated with no freshness/import issues.

Prior research: scoped WeilLogShift text search contains no characteristic-function or
Fourier law. The lexical binomial/characteristic search returned six unrelated algebraic
hits (characteristic radii, field characteristic, and Euler characteristic). The local
KroneckerFlowDensity cosine/binomial expansion supplies the finite proof pattern. Installed
Lean proves sinc continuity and the exponential limit from n*g(n) convergence. No external
paper or web source was read. The full probability-space central limit theorem was inspected
locally; the scalar cosine limit below avoids introducing unneeded probability-space data.

Conjecture: write n=r+1,k=2n²+t(r),m for the canonical edge law,E=sum m i,T for
the local log correction,Q=sum m T. For all real a,b,

sum_i m_i exp(I*[a(i-E)+bn(T_i-Q)]/sqrt(n)) -> exp(-(a+b)²/8).

This is a full joint characteristic-function limit with no analytic premises, strengthening
the already proved rank-one covariance limit. It does not by itself claim an implemented
weak-convergence theorem for a newly constructed measure type.

Dependency-closed paper argument:

1. The unit-circle phase has modulus one and |exp(ix)-exp(iy)|≤|x-y|, using the
   existing exact sine formula and |sin z|≤|z|. Weighted phase expectations inherit
   the corresponding L1 phase bound and the L1 weight bound.
2. Centered binomial characteristic functions are cos(u/2)^n by the binomial theorem.
   For fixed z, n(cos(z/sqrt(n))-1)=-(z²/2)*sinc(z/(2sqrt(n)))² for n>0. Sinc
   continuity and the existing (1+g(n))^n limit give exp(-z²/2). Therefore the
   binomial characteristic function at u=alpha/sqrt(n) tends to exp(-alpha²/8).
3. The midpoint/binomial L1 discrepancy tends to zero, so their characteristic
   functions have the same limit. The exact endpoint pairing changes centered edge
   position to midpoint position by only +/-1/2, giving phase error ≤|alpha|/(2sqrt(n)).
4. Actual centering differs from r/2 by at most 2, adding error ≤2|alpha|/sqrt(n).
5. The preceding residual theorem gives W=sum m[n(T-Q)-(i-E)]²≤1. Weighted
   Cauchy-Schwarz gives sum m|n(T-Q)-(i-E)|≤1. Replace the joint centered phase by
   (a+b)(i-E); error is at most |b|/sqrt(n), which vanishes. The stated limit follows.

Plan: phase estimates; scalar cosine Gaussian limit; binomial characteristic identity;
midpoint transfer; edge transfer and actual centering; joint transfer. Validate every leaf
individually, one owned foreground Lean process at a time, then audit every public declaration
and local API in a final native import. Wire finished leaves once, inspect freshness and all
incoming imports, index exact roots, run formal lint, and preserve unrelated concurrent work.

## Native checkpoint

All seven planned sources are authored: WeilLogShiftPhaseBounds, WeilLogShiftCosineGaussian,
WeilLogShiftBinomialCharacteristic, WeilLogShiftMidpointCharacteristic,
WeilLogShiftEdgeCharacteristic, WeilLogShiftCenteredCharacteristic,
WeilLogShiftJointCharacteristic. First three passed native Lean with empty logs. The
midpoint check was launched as session 38595; no dependent leaf has been launched yet.
Local API scratch `/tmp/hgt-gaussian-api.lean` passed 37 explicit API haves without warnings.
Final metadata/audit generator is `/tmp/hgt-gaussian-metadata.py` (expected 30 public
declarations). New leaves are not wired yet. Finish the remaining checks before wiring.


## Formalization completion — 2026-10-11

Current status: FORMALIZED. This record supersedes the initial status and the native checkpoint.
The conjectured full joint characteristic-function limit is proved for every real a,b and
every natural-valued offset t(r), with no analytic premises.

For n=r+1, k=2n²+t(r), the exact root is

sum_i m_i exp(I*[a(i-E)+bn(T_i-Q)]/sqrt(n)) -> exp(-(a+b)²/8).

Thus the complete joint phase law has the same Gaussian limit as the common scalar edge
fluctuation; the difference direction has limiting characteristic function identically one.
The result strengthens the preceding covariance and correlation limits. It is stated and
verified as convergence of explicit finite characteristic-function sums. Construction of
probability measures and a separate Lean weak-convergence theorem are not part of this claim.

Finite controls exposed by the proof:

- Unit-circle phase is 1-Lipschitz, and weight perturbations cost at most their L1 norm.
- Midpoint/edge characteristic difference is at most |u|/2 for every r,k,u.
- Actual edge centering costs at most |u|*|E-r/2|, hence at most 2|u| at quadratic starts.
- Centered residual first absolute moment is at most one under n²≤k+2, by weighted
  Cauchy-Schwarz and the preceding exact residual variance bound.
- Joint characteristic difference from the centered edge characteristic at
  (a+b)/sqrt(n) is at most |b|/sqrt(n).

The scalar Gaussian input is proved locally through the exact sinc identity and a verified
Lean exponential limit. No numerical computation, external paper, web lookup, new axiom,
heartbeat increase, full build, commit, or push was used.

Root declarations:
- `GaloisForLFunctions/RHTower/WeilLogShiftCosineGaussian.lean:9`: `tendsto_finiteWeil_inverse_sqrt`.
- `GaloisForLFunctions/RHTower/WeilLogShiftCosineGaussian.lean:29`: `tendsto_finiteWeil_cosine_gaussian`.
- `GaloisForLFunctions/RHTower/WeilLogShiftCosineGaussian.lean:53`: `tendsto_finiteWeil_inverse_sqrt_succ`.
- `GaloisForLFunctions/RHTower/WeilLogShiftBinomialCharacteristic.lean:34`: `tendsto_finiteWeilBinomialCharacteristic_gaussian`.
- `GaloisForLFunctions/RHTower/WeilLogShiftMidpointCharacteristic.lean:26`: `tendsto_finiteWeilCanonicalMidpointCharacteristic_gaussian`.
- `GaloisForLFunctions/RHTower/WeilLogShiftEdgeCharacteristic.lean:80`: `tendsto_finiteWeilCanonicalEdgeCharacteristic_gaussian`.
- `GaloisForLFunctions/RHTower/WeilLogShiftCenteredCharacteristic.lean:44`: `tendsto_finiteWeilCanonicalCenteredCharacteristic_gaussian`.
- `GaloisForLFunctions/RHTower/WeilLogShiftJointCharacteristic.lean:78`: `tendsto_finiteWeilCanonicalJointCharacteristic_gaussian`.

Validation: seven leaves, 30 public declarations (7 definitions, 23 theorems).
All seven passed native Lean individually with empty final logs. The final imported-root
audit checked every public declaration and 37 explicit local API haves; only standard
propext, Classical.choice, and Quot.sound occur. Own/direct freshness includes the installed
Mathlib root. All 11 direct imports, all 13 incoming imports, global declaration uniqueness,
whitespace, and seven single umbrella imports passed. Six Gaussian roots and two reciprocal
square-root helpers are indexed as eligible with no markers.

Global lint snapshot: 12 unrelated errors and 367 warnings.
This does not claim a passing repository-wide lint gate. Exact errors:
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMParityNearHalfTurn`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMPolarOddPrimeJumps`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzEnergyDomain`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzPowerRegularization`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzSourceIdealBridge`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperHurwitzWallApproach`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilLogPeriodicLockRigidity`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiGaussianHeatHankelJacobiSignChanges`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`
- `error: proof debt: formal/GaloisForLFunctions/RHTower/CCM/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)`

Validation artifacts: `/tmp/hgt-gaussian-metadata.py`, `-metadata.json`, `-declarations.json`,
`-incoming-imports.txt`, `-final-audit.lean`, `-final-audit.log`, `-api.lean`, `-api.log`,
`-roots-search.json`, `-reciprocal-search.json`, `-lint.log`, and the seven native leaf logs.
The Gaussian characteristic-function increment is complete; the broader research goal remains active.
