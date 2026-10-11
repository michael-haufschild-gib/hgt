# Finite Weil joint Gaussian quadratic transport

Status: FORMALIZED — 2026-10-11.

Objective: prove vanishing mean-square distance for the actual joint
Gaussian coupling, then uniform mean-square comparison of arbitrary
rank-dependent, unbounded real Lipschitz observables with a common constant.

Sources: local Lean corpus and installed Lean dependencies only.
Scoped search `JointGaussian quadratic` returned no hits; exhaustive
WeilLogShift text search found quadratic-width statements but no joint
quadratic-coupling result. Existing JointGaussianCost supplies the actual
coupling; GaussianQuadraticLimit and FluctuationRankOneLimit supply both
scalar quadratic-cost decay and normalized residual-variance decay.

Dependency-closed proof:

1. Diagonal embedding has squared Euclidean distance exactly 2|x-y|^2.
   JointLiftDisplacement squared integrates, through the scalar first
   marginal, to residual variance divided by r+1.
2. Triangle inequality and (A+B)^2 <= 2A^2+2B^2 give pointwise joint
   squared distance <= 2 displacement^2 +4|x-y|^2. Its majorant is
   integrable. Map the existing scalar coupling to the joint coupling.
3. Actual joint quadratic cost J satisfies J <= 2R/(r+1)+4C. Existing
   limits and nonnegativity give J -> 0 for every quadratic-width family.
   Variance positivity also gives joint mean-distance squared <= J.
4. For every L-Lipschitz f, |f(u)-f(v)|^2 <= L^2 dist(u,v)^2.
   Therefore the squared difference is integrable and its expectation
   <= L^2 J. The same bound yields convergence for rank-dependent test
   functions with one common L, with no boundedness or L2 premises.

Plan: verify APIs; formalize squared geometry and transverse integral;
prove joint integrability, cost bounds and decay; prove observable L2
comparison; wire leaves; native-build/axiom-audit all declarations;
run lint and record unrelated failures. Research goal remains active.

Result: the same actual joint probability coupling has vanishing
mean-square Euclidean distance for every natural offset sequence.
For any rank-dependent family of real L-Lipschitz functions, the mean
square of the coupled test-value difference tends to zero. Test functions
may be unbounded; no integrability, boundedness, or L2 premise remains.

Exact transverse second moment is R/(r+1). The joint quadratic cost J
satisfies J <= 2R/(r+1)+4C, improving the preceding candidate coefficient
8 to 4 through exact squared diagonal geometry. At quadratic width,
J <= 2/(r+1)+4C. Joint mean distance squared is <= J, and squared test
difference has expectation <= L^2 J.

Formal leaves in `formal/GaloisForLFunctions/RHTower/`:

- `WeilLogShiftJointDiagonalQuadratic.lean`: exact squared diagonal
  distance, transverse square integrability and exact integral, pointwise
  joint quadratic majorant.
- `WeilLogShiftJointGaussianQuadratic.lean`: actual joint squared-cost
  integrability, cost definition and bounds, finite-width estimate,
  mean-distance comparisons, and unconditional quadratic-cost decay.
- `WeilLogShiftJointGaussianL2Tests.lean`: pointwise squared Lipschitz
  comparison, square-difference integrability, actual quadratic-gap
  definition and bound, and common-L rank-dependent gap decay.

Verification: all three native leaf builds exited zero with empty logs.
Metadata found no issues: 19 declarations (17 theorems, 2 definitions),
5 direct imports, 5 incoming imports, each umbrella import exactly once,
fresh leaf/direct-dependency objects. Final native audit used
`lake --old env lean /tmp/hgt-joint-quadratic-final-audit.lean` and exited zero.
All 19 declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
all 17 API references passed. Both roots were indexed, one exact scoped
hit each, no markers. Scoped whitespace check passed; all owned jobs exited.

Broadened `integrable sq` search in Quantile returned 23 hits across two
pages, all inspected; BddSupp.integrable_sq requires bounded Lebesgue
support, so the actual Gaussian coupling uses its own verified majorant.

Global formal lint exited 1: 18 unrelated errors, 367 warnings; no finding
in the three new leaves. Seventeen unrelated modules were unreachable:
RHTower.CCMPolarOddPrimeJumps, JointAncestryClusterTwoSided,
PaperPoissonCompletionGap, WeilMixedResonanceLockRigidity,
WeilMixedResonanceLockSpectrum, XiHeatHankelFormOrthantPositivity,
ZetaCriticalAsymptotics, ZetaCriticalCountControl, ZetaCriticalGoodRows,
ZetaCriticalInteriorRows, ZetaCriticalPairDecomposition, ZetaCriticalRowBound,
ZetaCriticalRowNumerics, ZetaCriticalWindowStructure, ZetaZeroAntiCrystalCritical;
HTGeometry.BoxPartitionSums, QKrawtchoukCompanionTriangular. Remaining error:
existing `sorry` at `CCMPolarOddPrimeJumps.lean:104`,
`ccmPolarOddSource_eq_core_add_atoms`.

Artifacts use `/tmp/hgt-joint-quadratic-`: `prior-search.json`,
`receiver-search.json`, `broad-search.json`, `broad-tail-search.json`,
`api.lean`, `api.log`, `metadata.py`, `metadata.json`, `declarations.json`,
`incoming-imports.txt`, `final-audit.lean`, `final-audit.log`,
`cost-root-search.json`, `tests-root-search.json`, `lint.log`.
Leaf logs: `/tmp/hgt-<leaf>.log`. No external mathematical source was used.

Follow-up formalized in `finite-weil-joint-quantile-realization.md`:
the explicit quantile lift converges at every probability parameter in
(0,1), with exact common-space marginal and pair laws. Finite-atom range
membership and a uniform transverse bound discharge the remaining premises.
See that card for native and axiom audits.
The broader research goal remains active.
