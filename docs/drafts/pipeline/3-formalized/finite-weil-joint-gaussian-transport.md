# Finite Weil joint Gaussian transport

Status: FORMALIZED — 2026-10-11.

Objective: construct an actual probability coupling from the canonical
Euclidean joint law to its diagonal Gaussian target, prove its mean
distance vanishes, and discharge boundedness restrictions for joint
Lipschitz observables. Prove actual joint Wasserstein-one convergence.

Sources: local Lean corpus and installed Lean dependencies only. Search
`joint Gaussian` in WeilLogShift returned JointCharacteristic and
JointWeakLimit, two hits, no markers. JointWeakLimit currently integrates
fixed bounded continuous functions; GaussianTransportLimit supplies
rank-dependent, unbounded scalar Lipschitz convergence and scalar couplings.

Dependency-closed proof:

1. The first coordinate of the joint fluctuation point is injective in
   its finite index. Define a measurable lift by a finite sum of singleton
   indicators times the corresponding joint point; it recovers every atom.
2. Map the existing scalar coupling for projection (1,0) through
   (x,y) -> (lift(x), diagonal(y)). Its marginals are exactly the actual
   joint probability law and diagonal Gaussian.
3. Distance to the diagonal at each atom is absolute residual divided by
   sqrt(r+1). Existing first-moment residual bound at quadratic width gives
   mean diagonal displacement <= 1/sqrt(r+1).
4. Diagonal embedding is 2-Lipschitz. Triangle inequality bounds mapped
   coupling mean cost by diagonal displacement + 2 times scalar mean gap.
   Both terms vanish. Integrability follows from the same majorant.
5. Joint Wasserstein one is nonnegative and bounded by this actual cost.
   Every joint Lipschitz observable is integrable: finite source and
   Gaussian diagonal pullback. Coupling gives a uniform expectation gap
   bound, hence convergence even for rank-dependent common-L test families.

Plan: verify APIs and geometry; construct lift and marginals; prove cost
integrability/bound; compose Wasserstein and Lipschitz limits; wire leaves;
native-build and audit every declaration; lint and record unrelated errors.
No external sources, computations, full builds, new axioms, or analytic
premises at final finite Weil roots. Research goal remains active.

Result: the full Euclidean joint fluctuation law converges in actual
Wasserstein one to the diagonal Gaussian along every quadratic-width
family. A concrete coupling has vanishing mean distance. Its cost bounds
expectation gaps uniformly for arbitrary rank-dependent, unbounded joint
Lipschitz tests with a common constant. All analytic premises are discharged.

The new structural bridge is measurable recovery of the joint atom from
its scalar first coordinate. This transfers the existing scalar Gaussian
coupling to the full joint law. The exact transverse atom distance is
absolute residual divided by sqrt(r+1), and joint mean cost is bounded by
the transverse mean gap plus twice the scalar Gaussian mean gap.

Formal leaves in `formal/GaloisForLFunctions/RHTower/`:

- `WeilLogShiftJointTransportGeometry.lean`: injectivity, diagonal
  Lipschitz bound, exact transverse distance, diagonal mean-gap bound and limit.
- `WeilLogShiftJointLift.lean`: measurable finite lift, atom recovery,
  projected-law pushforward, and diagonal Gaussian pushforward identity.
- `WeilLogShiftJointGaussianCoupling.lean`: measurable transport map,
  actual probability coupling, and both exact marginals.
- `WeilLogShiftJointGaussianCost.lean`: displacement integrability and
  integral, pointwise cost bound, actual coupling integrability and mean bound.
- `WeilLogShiftJointGaussianTests.lean`: unbounded joint Lipschitz test
  integrability under the Gaussian and both coupling marginals; integral-gap bound.
- `WeilLogShiftJointGaussianTransportLimit.lean`: actual Wasserstein
  definition and bounds; vanishing coupling cost, Wasserstein distance,
  and rank-dependent Lipschitz expectation gaps.

Verification: six native leaf builds exited zero with empty logs;
36 declarations (29 theorems, 7 definitions). Final audit used
`lake --old env lean /tmp/hgt-joint-gaussian-final-audit.lean` and exited zero.
All 36 declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
all 23 API references checked. Metadata found no issues: 12 direct imports,
11 incoming imports, each umbrella import exactly once, all leaf objects
and direct-dependency objects fresh. Scoped whitespace check passed.
All three convergence roots were indexed; all six returned module hits
were inspected, with no markers. All owned jobs exited.

Global formal lint exited 1: 15 unrelated errors, 367 warnings; no finding
in the six new leaves. Fourteen unrelated modules were unreachable:
RHTower.CCMPolarOddPrimeJumps, JointAncestryClusterTwoSided,
PaperPoissonContinuumPort, PaperPoissonNativeSource, PaperPoissonPortSymbol,
ZetaCriticalCountControl, ZetaCriticalGoodRows, ZetaCriticalInteriorRows,
ZetaCriticalPairDecomposition, ZetaCriticalRowBound, ZetaCriticalRowNumerics,
ZetaCriticalWindowStructure; HTGeometry.BoxPartitionSums,
QKrawtchoukCompanionTriangular. Remaining error: existing `sorry` at
`CCMPolarOddPrimeJumps.lean:104`, `ccmPolarOddSource_eq_core_add_atoms`.

Artifacts: `/tmp/hgt-joint-gaussian-` prefix with `prior-search.json`,
`api.lean`, `api.log`, `metadata.py`, `metadata.json`, `declarations.json`,
`incoming-imports.txt`, `final-audit.lean`, `final-audit.log`,
`roots-search.json`, `lint.log`; leaf logs `/tmp/hgt-<leaf>.log`.
No external mathematical source was consulted.

Follow-up formalized in `finite-weil-joint-gaussian-quadratic-transport.md`:
this same lifted coupling has vanishing quadratic distance. The proved
bound is twice normalized residual variance plus four times scalar
Gaussian quadratic cost; common-L test-value differences also vanish
in mean square. See that card for native and axiom audits.
The broader research goal remains active.
