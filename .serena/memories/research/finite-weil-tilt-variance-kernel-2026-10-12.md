# Finite Weil tilt variance kernel — 2026-10-12

Only local Lean corpus for mathematical evidence; no web, external papers, experiments, or literature novelty claims. See `mem:workflow/research-corpus-only-2026-10-12`.

Card: docs/drafts/pipeline/3-formalized/finite-weil-tilt-variance-kernel.md. Predecessor: `mem:research/finite-weil-quadratic-tilt-equality-2026-10-12`; its card boundary now points to this result.

Four leaves/eight theorems; all native leaf builds passed with EMPTY logs; umbrellas wired without building.

HTGeometry/VarianceGaugeRigidity.lean (imports Mathlib.Probability.Moments.Variance): variance_eq_zero_iff_ae_const for probability mu and MemLp f 2 mu. Var(f)=0 iff exists c, f=c mu-a.e. L2 is essential: real variance can be zero when extended variance is infinite. Forward uses ProbabilityTheory.ae_eq_integral_of_variance_eq_zero; reverse variance_congr then variance_eq_integral aemeasurable_const and simp.

RHTower/WeilLogShiftTiltVarianceKernel.lean imports VarianceGaugeRigidity, WeilLogShiftObservableSupport, WeilLogShiftQuadraticTiltResponse. Four unconditional actual-root theorems, all finite r,k and all real coefficient triples:
1. finiteWeilCanonicalJointQuadraticTilt_ae_iff: arbitrary predicate p holds a.e. under tilted law iff forall source atom i,p(FluctuationPoint r k i). Uses mutual absolute continuity of tilt and base, then prior exact base support theorem.
2. finiteWeilCanonicalJointQuadraticTilt_memLp_two: EVERY f:E→R belongs to L2 under each finite tilted law, with no measurability/integrability premise. Existing finite-law integrability of f and f² discharges memLp_two_iff_integrable_sq.
3. finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff_values: Var(f)=0 iff all atom values f(point i) equal f(point0).
4. finiteWeilCanonicalJointQuadraticTilt_variance_eq_zero_iff: zero variance for arbitrary f is equivalent under ANY TWO coefficient triples at the SAME finite r,k. This identifies common kernel, NOT equal variance magnitudes. It does NOT identify kernels across different depths or with the Gaussian limit.

RHTower/WeilLogShiftQuadraticVarianceRigidity.lean imports TiltVarianceKernel and QuadraticTiltEquality. finiteWeilCanonicalJointQuadraticTilt_eq_iff_variance_eq_zero (r k)(a b d A B D u v w:R): equality of laws for (a,b,d) and (A,B,D) iff variance of Q(a-A,b-B,d-D) under third tilt (u,v,w) is zero. finiteWeilCanonicalJointQuadraticTilt_ne_iff_variance_pos gives inequality iff strictly positive variance. All real coefficients and all finite depths; no subcriticality.

RHTower/WeilLogShiftQuadraticVarianceReplication.lean imports QuadraticVarianceRigidity and QuadraticFastReplication. exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff_variance: arbitrary k:N→N, two fixed real coefficient triples, and arbitrary changing probe coefficients u,v,w:N→R. Monotone m>=id escaping with actual product Bhattacharyya affinity→0 exists iff eventually variance of Q(coefficient difference) under probe tilt at SAME r,k(r) is positive. No convergence, boundedness, subcriticality, or growth conditions on probe coefficients/depth.

Validation: native /tmp/hgt-weil-tilt-variance-final-audit.lean passed,8 axiom reports only propext/Classical.choice/Quot.sound;7 API references plus constant-variance example;8 unique declarations;8 direct edges;7 incoming imports;4 fresh native objects;direct dependency freshness;scoped index8/8 no partial/markers/stderr;whitespace clean. Single lint snapshot8 unrelated errors,367 warnings: unreachable RHTower.CCMPolarOddPrimeJumps,Sieve.FourthDerivativeTestSharp,XiSliceHeatRateInteriorLindelof,ZetaFiveSeventhsLineBound,ZetaStripInterpolation; HTGeometry.HurwitzZetaEulerMaclaurinBridge,QKrawtchoukCompanionTriangular; existing CCMPolarOddPrimeJumps.lean:104 sorry. No owned error. Artifacts prefix /tmp/hgt-weil-tilt-variance-.

Prior evidence: all37 scoped WeilLogShift variance/covariance declarations inspected across2 pages; HTGeometry tilt/variance/kernel query0. Existing NavierStokesFiniteTiltConvexity gives finite scalar covariance positivity under nonconstant score, a distinct object. Existing actual mixed moment/coordinate covariance limits in WeilLogShiftQuadraticTiltMoments.lean were read; no quadratic-variance limit was proved this increment.

Next frontier: uniform rank/coefficient basis of common kernel; quantitative quadratic-variance limit from second/fourth mixed moments; prescribed replication rates; monotone interior targets. A local conjectural limit would use Q(h,j,l)(X,X)=(h+2j+l)X² under the existing diagonal Gaussian, but must audit exact moment APIs and paper proof before formalizing. Do not claim that limit is established. Corpus-wide goal active.