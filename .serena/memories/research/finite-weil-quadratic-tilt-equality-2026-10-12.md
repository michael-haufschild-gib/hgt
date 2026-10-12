# Finite Weil quadratic tilt equality and finite witnesses — 2026-10-12

User constraint: ONLY local Lean corpus for mathematical evidence. No web, external papers, numerical experiments, or literature novelty claims. See `mem:workflow/research-corpus-only-2026-10-12`.

Formalized card: docs/drafts/pipeline/3-formalized/finite-weil-quadratic-tilt-equality.md. Predecessors: `mem:research/finite-weil-quadratic-replication-spectrum-2026-10-12`, `mem:research/finite-weil-quadratic-fast-replication-2026-10-12`. The spectrum card boundary was updated.

Four leaves, seven theorems, all sequential native leaf builds empty-log successes; both umbrellas wired without full/umbrella builds.

HTGeometry/TiltedEqualityRigidity.lean imports Mathlib.MeasureTheory.Measure.Tilted. tilted_eq_iff_sub_ae_const: for probability mu and exp-integrable real f,g, mu.tilted f=mu.tilted g iff exists real c, f-g=c mu-a.e. Forward identifies log RN formulas; reverse uses tilted_congr, tilted_tilted, and tilted_const with probability instance isProbabilityMeasure_tilted hg.

RHTower/WeilLogShiftObservableSupport.lean imports WeilLogShiftObservableLaw. finiteWeilCanonicalObservableLaw_ae_iff: for any measurable target with measurable singletons, arbitrary f:Fin(r+1)→target and predicate p, AE p under actual canonical observable law iff forall i,p(f i). No predicate measurability or observable injectivity premise. Uses strict positivity of every canonical edge mass, finite sum of weighted Dirac measures, ae_dirac_eq=pure.

RHTower/WeilLogShiftQuadraticTiltEquality.lean imports generic rigidity, observable support, QuadraticTiltLaw. Three actual-root theorems, ALL finite r,k and ALL real coefficients (no subcriticality):
- finiteWeilCanonicalJointQuadraticTilt_eq_iff_constant: equality of laws iff exists c with forall i, Q(a-A,b-B,d-D)(FluctuationPoint r k i)=c.
- finiteWeilCanonicalJointQuadraticTilt_eq_iff_values: same equality iff every such value equals value at index0.
- finiteWeilCanonicalJointQuadraticTilt_ne_iff_witness: unequal laws iff exists i with that value different from value at0.
Thus measure equality reduces exactly to finite linear conditions in coefficient differences. Actual fluctuation points remain explicit corpus-defined coordinates (do not assume they lie exactly on limiting diagonal). All exp-integrability premises discharged via finite-law theorem.

RHTower/WeilLogShiftQuadraticReplicationWitness.lean imports QuadraticTiltEquality, QuadraticFastReplication, QuadraticReplicationSpectrum. Two exact iff roots rewrite measure inequality into existence of one anchored finite point witness:
- exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff_witness: arbitrary depth schedule k:N→N, all real coefficients; monotone escaping m>=id with actual product affinity→0 iff eventually a finite potential witness exists.
- exists_finiteWeilCanonicalJointQuadraticTilt_replication_limit_iff_witness: original subcritical domains/canonical depths 2*(r+1)^2+t r; arbitrary q:ENNReal. Escaping schedule with affinity→q iff (unequal diagonal sums and q=0) OR (equal sums and (q=1 OR (q<1 and eventually finite witness))). No monotonicity promised for interior targets.

Audit: /tmp/hgt-weil-tilt-equality-final-audit.lean passed native; 7 axiom reports standard propext/Classical.choice/Quot.sound;10 API checks;7 unique declarations;8 direct edges;7 incoming imports;4 fresh objects;direct dependency freshness;scoped index7/7 no partial/markers/stderr;whitespace clean. Prefix /tmp/hgt-weil-tilt-equality-. Single lint snapshot6 unrelated errors,367 warnings: unreachable CCMPolarOddPrimeJumps,PaperWoldPrimeWindows,Sieve.FourthDerivativeTestSharp,ZetaFiveSeventhsLineBound,QKrawtchoukCompanionTriangular; existing CCMPolarOddPrimeJumps.lean:104 sorry. No owned error. Do not use prior increment's16-error snapshot for this result.

API lesson: MeasureTheory.Measure.ae_smul_measure_iff is generic over scalar IsDomain and does NOT work for ENNReal. Use MeasureTheory.Measure.ae_ennreal_smul_measure_iff.{0}. ae_finsetSum_measure_iff.{0,0} plus Finset.mem_univ,true_implies,forall_congr', then simp[Measure.ae_ennreal_smul_measure_iff hmass,ae_dirac_eq,Filter.eventually_pure] handles arbitrary predicates. hmass=(ENNReal.ofReal_pos.mpr finiteWeilCanonicalEdgeMass_pos).ne'.

Prior scoped queries: WeilLogShift QuadraticTilt/equality0, HTGeometry tilt/equality4 unrelated records, tilted/constant2 unrelated records; source search plus Mathlib Tilted supplied APIs. No broad novelty claim.

Remaining: uniform classification/rank of coefficient subspace cut out by these anchored evaluations; prescribed replication rates; monotone intermediate targets. A covariance-kernel reformulation could be investigated next but is NOT established here. Corpus-wide goal active.