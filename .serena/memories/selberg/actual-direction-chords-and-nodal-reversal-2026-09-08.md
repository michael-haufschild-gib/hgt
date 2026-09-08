# Cycle 27 complete: actual normalized directions, weighted distance, nodal reversal
Selberg all-congruence 1/4 goal ACTIVE and UNPROVED. No nonnegative Qcore+B lower bound obtained. Prior strict mass is complete; see mem:selberg/strict-mass-and-actual-radial-defect-2026-09-08.

## Latest user steering
"use wider searches with our search tool for the lean corpus. dont forget that default when using multiple terms is AND."
Use explicit --any wide discovery batches, per-module 1 and exploration; AND only to follow concrete leads. This steers ongoing goal. Continue corpus-derived conjecture→proof/fail→pivot, no numerical experiments.

## Finished actual source module
formal/GaloisForLFunctions/RHTower/SelbergMaassTraceDirection.lean, 360 lines, imports ONLY SelbergMaassTraceRadial.
Actual N, MaassCuspEigenform Gamma(N+1), eigenvalue lam. All exceptional conclusions use actual lam in (0,1/4).
Definitions: direction u_q=F_q/sqrtD, correlation C(z,w)=Re sum Fq(w)conjFq(z), directionCorrelation, directionDistanceSq.
component_zero_of_density_zero and amplitude_mul_direction: exact reconstruction including common zeros.
direction_normSq: sum norms²=1 on D>0.
direction_equivariant: u_q(A*z)=u_(q[A])(z), every integral modular matrix, includes S/T.
component_mean_zero and weighted_direction_mean_zero: ∫Fq=∫rho*u_q=0 on EVERY shifted interval length N+1 at ANY positive height.
correlation_mean_zero against any fixed source point.
exists_negative_correlation: each D(z)>0 has same-height point in centered level period with C(z,w)<0. Continuity, zero integral, positive diagonal prove it.
amplitude_mean_pos: centered amplitude mean strictly positive at any positive source point. Actual amplitude does not inherit constant-term vanishing.
correlation_eq_amplitudes_mul all points; directionDistanceSq_eq=2-2directionCorrelation when both positive.
exists_separated_direction and source_direction_separation (line238): original nonvanishing gives actual same-height positive points with normalized squared chord distance>2.
amplitude_differentiableAt and direction_differentiableAt positive locus only.
amplitude_mul_direction_dir: rho*D_v u_q=D_v Fq-c_v Fq, actual Frechet derivative.
radialResidual_eq_direction_energy: R_v(c_v)=D*sum_q |D_vu_q|² at D>0.
amplitude_mul_directionDistanceSq: for positive base z and ALL moving w including zeros,
rho(w)*d(z,w)²=2rho(w)-2C(z,w)/rho(z).
weighted_distance_slice_continuous: weighted chord slice continuous through common zeros, hence compact integrability.
weighted_direction_distance_mean (line339): every shifted level period satisfies ∫rho*d²=2∫rho.
Do not claim unweighted direction smooth at zeros or any core/Bessel lower bound.

## Finished exact toy
formal/GaloisForLFunctions/RHTower/SelbergNodalAngularToy.lean,84 lines. Imports Mathlib Integrals.Basic and Trigonometric.Complex.
residual h x=(h'-(h²)'/(2h²)*h)² for real profile.
residual_eq_zero_off_zeros for differentiable h!=0, residual_at_zero=h'².
cosine_zeros_countable via exact integer classification.
cosine_residual_ae_zero, cosine_residual_integrable globally on volume, cosine_residual_integral on all compact intervals.
cosine_residual_at_node at pi/2=1.
zero_mean_does_not_force_angular_energy(line71): CLOSED existence h=cos, C², period2pi, h0=1,hpi=-1, zero mean, positive squared mass, genuinely integrable residual with period integral0.
SCOPE: not claimed Maass, cuspidal, or inversion-invariant. Only refutes positive integrated angular residual from smooth periodic zero-mean data alone. Actual positive survivor is source weighted chord/transport above.

## Corpus ideas and next cycle28
Early queries: weighted Poincare, normalized direction, variance mean, zero mean sign, cosine mean.
Read HedenmalmCriticalFeatureAliasVariancePhaseSaving1..102, CesaroSignRecurrence1..87 (signed-mean separation), OccupationVacuumAnomalyReciprocity248..281 (normalization retaining raw norm), CosinePolynomialPurchaseCap72..109 (exact cosine integrals).
After user steering explicit --any batches:
nodal chord oscillation variance (2922 matches/667 modules),
coarea Cheeger conductance resistance (709/92),
permutation transport holonomy expansion (11622/3251),
OR phrases effective resistance/Dirichlet principle/Poincare and spectral gap/boundary transport/zero mean.
Counts describe searched corpus, NOT all source files read.
Read FirstOrderConnectionIntervalClassification1..210 (actual endpoint holonomy); StokesCartanCoronaCapacity all (parallel resistance square completion); WeightedGraphSpectralGap all (Dirichlet=massnorm-averaging; HasSpectralGap is INPUT); GateCapacityDiscrepancy1..160 (actual killed-chain minimizer); FiniteProjectivePlaneSpectralGap1..160 (source incidence gap NOT identified with actual Maass quotient); FormationStokesFolnerSelection165..213 (bulk/boundary capacity). PathShellEdgeTail symbol scan: conductance there is minimum edge norm, NOT spectral gap. ReciprocalCoareaEnergy1..170 is prime-shell specific, no actual Maass comparison.
Cycle28: conjecture actual amplitude-weighted chord/core-energy capacity comparison retaining S/T permutations, reciprocal-density divergence at common zeros, and adverse Bessel channels. Construct actual weights/operators; no assumed graph gap or positive inverse. Width-dependent interval Poincare alone does not give congruence-uniform control. Continue broad OR discovery, then prove/fail/pivot.

## Durable cards
Parent docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecturing-loop.md completed27, next28, wide-OR policy.
Stage3 docs/drafts/pipeline/3-formalized/selberg-source-directions-and-nodal-reversal.md complete dependency-closed paper proof and audit. Temporary stage2 file promoted/removed.
Failed shortcut docs/drafts/pipeline/5-failed/selberg-zero-mean-angular-energy.md complete positive survivor closure.

## Audit terminal; do not repeat without edits
Both complete scratch and direct source checks passed without warnings.
Two sequential LEAN_NUM_THREADS=1 lake build namedtarget audits passed, rebuilt only each named target:
 /tmp/selberg_trace_direction_build.log (7.1s)
 /tmp/selberg_nodal_angular_build.log (1.7s).
No full/umbrella build; both wired around RHTower16246.
35 public declarations passed lake env lean /tmp/selberg_direction_nodal_axioms.lean.
35 reports, none missing, no errors, only propext/Classical.choice/Quot.sound or none.
 /tmp/selberg_direction_nodal_axioms.log
 /tmp/selberg_direction_nodal_declarations.txt
Index passed /tmp/selberg_direction_nodal_index.log; research retrieves capstones.
LATEST global lint FAIL only unrelated UNTRACKED UNWIRED HTGeometry.FokasLenellsSobolevEnergy.
 /tmp/selberg_direction_nodal_lint.log.
Previous FokasLenellsUniformization resolved concurrently. Don't claim global lint pass.
All task file whitespace checks passed; ALL task handles terminal. Final process scan Lean/Lake executable processes:[].
No task commit/push, shared unrelated work preserved.

## Lean lessons
Use generated fun_pow/fun_mul/fun_inv for function-valued operations when rewrite transparency fails.
Explicitly change differentiation target to literal function before simpa; top-level composition may not unfold.
Complex.ofRealCLM_apply needed in amplitude casts. Cast polymorphic real dir as ((dir ... :ℝ):ℂ).
No HasFDerivAt.div; differentiate product reconstruction with ha.mul hu, and use inverse for differentiability.
Typed IntervalIntegrable complex product before reCLM.intervalIntegral_comp_comm prevents stuck measure/constant metavariables.
No intervalIntegral.integral_re: use reCLM.intervalIntegral_comp_comm.
Finset integral rewrite needs typed literal component integrability due to quotient source subtype coercions.
maassMean uses set Ioc integral: first intervalIntegral.integral_of_le.
field_simp may close goal directly; omit following ring then.
