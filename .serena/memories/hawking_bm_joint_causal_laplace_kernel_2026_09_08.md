# HB: original spatial response is one causal Laplace kernel

RH goal remains ACTIVE and UNPROVED. Frontier map is READ ONLY by latest user instruction; do not edit or revert concurrent changes. No new universal-law entry follows from this batch.

Completed 10 canonical leaves / 48 new public theorems / 723 lines. Proof card: docs/drafts/pipeline/3-formalized/hb-joint-causal-laplace-kernel.md. Active continuation: docs/drafts/pipeline/1-in-progress/hb-joint-causal-laplace-identification.md. Conformal-regularity card links this independent causal result.

Full proof chain: literal theta cusp -> Xi occurrence -> retained spin-two source -> original causal response and left-QNM pairing -> independent Hawking-clock extinction -> RH.

## Exact completed result
For each FIXED F : RHTower.D4BMJointWave.SpatialSpace, jointCausalKernel F is one frequency-independent SpatialSpace-valued function of real time. It is AE zero before zero; every positive exponential damping belongs to L2 on positive time. For EVERY Re(w)>0 its absolutely convergent Bochner Laplace integral equals jointEmbedding (jointWaveResponse w hw F), the original selected spatial response. All auxiliary positive damping choices yield AE equal kernels on the whole line. This is actual vector inversion, not a family of arbitrarily chosen scalar probe outputs.

Endpoint namespace RHTower.D4BMJointWave: jointCausalKernel_support, jointCausalKernel_memLp_pos, jointCausalKernel_integrable, jointCausalKernel_originalResponse_rightHalfPlane.

## Construction
Actual form pencil A(w)=I+(w^2-1)J*J for contractive energy embedding J. Existing rotated coercivity gives bounded two-sided inverse of conj(w)A(w). Cancel nonzero scalar to prove A(w) a unit. Ring.inverse defines waveEnergyInverse, holomorphic by Banach-algebra inversion; original uniqueness identifies it with old jointWaveResponse. Spatial R(w)=J A(w)^(-1)J*, norm <= norm(F)/(Re(w)*norm(w)).
For delta>0, each probe p_delta(w)=ell(R(w+delta)F) has bounded holomorphic multiplier (w+delta)p_delta. The existing Cauchy Hardy kernel and bounded multiplication give Hardy membership. Existing PaleyWienerHalfPlane supplies scalar causal datum and transform identity.
Construct actual vector boundary L2 on delta+sigma+2*pi*i*xi and vector inverse Fourier Q_delta,sigma. Probes commute with L2 Fourier/inverse via Schwartz integral commutation and density. Dense Bochner tensors imply vector L2 totality from all inner probes, including restricted support without a separability premise or a common pointwise exceptional set.
K_delta(t)=exp(2*delta*t) Q_delta,delta(t). Probes identify with scalar Hardy data, giving negative support and Bochner Laplace=R(w)F initially for Re(w)>2delta. For delta,epsilon use c=2delta+2epsilon: damped vector kernels both L2; every probe of difference has zero Laplace transform. Existing L2 Laplace injectivity plus vector probe totality proves equality. Cancel damping; negative support and singleton nullity extend whole-line AE equality. Compare fixed K_1 against epsilon=Re(w)/4 to prove full right half-plane. Compare epsilon=c/4 to get every positive damping.

## Canonical modules
RHTower.ThetaCuspHawkingBMJoint{AnalyticInverse,HardyResponse,VectorBoundary,CausalKernel,CausalLaplace,KernelDamping,KernelCoherence,CausalRightHalfPlane}; HTGeometry.{HilbertL2FourierNaturality,BochnerL2ProbeTotality}. Prefix GaloisForLFunctions. Generic namespace GaloisForLFunctions.HTGeometry. All wired once into respective umbrellas, NO umbrella builds.

## Hard remaining work
F must be fixed while frequency varies. Existing originalWaveResidual and cuspResidualVector in ThetaCuspHawkingBMJointSourceResponse / JointSourceResidualAssembly DEPEND ON w. This theorem alone does not identify the actual time-dependent smooth-onset source response. Need actual vector source time dependence, convolution/transform interchange or a direct source-specific analytic inversion, all onset terms and explicit cusp principal correction. Smooth source Laplace functions are in ThetaCuspHawkingBMMixedSmoothCurrentLaplace.
No time-slice completed energy-domain membership, weak/classical time PDE, metric finite propagation, modular patching or radial endpoint traces has been proved by this batch. Constrained Einstein sectors, physical left-QNM continuation and retained spin-two/AIME pairing remain. Independent Hawking-clock extinction is unproved. Causal response exists for every spatial F and by itself gives no Xi-zero selection.

## Verification and efficiency
All scratch checks passed. All ten exact canonical leaf lake build audits passed, each two jobs and no warnings, in isolated cache-only package. Forty-eight NEW theorem axioms checked once successfully using scratch lake env lean: only propext, Classical.choice, Quot.sound. No sorryAx or computational axioms. Earlier import-only failed attempts printed no theorem; shared old caches were incomplete and changed concurrently. Restored only required missing caches with foreground single-file checks; did not broad-build dependencies. Do not repeat any completed new or previous theorem axiom audits.
All ten sources and twenty olean/ilean pairs bytechecked and umbrella imports checked exactly once. Source index refreshed. formal_tools.py lint --check-generated passed with 141 large-file warnings only; scoped whitespace check passed. No numerical experiment, no full build, no umbrella build. Owned scratch dirs were /tmp/hb-joint-causal.VeIIXI and /tmp/hb-causal-leaf-audit.6627jg8o; cleanup handled at close. Never touch unrelated concurrent Lean processes/files.

Previous completed memory: `mem:hawking_bm_joint_nonseparated_energy_tests_2026_09_08`. Coordinate regularity remains an obligation for physical PDE identification but is not prerequisite for the causal transform proved here.
