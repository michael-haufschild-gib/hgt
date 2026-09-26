# Quadratic Xi sampling floor: verified progress; RH still open

Goal remains unconditional Lean RH proof or refutation via actual Xi-moment positivity. Do NOT mark complete. This follows research/xi_full_hankel_uniform_floor_quarter_rate_2026_09_26 (previous32 theorems) and initial third-form26 theorem increment. Repo /Users/michael/Documents/code/hgt/formal, projectless log/output under /Users/michael/Documents/Codex/2026-09-26/new-chat-3.

## Current increment verified
Three new leaves,12 theorems,3 definitions. Every first leaf audit passed warning-free:
- XiHeatSamplingEnergyBound: session69639 exit0.
- XiHeatQuadraticSamplingBands: session51574 exit0.
- XiHeatQuadraticEnergyFloor: session77225 exit0.
Each used foreground lake --old env lean leaf -o target. One Lean process at a time; no full/umbrella builds. Axiom audit8997 exit0: all12 theorem reports, only propext/Classical.choice/Quot.sound, no missing/unexpected axioms/diagnostics. Own3 imports exactly once; oleans current; forbidden source scan empty and scoped git diff --check clean. No computations, proof holes, added axioms, or heartbeat overrides. No commit/push by this agent. Previous five leaves now externally tracked; preserve external work.

1. RHTower/XiHeatSamplingEnergyBound.lean:
xiHeatFiniteNormEnergy_sampling_bound holds unconditionally for any N, coefficient vector a, actual sample list q:FinN→XiZeroCopy and every tau. With z_i=exp(tau)*alpha(q_i)^2:
|det V(z)|² sum_j a_j² <= N² polynomialSamplingCap(z)² *sum_i exp(Re z_i)*K_N(a,tau).
Exact inverse Gaussian weights retained; no sample separation, positive Hankel, or time restriction premise. Derived from full interpolation energy inequality and each actual norm atom<=K, with exp(Re z_i) cancelling Gaussian weight.

2. RHTower/XiHeatQuadraticSamplingBands.lean:
exists_xiSpectralPoint_in_bounded_windows extracts actual divisor copies in (T-h,T+h] for every sufficiently largeT. Uses existing XiLogDerivLineOneWindowLower.exists_xiZeroCount_window_ge_log; multiplicity support counts strictly increase because logT>0. No count-only surrogate.
xiHeatQuadraticSamplingRadius N=(N+1)²+1.
eventually_forall_exists_xiHeat_quadratic_separated_nodes: ONE small-time cutoff ALL N. Windows centered (i+1)T, T=exp(-tau/2), T>=4h. Scaled nodes real part between (i+3/4)²-1/4 and (i+5/4)²; norm upper latter+1/4; adjacent gaps>=1.
eventually_forall_exists_xiHeat_quadratic_sampling_determinant: normbound plus determinant norm>=1 at common cutoff.

3. RHTower/XiHeatQuadraticEnergyFloor.lean:
xiHeatQuadraticEnergyFloor N=1 at0; forN>=1 eta'_N=exp(-R)/(N³ C²), R=(N+1)²+1,C=N!*[(1+N R)^(N-1)]^N.
xiHeatFiniteNormEnergy_eventually_quadratic_floor: K_N>=eta'_N sumcoeff², one common sampling cutoff.
xiHeatQuadraticSamplingRadius_le and xiHeatSamplingEnergyFloor_le_quadratic prove eta_old<=eta'_N for everyN (oldradius(3*4^N)²+1).
xiHeatHankelForm_eventually_quadratic_lower_bound: H_N(scaled a,t)>=(eta'_N-A_N*t^(1/4))*sumcoeff², retaining full previous phase budget A_N=S_(3/2)*sum b_j.
xiHeatQuadraticLogTime N=4log(eta'_N/(2(1+A_N))).
xiHeatJointLogTime_le_quadratic proves explicit degree-dependent time factor improves. Global sampling cutoff can differ: do NOT claim entire new region contains old region.
xiHeatHankelForm_quadratic_degree_time_coercive: exists tau0, forall N,tau<=min tau0 newLogTime, all coeffvectors positive margin eta'_N/2.
N0 vacuous, all positive N actual complete forms and cross terms.

## Still missing RH endpoint
XiGaussianHeatHankelLadder criterion needs every order and every positive time. New all-time bound is for K only, NOT Hankel positivity. Common sampling cutoff is NOT common all-order positivity cutoff. No actual negative Xi witness, RH proof, or all-time propagation produced. Refining sampling constants alone has not supplied fixed-time all-order phase cancellation.

## Next conjecture9: relative Gaussian energy, infrastructure required
Corpus search and direct Lean reads verified:
- HTGeometry/HermitePolynomialDerivativeEnergy.lean, gaussianPolynomialDerivativeEnergy_le P:
||P' e^(-pi x²)||_2² <=4*pi*natDegree(P)*||P e^(-pi x²)||_2². Unconditional sharp oscillator estimate.
- HTGeometry/ComplexGaussianPolynomialTranslation.lean:
gaussianPolynomialDerivativeNorm_le; gaussianPolynomialIterateDerivativeNorm_le;
gaussianHasseDerivativeFactorialNorm_le;
complexTranslatedPolyGauss_apply identifies literal P(x+z)e^-pi x²;
norm_complexTranslatedPolyGauss_le <=exp(|z|sqrt(4*pi*d))*base norm.
Also evenSquarePolynomial, complexTranslatedEvenPolyGauss_apply, norm_complexTranslatedEvenPolyGauss_le (bottom not yet fully read).
No translation-difference norm theorem in this file (rg enumerated all declarations), no actual Gaussian sampling-frame result from corpus search.
Next build difference bound <=(exp(|z|sqrt(4*pi*d))-1)*base norm, then actual-divisor transfer: fixed-width lower windows plus XiZeroCountLocalCeiling upper count. Must handle variable imaginary shift |Im alpha|<1/2, actual multiplicity counting measure, low-height hole, and full Gaussian multiplier, not assume continuous L2 bound applies to discrete Xi energy. Missing infrastructure must be built, not pivoted away.
Expected useful relative phase control at joint degree/time scale; do not claim all-time RH from it before proof.

## Other searched source constraints
GammaConductorGaussianHeatDiagonalNoGo directly proves unfiltered one-prime Gaussian curvature negative outside aperture while Gamma-conductor residual diagonal positive. Cannot identify kernels by real diagonal congruence; mixed polar/Gamma and cross-prime terms essential. This is NOT an actual Xi negative witness.
XiGlobalReflectionDefectEnergy directly proves defect=2*(Hermitian reciprocal mass - primeArchCentralCurvature)>=0, equality iffRH; reverse bound remains missing. No new theorem added there.
Search xiPolynomialGaussian approx returnednone; Hankel propagation returned nesting/upwardnegative and unrelated shifted boundary transport, no heat-time closure from current small-time result.

## Artifacts and audits
work/xi-quadratic-manifest.json, xi-quadratic-axioms.lean/.log, xi-quadratic-audit-summary.json, xi-quadratic-scope-audit.json, xi-quadratic-lint.log.
outputs/xi-full-hankel-energy-bound.md updated to quadratic radius and total44 full-family theorems,15defs,8modules across previous+current increments. Prior third-form report linksforward.
Global lint97167 exit1: eight unrelated unwired modules (EtaReflectionCenterTurning, HorizontalIsolationBlockPacket, HorizontallyIsolatedSimpleZeros, MoebiusMollifiedZetaField, ThetaNoetherHamiltonJacobi, ThetaPrimeGammaScalingEnergy, WindowTransformSamplingParseval, HilbertMetric.HorizontalLamzouriUnnormalized), stale LEAN_API/LEAN_OVERVIEW due concurrentwork. No owned3 unwired. Final index refresh launched after inspectinglint; poll its saved session from latest chat if live. Do not claim global lint passed. No owned Lean process remains after axiomaudit; only final index maystillrun.
No temporary API/profile files created this turn; auditlogs retained. Shared Serena project activation can change; activateformal beforememorywrite. Avoid symbol tools that previously triggered hidden Lake builds under foreground/no-full-build constraint; use formal_tools.py research plus directLean.
