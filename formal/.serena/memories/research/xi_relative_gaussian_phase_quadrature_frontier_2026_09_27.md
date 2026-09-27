Active goal is unconditional Lean RH or negation; remains ACTIVE, unproved. Latest work extends independent actual Xi energy/debt lower bounds by relative Gaussian phase and quadrature infrastructure. Continue conjecture/prove/fail loop; do not replace full RH goal with finite-order or small-time target.

Project formal=/Users/michael/Documents/code/hgt/formal. Projectless /Users/michael/Documents/Codex/2026-09-26/new-chat-3. Log work/xi-curvature-rh-loop.md. User report outputs/xi-relative-gaussian-control.md; master actual-Xi report outputs/xi-full-hankel-energy-bound.md links to it. Follow earlier memories mem:research/xi_heat_quadratic_floor_relative_gaussian_frontier_2026_09_27 and mem:research/xi_full_hankel_uniform_floor_quarter_rate_2026_09_26 for existing44 actual-full-family theorems. All prior full family results preserved.

NEW: six HTGeometry leaves, namespace GaloisForLFunctions (NOT .HTGeometry), 24 unconditional theorems, three defs. All warning-free final foreground lake --old env lean leaf audits passed, all six imports wired exactly once, oleans current, no holes/axioms/norm_num/decide/native_decide/computations/heartbeat overrides. Axiom audit97190 exit0:24/24 reports, missing=[], unexpected_axioms={}, diagnostics=[]; only propext/Classical.choice/Quot.sound. Scope whitespace clean. No full or umbrella builds. Source changes not committed/pushed by us; ComplexGaussianTranslationDefect became tracked externally, otherfive new leaves were untracked when last inspected; preserve concurrent changes.

1 HTGeometry/ComplexGaussianTranslationDefect.lean (4thms, leaf60555): exact nonconstant Hasse tail; norm_complexTranslatedPolyGauss_sub_le bounds ||(P(.+z)-P)g||2 <=(exp(|z|sqrt(4pi*d))-1)||Pg||2. EvenSquarePolynomial specialization sqrt8pi*d. Lower margin2-exp. Fixed real Gaussian only.

2 HTGeometry/GaussianPolynomialCoordinateEnergy.lean (4thms, leaf11823): creation/annihilation norms <=A_d||Pg||2, A_d=sqrt(4pi(d+1)); gaussianPolynomialCoordinateNorm_le gives 2pi||xPg||2<=A_d||Pg||2; gaussianPolynomialFullDerivativeNorm_le gives ||(Pg)'||2<=A_d||Pg||2. Based on existing numberCLM_polyGauss_norm_le. Existing RHTower/PolynomialGaussianLocalConcentration has looser16(d+1) derivative-energy bound and useful compact-mass estimate; do not duplicate these.

3 HTGeometry/GaussianPolynomialPhaseDefect.lean (7thms,2defs,leaf40433): norm_modulationMul_eq is isometry; norm_modulationSymbol_sub_one_le <=2pi|a||x|; norm_modulationMul_sub_toLp_le <=2pi|a| ||x f||2; poly specialization <=|a|A_d||Pg||2.
verticalPolynomialGaussianLp P delta =exp(pi delta²) • modulationMul(-delta)(complexTranslatedPolyGauss P (delta*I)).toLp.
coeFn_verticalPolynomialGaussianLp verifies actual amplitude P(x+i delta)*exp(-pi(x+i delta)²), all phase/scalar factors.
verticalPolynomialGaussianDefect d delta =
 exp(pi delta²)*(exp(|delta|sqrt(4pi*d))-1+|delta|sqrt(4pi(d+1)))+exp(pi delta²)-1.
norm_verticalPolynomialGaussianLp_sub_le <=E_d||Pg||2; lower_margin >=(1-E_d)||Pg||2. Every delta, useful margin only when E<1.

4 HTGeometry/GaussianPolynomialParabolicDefect.lean (4thms,1def,leaf61933):
parabolicGaussianDefect epsilon=exp(pi epsilon²)*(exp(|epsilon|sqrt4pi)+|epsilon|sqrt4pi)-1.
verticalPolynomialGaussianDefect_parabolic_le d epsilon: E_d(epsilon/sqrt(d+1))<=E_*(epsilon).
norm_verticalPolynomialGaussianLp_parabolic_sub_le all polynomials, same profile.
parabolicGaussianDefect_tendsto_zero at epsilon0.
eventually_forall_verticalPolynomialGaussianLp_parabolic_lower: one epsilon neighborhood gives half-norm lower floor for ALL polynomials at delta=epsilon/sqrt(d+1).

5 HTGeometry/SchwartzQuadratureEnergy.lean (3thms,leaf92638):
schwartzEnergy_interval_oscillation, interval_quadrature_error, grid_quadrature_error.
All Schwartz f, a real, h:NNReal, sample offsets s:Nat -> Set.Icc 0 1 and N:
abs(integral_a^(a+Nh)||f||² - h sum_(j<N)||f(a+(j+s_j)h)||²)
 <=h integral_same 2||f||||derivSCLM f||.
Geometric point membership is input data; no analytic hypotheses. Local cross integral retained, no cell-count factor. FTC on norm², abs derivative bound, finite adjacent-integral telescoping.

6 HTGeometry/GaussianPolynomialSamplingError.lean (2thms,leaf7162):
gaussianPolynomial_crossIntegral_le:
 integral_R 2|f_P||f_P'|<=2A_d M(P), M=||f_P||2².
gaussianPolynomial_grid_quadrature_error:
 arbitrary grid error <=2h A_d M(P), independent of coefficients and number of cells.
AM-GM plus full derivative norm avoids extra coefficient loss.

Proof audit artifacts: work/xi-relative-gaussian-manifest.json, -axioms.lean/.log, -scope-audit.json, -audit-summary.json, -lint.log. Global metadata lint76654 exit1: five unrelated unwired RHTower modules CCMThetaGroundProfile, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving; stale LEAN_API/LEAN_GAPS/LEAN_OVERVIEW from concurrent changes. Index63442 exit0; final refresh55225 must be confirmed terminal in latest tool/log (do not rerun if completed). No own Lean process remains.

CRITICAL mathematical frontier:
Continuous Lebesgue L2 estimates do NOT automatically transfer to actual Xi counting measure. Each Xi zero has its own imaginary displacement; cannot substitute delta(q) into a constant-delta integral norm theorem. Need vertical-strip maximal or integrated vertical derivative control AND upper local zero counts, in addition to real-axis sampling lower bound.
Next concrete route:
(a) Actual real-axis Gaussian energy K0 from fixed-width zero-window samples, new mesh quadrature, infinite-grid limit, even-polynomial half-line mass, existing low-height concentration.
(b) Bound summed variable-vertical-shift error relative to K0/continuous mass using analytic strip maximal control and actual upper local counts.
(c) Preserve all terms H=K-D; degree/time wedge alone does not meet RH criterion allN/allt>0. No negative actual Xi witness, no all-time propagation proved.

Actual amplitude scaling: Q(t alpha²)*exp(-t alpha²/2) is P(w)*exp(-pi w²) with w=sqrt(t/(2pi))*alpha and P(w)=Q(2pi*w²). Thus degree P=2deg Q and |Im w|<sqrt(t/(2pi))/2. New continuum profile suggests t*(degree+1) scaling only after missing discrete variable-shift transfer; not a proved actual Xi parabolic domain.

Source discoveries read:
RHTower/PolynomialGaussianLocalConcentration.lean: integral_Icc_norm_polynomialGaussianEnergy_le <=18R sqrt(d+1)M, pointwise norm_polyGaussSchwartz_sq_le <=9sqrt(d+1)M; native heat scaling version.
RHTower/XiLogDerivLineOneWindowLower.exists_xiZeroCount_window_ge_log: width h>0 and threshold, count(T+h)-count(T-h)>=log T. Actual copy extraction already proved in XiHeatQuadraticSamplingBands.
RHTower/XiHeatThirdPhaseDefectBound.lean: xiHeatNormMoment, summable_xiHeatNormMoment allk,t=exp tau; can dominate real-coordinate Gaussian terms for K0 summability.
Mathlib MeasureTheory/Integral/IntegralEqImproper.lean line658 intervalIntegral_tendsto_integral_Ioi exists (statement not yet read).
No corpus Gaussian sampling frame theorem found in several research searches; no cards read.

Lean API lessons: NNReal notation requires open scoped NNReal; use explicit (s j : Real) inside mixed additions. For simple NNReal nonneg use h.coe_nonneg, avoid linarith on h.property with hidden coe atoms. Current mathlib mul_le_mul_iff_right₀ hA actually cancels positive LEFT multiplication; match mul_add. add_le_add_right is not old remembered signature: prefer add_le_add h le_rfl. Qualify MeasureTheory.integral_const_mul vs intervalIntegral; give coefficient and integrand to rewrites so they don't rewrite the wrong side. integral_mono_on standalone bindings need explicit volume. Use Pi.add_apply before integral_add rewrite.

Rules: corpus search python3 ../scripts/formal_tools.py research; direct Lean sources, no cards. One owned foreground Lean process at a time; final audit lake --old env lean leaf -o exactolean. No full/umbrella builds. No numerical tactics, holes, extra axioms, raised heartbeats, or commits/push. No proactive subagents authorized. Avoid Serena symbol operations (trigger hidden builds); memory tools okay after activating formal. Final output links only projectless outputs files.