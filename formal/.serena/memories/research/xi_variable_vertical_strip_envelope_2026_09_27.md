Goal ACTIVE: prove/refute RH unconditionally in Lean. This turn PROGRESS, not endpoint. User explicitly requires complete actual Xi forms, all cross terms, no axioms/premises/computations/heartbeat hacks, foreground leaf-only audits --old, corpus research tool/direct Lean/no cards, no full/umbrella builds, no commits/push. No subagents authorized. Prior mem:research/xi_actual_real_axis_gaussian_floor_2026_09_27, mem:research/xi_relative_gaussian_phase_quadrature_frontier_2026_09_27 remain valid.

Repo /Users/michael/Documents/code/hgt/formal. Projectless /Users/michael/Documents/Codex/2026-09-26/new-chat-3. Log work/xi-curvature-rh-loop.md. New report outputs/xi-variable-shift-control.md; prior real-axis report links forward.

NEW FOUR HTGeometry leaves; namespace GaloisForLFunctions (NOT .HTGeometry);19theorems,5definitions. ALL passed warning-free final foreground lake --old env lean leaf -o exactolean:
GaussianHasseTailEnvelope leaf53854 exit0
GaussianVerticalStripEnvelope leaf78394 exit0
GaussianPolynomialSamplingUpper leaf29143 exit0
GaussianVariableVerticalShift leaf5276 exit0
All4 wired once to HTGeometry umbrella, current oleans, forbidden-source scan empty, scoped git diff --check clean.
AXIOM audit34348 exit0:19/19 present,missing=[],unexpected_axioms={},diagnostics=[]; standardpropext/Classical.choice/Quot.sound only.
Index2843 exit0. Global metadata lint39156 exit1 for5UNRELATED unwired RHTower leaves CCMThetaArithmeticCorrelation, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving, plus LEAN_API/LEAN_OVERVIEW stale. FINAL INDEX18158 CONFIRMED EXIT0. Every owned process terminal. No temporary API files/cleanup pending. No full/umbrella builds, commits/push. DO NOT repoll/restart finished handles.
Artifacts work/xi-variable-shift-manifest.json, -axioms.lean/.log, -scope-audit.json, -audit-summary.json, -lint.log.

MATHEMATICS:
F_P(z)=P(z)exp(-pi z²),d=natDegreeP,N=||Freal||2,M=N²,R>=0.
A0=sqrt(4pi*d),A1=sqrt(4pi*(d+1)).
E_d(R)=exp(piR²)*(exp(RA0)+R A1)-1 = existing verticalPolynomialGaussianDefect d R.
Explicit simultaneous envelope
B(P,R,x)=exp(piR²)*(sum_{k=1}^d R^k|hasse_k(P)(x)g(x)|+2piR|xP(x)g(x)|)
 +(exp(piR²)-1)|P(x)g(x)|.
For EVERY x and EACH delta with |delta|<=R, |F(x+i delta)-F(x)|<=B(x).
MemLp B 2 volume; ||B||2<=E_d(R)N. This is stronger than fixed-shift L2 control: ONE pointwise envelope permits a different delta at every sample.
All polynomial cross terms stay inside whole P/Hasse evaluations and reference M; triangle inequalities bound correlations, no coefficient diagonalization.
For ANY continuous graph delta:R->Icc(-R,R), entire F along graph and its difference from F are MemLp, errorL2<=E N, normlower>=(1-E)N. NO derivative/Lipschitz constraint on graph.
R=epsilon/sqrt(d+1) gives E<=parabolicGaussianDefect epsilon from prior theorem. One common exp(tau) cutoff gives half-norm lower for ALL polynomials and graphs after degree-normalized radius. NOT all degrees at fixed heat time.

APIs:
1 HTGeometry/GaussianHasseTailEnvelope.lean (5thms,1def):
gaussianHasseTailEnvelope P R x: finite nonconstant absolute Hasse tail.
gaussianHasseTailEnvelope_nonneg P R x.
norm_complexTranslatedPolyGauss_sub_le_envelope (P)(R:NNReal)(z:Metric.closedBall (0:Complex) R)(x:Real).
memLp_gaussianHasseTailEnvelope P R.
lpNorm_schwartz_eq f: MeasureTheory.lpNorm f 2 volume=||f.toLp2volume||.
lpNorm_gaussianHasseTailEnvelope_le P R: <=(exp(Rsqrt4pi*d)-1)*N.

2 HTGeometry/GaussianVerticalStripEnvelope.lean (5thms,1def):
gaussianVerticalStripEnvelope as B above.
gaussianVerticalStripEnvelope_nonneg.
polynomialGaussian_vertical_eq P x delta: full entire eval equals exp(pi delta²)*modulationSymbol(-delta)x*complexTranslatedPolyGauss P (delta I)x, pointwise exact.
norm_polynomialGaussian_vertical_sub_le_envelope P (R:NNReal) x (delta:Icc(-R)R).
memLp_gaussianVerticalStripEnvelope.
lpNorm_gaussianVerticalStripEnvelope_le: <=verticalPolynomialGaussianDefect d R *N.

3 HTGeometry/GaussianPolynomialSamplingUpper.lean (3thms,1def):
gaussianPolynomial_grid_energy_upper P a(h:NNReal)(s:Nat->Icc0,1)N:
h sum_{j<N}|F(a+(j+s_j)h)|² <=(1+2h sqrt4pi(d+1))*M.
NO N factor.
gaussianGridSamples a h s N(f:Real->Complex):EuclideanSpace Complex (Fin N)
 :=sqrt h • WithLp.toLp2(fun j=>f(a+(j+s_j)h)).
gaussianGridSamples_norm_sq: exact h*sumrange norm².
norm_gaussianGridSamples_polyGauss_le: <=sqrt(1+2h sqrt4pi(d+1))*N.

4 HTGeometry/GaussianVariableVerticalShift.lean (6thms,2defs):
variableVerticalPolynomialGaussian P R(delta:C(Real,Icc(-R)R)) x actual F(x+i delta(x)).
memLp_variableVerticalPolynomialGaussian_sub,
memLp_variableVerticalPolynomialGaussian,
lpNorm_variableVerticalPolynomialGaussian_sub_le,
lpNorm_variableVerticalPolynomialGaussian_lower_margin.
polynomialGaussianStripRadius P(epsilon:NNReal):NNReal :=epsilon/sqrt(d+1).
lpNorm_variableVerticalPolynomialGaussian_parabolic_sub_le P epsilon delta.
eventually_forall_variableVerticalPolynomialGaussian_parabolic_lower:
eventuallytauatBot,forallP,forallcontinuousdelta in stripradius(P,exp tau),
N/2<=lpNorm(actual variable amplitude)2volume.

NEXT CONJECTURE (still unproved):
For arbitrary grid samples x_j=a+(j+s_j)h and variable |delta_j|<=R:
h sum_j |F(x_j+i delta_j)-F(x_j)|²
 <=(1+2h sqrt(4pi(d+2)))*E_d(R)²*M.
Mechanism:
- finite GaussianGridSamples Hilbert norm triangle.
- pointwise strip envelope above.
- apply grid upper sampling to Hasse_kP (degree<=d) and XP (degree<=d+1).
- coordinate L2 norm<=sqrt4pi(d+1)/(2pi)*N.
- common grid operator ceiling sqrt(1+2h sqrt4pi(d+2)); finite Taylor factorial sum gives same E, no cell-count loss.
Build helper grid linear/norm-of-norm properties if needed; preserve exact sums.
Then selected actual Xi window copies with mesh rh and |delta_j|<=r/2 transfer real sample half-line lower to actual complex K. Elementary ||u+v||²>=||u||²/2-||v||² gives floor without reverse triangle square subtleties.
IMPORTANT: previous K0 lower is complete real-ordinate sum; selected subset lower must be extracted from finite quadrature plus half-line integral, not falsely inferred from K0. Existing actual grid theorem provides injection and adjacent-cell samples.
IMPORTANT: phase debt includes ALL divisor copies. Selected-sample error estimate can lower-bound K, but CANNOT upper-bound full debt. Need full divisor local-count upper estimates; possibly use multiplicity-rich log-height lower windows to preserve matching density scales.
Full RH endpoint remains forallN,a,t>0 H_N>=0. Only small-time/degree-normalized region currently proved; no actualnegativewitness or alltimepropagation.

Source searches this turn:
formal_tools.py research 'Gaussian variable shift' and 'Gaussian grid upper' found no direct applicable theorem. Read actual prior PhaseDefect, TranslationDefect, CoordinateEnergy, SamplingError, Mathlib lpNorm/Schwartz/PiLp definitions. No cards or literature claims.

Lean lessons:
- NNReal.property proves val>=0; NNReal.coe_nonneg matches toReal coercion in rewrite and nlinarith. Using .property caused visually identical unmatched atoms. Use .coe_nonneg for scalar comparisons.
- Explicit change required for NNReal constructor coercions before rewriting; dsimp[NNReal.coe_mk] sometimes no progress.
- memLp_finsetSum is pointwise-sum version; memLp_finsetSum' function-sum version. Deprecated snake aliases warn.
- Convert function-sum via Finset.sum_fn, smul function via Pi.smul_def.
- Generic root sub_apply/smul_apply replace deprecated SchwartzMap equivalents.
- lpNorm_schwartz_eq uses SchwartzMap.norm_toLp and toReal_eLpNorm.
- For real nonnegative scaling lpNorm_const_smul, change RHS nnnorm coercion to real norm then rw Real.norm_eq_abs,abs_of_nonneg.
- Fin.sum_univ_eq_sum_range needs explicit Nat->Real function to avoid stuck AddCommMonoid.
- add_le_add of explicit le_refl avoided add_le_add_right orientation confusion.
- Do not use Serena symbol calls (can trigger hidden builds); memory tools safe after projectactivation.
