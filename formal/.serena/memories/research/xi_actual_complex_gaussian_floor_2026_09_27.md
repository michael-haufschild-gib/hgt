Goal remains ACTIVE: prove or refute RH unconditionally in Lean. Previous turn PROGRESS: actual full complex Xi Gaussian relative floor and discrete varying-shift error now verified. No full phase-debt domination or all-time RH conclusion. Do not mark complete.

Repo /Users/michael/Documents/code/hgt/formal. Projectless /Users/michael/Documents/Codex/2026-09-26/new-chat-3. Work log work/xi-curvature-rh-loop.md. Report outputs/xi-complex-gaussian-floor.md, prior variable-shift and real-axis reports link forward. Predecessor mem:research/xi_variable_vertical_strip_envelope_2026_09_27 and mem:research/xi_actual_real_axis_gaussian_floor_2026_09_27 remain relevant.

Rules: unconditional final statements/no added analytic hypotheses or axioms; data parameters/positive scale geometric subtypes accepted. No numerical computations or norm_num/decide/native_decide/#eval. One owned foreground Lean process, final lake --old env lean leaf -o matchingolean. No full/umbrella builds; wire completed modules once. No heartbeat overrides/proofholes. Corpus research tool directly via python3 ../scripts/formal_tools.py research '<query>' --budget-seconds45, direct Lean only/no cards. No commits/push or subagents authorized. Preserve concurrent work. Serena memory tools safe; avoid symbol tools causing hidden builds. Reports linked only projectless outputs.

LATEST SIX LEAVES,19theorems,4defs, all warning-free:
HTGeometry/GaussianGridSamplingAlgebra final46706 exit0 (5thms,1def)
HTGeometry/GaussianGridHasseEnvelope final62361 exit0 (5thms,1def)
HTGeometry/GaussianStripSamplingError final68274 exit0 (2thms)
RHTower/XiScaledEvenGaussianEnergy final42513 exit0 (4thms,2defs)
RHTower/XiComplexGaussianSampling final72159 exit0 (1thm)
RHTower/XiComplexGaussianCoercivity final72375 exit0 (2thms).
HT namespace GaloisForLFunctions, RHT namespace RHTower.
All6 wiredonce,matchingcurrentoleans,forbidden source scanempty,scoped gitdiffcheckclean.
AXIOM64324 exit0:19/19 expected reports,missing=[],unexpected_axioms={},diagnostics=[]; standardpropext/Classical.choice/Quot.sound only.
Index97284 exit0. Global metadata lint85166 exit1:5 unrelated unwired RHTower modules CCMThetaThreeEnergyComparison,MoebiusMollifiedCriticalMoment,MoebiusMollifiedErrorThreeLines,MoebiusMollifiedZetaField,ZetaZeroDensityPowerSaving;3 stale generatedfiles LEAN_API,LEAN_GAPS,LEAN_OVERVIEW. FINAL INDEX37566 CONFIRMED EXIT0.
EVERY owned process terminal; no scratchcleanup pending. No full/umbrella builds/commits/push. Do NOT repoll/restart completed handles.
Artifacts work/xi-complex-gaussian-manifest.json, -axioms.lean/.log, -scope-audit.json,-audit-summary.json,-lint.log.

NEW MATHEMATICS:
For real P, F_P(z)=P(z²)exp(-pi z²), d=2natDegreeP, M=||Freal||2²,
K(P,r)=sum_q |F_P(r alpha_q)|² over ALL XiZeroCopy with analyticmultiplicity,r>0.
Exact amplitude²=xiPolynomialGaussianHeatTerm(P.comp(C(r²)*X),2pi*r²,q).
Thus actual heat normalization Q_r(X)=P(r²X),t=2pi r².
Existing complete defect E_d(R)=exp(piR²)*(exp(Rsqrt4pi*d)+R sqrt4pi(d+1))-1.
Fixedactual h,C>0 independent of allP,r:
rh*K(P,r)>= [1/4-C*r sqrt(d+1)
 -(1+2rh sqrt4pi(d+2))*E_d(r/2)²]*M.
C=9a/2+h sqrt4pi wherea,hactualzero windows.
One COMMON tau cutoff, r=exp(tau)/sqrt(d+1), gives rh*K>=M/8 for EVERY realP/allcoefficients/alldegrees.
This is degree-normalizedscale (small t(d+1)), not all degrees at fixed time.
Independent of RH/phase-debt assumptions. All polynomial coefficient crossterms remain in whole evaluations/energies. Actual full complex points, not realreference only.

DISCRETE VARYING-SHIFT ESTIMATE:
For arbitrary realQ, degree n, grid x_j=a+(j+s_j)h,0<=s_j<=1 and arbitrary per-index |delta_j|<=R:
h sum_(j<N) |Q(x_j+i delta_j)exp(-pi(x_j+i delta_j)²)-Q(x_j)g(x_j)|²
 <=(1+2h sqrt4pi(n+2))*E_n(R)²*||Qg||2².
NO sample-count factor, coefficientindependent. Allows differentdelta even if samplecoordinatescoincide.
Actual grid from exists_xiRealAxis_sampling_grid hasinjectiveq inadjacentwindow; eachshift r*imAlpha lies[-r/2,r/2].
Realreference²<=2complex²+2error², sum andupperboundselectedcomplexsumbyfullK, thenGaussianquadrature andinfiniteintervallimit give halfline mass control. Even lowheight mass theorem finishesfullKfloor.
Selectedsamples ONLY lowerboundK; cannotupperboundphaseDoverALLcopies.

APIs:
1 GaussianGridSamplingAlgebra:
gaussianGridSamplingLM a(h:NNReal)sN:(Real->Complex)->_Complex EuclideanSpaceComplex(FinN).
gaussianGridSamples_add, gaussianGridSamples_smul, gaussianGridSamples_sum;
norm_gaussianGridSamples_norm: norm of sampling pointwisenormcast equalsoriginal samplingnorm.
mulXCLM_polyGauss_eq P: mulXCLM(polyGauss P)=polyGauss(X*P).
2 GaussianGridHasseEnvelope:
gaussianStripSamplingFactor d h=sqrt(1+2h sqrt4pi(d+2)), nonneg.
norm_gaussianGridSamples_polyGauss_le_stripFactor.
norm_gaussianGridSamples_hasse_le_stripFactor P k: samefactororiginaldegree.
norm_gaussianGridSamples_coordinate_le:2pi*normsamples(xPg)<=factor*A_d*||Pg||.
norm_gaussianGridSamples_hasseEnvelope_le: <=factor*(exp(Rsqrt4pi*d)-1)*||Pg||.
3 GaussianStripSamplingError:
norm_gaussianGridSamples_stripEnvelope_le P R a h s N: <=factor*E_dR*||Pg||.
gaussianPolynomial_grid_variableShift_error P R a h s N(delta:Nat->Icc(-R)R): squaredboundabove.
4 XiScaledEvenGaussianEnergy:
xiScaledEvenGaussianAmplitude P(r:{r:Real//0<r})q :=evenSquareP.eval2(r*alpha)*exp(-pi(r*alpha)²).
xiScaledEvenGaussianEnergy P r:=tsumnormamplitude².
xiScaledEvenGaussianAmplitude_sq exactexistingheat term above.
summable_xiScaledEvenGaussianAmplitude_norm_sq.
xiScaledEvenGaussianEnergy_nonneg.
xiScaledEvenGaussianAmplitude_vertical exact evalat rRealpha+i*rImalpha.
5 XiComplexGaussianSampling:
exists_xiComplexGaussian_halfLine_sampling_bound:existsa>0,h>0,forallP,r>0,
integral_(ra)^infty |Freal|² <=2rh*K+(2rh sqrt4pi(d+1)+2(1+2rh sqrt4pi(d+2))*E_d(r/2)²)*M.
6 XiComplexGaussianCoercivity:
exists_xiScaledEvenGaussian_relative_floor:fullKrelativeformulaabove.
exists_eventually_forall_xiScaledEvenGaussian_parabolic_floor:commonτ/M8.
Uses existing xiGaussianParabolicScale from realaxisfloor.
Uniformτ proof bounds sqrt(d+2)<=2sqrt(d+1), factor<=1+4h sqrt4pi expτ,
E_d(r/2)<=parabolicGaussianDefect(expτ/2), and continuous G(u)=C*u+(1+4h sqrt4pi*u)*parabolicDefect(u/2)²->0.
No unsupplied hypothesis.

NEXT FULL-PHASE-DEBT CONJECTURE (UNPROVED):
For arbitrary realQ degree d,B=gaussianVerticalStripEnvelope Q R, N=||Qg||2:
|x|*B(x)<=W_d*E_d(R)*N,
W_d²=(1+2sqrt(4pi(d+3)))*(d+2)/pi.
Proofsuggestion:
Singleton grid h=1 givespointnorm ceiling S_d=sqrt(1+2sqrt4pi(d+3)) on polynomials degree<=d+2.
CoordinateHasse x*Hasse_kQ costs A_d/(2pi); x²Q costs A_(d+1)A_d/(2pi)², A_d=sqrt4pi(d+1).
Takecommon extraA_(d+1)/(2pi), apply exactthree envelopecomponents/Hassefactorialtail.
Atactual x=rRealpha, sector ||alpha||²<=2Realpha² gives r²||alpha||²B²<=2x²B².
S2=tsum1/||alpha||² finite.
Then fullsum B(rRealpha)²<=2*S2*W_d²*E_d(r/2)²/r²*M.
ActualD=2sum(ImAmp)²<=4*S2*W_d²*E_d(r/2)²/r²*M (realreferencehaszeroim).
CompareagainstK>=M/(8rh); expect polynomialjointdegree/time horizon r*d^(5/2)small or t*d^5small. These rateclaims are HEURISTIC/UNPROVED, noRHsufficiencyclaim.
Need actual summability/fullK-D linkage, notselectedsum. This is baselinewhilebuildingstrongerlogweightedcountcontrol, notreplacementofalltimeobjective.

FULL COUNT INFRA FOUND VIA CORPUS/DIRECT SOURCES:
RHTower/XiWindowZeroCount.lean importsLorentzianZeroMass.
xiOrdinateWindow w t={q:XiZeroCopy ||Imrho_q-t|<=w}.
finite_xiOrdinateWindow w t unconditional.
ncard_xiOrdinateWindow_le_log w t:
ncard(window)<=8(1+w²)*(xiLineTwoLogDerivConstant+log(|t|+4)),ALL realw,t.
ncard_xiOrdinateWindow_one_le_log t<=16*(C+log(|t|+4)).
RHTower/XiZeroCountLocalCeiling.lean:
exists_xiZeroCount_window_le,exists_card_window_le yield (H/(2pi)+2C)*log(t+H) for t>=T0,H>=0; includesallcopies.
XiLogDerivLineOneWindowLower.exists_xiZeroCount_window_ge_log:fixedwidthh, forlargeT,logT<=N(T+h)-N(T-h), exactmultiplicity.
This suppliesfull-divisor uppercounts andmultiplicityrich lowercounts. For sharperphasecontrol usecompatiblelogweightedGaussianestimates. A onecopypercellKfloorcanloselogdensityrelativetofulldebtupper.

Fresh research queries: 'Gaussian strip sampling','xi complex Gaussian energy','xi local count upper','xiZeroCount window'. Noexistingdirectdiscretevariableerror/actualcomplexfloorfound. Direct Lean read countmodulesabove.
Lean lessons:
- Imported add_le_add_left/right names have sideorientation opposite assumptions; use add_le_add (le_refl1) or add_le_add _ le_rfl explicitly.
- LinearMap field .map_sum unavailable; use root map_sum lm f J; change target into lm form before simp[Finset.sum_fn].
- NNReal.coe_nonneg matchescoercions; .property causedprioratom mismatch.
- PositiveReal subtype positivity tactic needs explicit have hrpos:0<(r:Real):=r.property. Radiusnonneguse div_nonneg r.property.le.
- Finite halfline hfinite vs final RHS differed onlyassociation2*(factor*E²) vs2*factor*E²; simpa only[localdefs,mul_assoc] closed.
- Avoid shell globs Xi* as explicitrgfileargs: theyinclude.ilean despite-g; search directory with-g'*.lean' instead.
