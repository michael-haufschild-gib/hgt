# Latest WP06 checkpoint — 2026-10-08 C12g/G1
Main goal ACTIVE/UNSOLVED: docs/reports/weil-work/06-spectral-deficit.md. No unconditional upper-deficit producer, C11q construction, or RH conclusion. This checkpoint supersedes older module counts.

22 completed owned modules / 93 public theorem axiom audits. New formal/GaloisForLFunctions/RHTower/WeilWorkDeficitTwistedGapBudget.lean (namespace RHTower.WeilWorkDeficitGap) has two public theorems:
- summable_twistedGapWeight: whole positive-pair reciprocal-square gap sum is summable, T>=0,n>=1.
- tsum_twistedGapWeight_le: for T>=1,n>=1, sum <= (48*n^2*integerGapBudget+16*pairZeta)*T.
Actual summand: (rm)^(-1/2)*min(1,T/(rm))^2/(log(m/r)-log n)^2. Diagonal zero by field division convention. integerGapBudget=sum_z in Z 1/z^2. No scientific premises.
Proof: near detuning<1/4 implies nr/2<=m<=2nr; reciprocal log gap <=(2nr)^2/(m-nr)^2; integer gaps inject into Z. Radial r*min(1,a/r^2)^2 <=sqrt(a)*min(1,a/r^2), total<=3a. Far detuning>=1/4 uses16*pairWeight, total<=16*pairZeta*T^.75. Complete tails included.
Audit: target lake --old build +GaloisForLFunctions.RHTower.WeilWorkDeficitTwistedGapBudget exit0,target16s,9501 jobs cached replay; final unchanged lake --old env lean GaloisForLFunctions/RHTower/WeilWorkDeficitTwistedGapBudget.lean exit0/empty; /tmp/wp06-c12g-gap-axioms.lean exit0, both public standard-only propext/Classical.choice/Quot.sound, exact types inspected. Umbrella wired (line may change). Scoped whitespace clean. Latest lint7 unrelated unreachable modules: WeilWorkHigherDenominatorInversionFourier, WeilWorkQuantizationRationalResonance, ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No own/forbidden finding. All owned processes terminal; prototype /tmp/wp06-c12g-gap.lean and API scratch removed; audit source/logs retained. No full/umbrella build, heartbeat change, numerical computation, commit.

NEW PAPER PROOF in owned PROOF.md:
C12g for fixed n>=1,c>0,H=c*sqrt(T):
integral exp(-((t-T)/H)^2)*abs(zeta(1/2+it))^2*exp(-it log n) =
sqrt(pi)*H*log(T)/sqrt(n)+O_(n,c)(H).
Use EXISTING ZetaSquareStirlingAFE.exists_norm_zetaSq_sub_symmetricAFE_le, not sharp Riemann-Siegel/chirp (superseded). Actual smoothAFECutoff is Gaussian upper tail (SmoothAFECutoffGaussianTail); first two log derivatives have min(1,x^-2) bounds. With fixed compact chi(t/T), F_P=chi*Gaussian*V(2piP/t), L1 second derivative <=C/H*min(1,T/P)^2. Two IBPs + new G1 giveO_n(T/H). AFE remainderO(logT). Two diagonals=2/sqrt(n)*integral Gaussian*diagHarm(t/(2pi n)); existing ZetaSquareDiagonalHarmonic.exists_norm_diagHarm_sub_le supplies .5log x+gamma+O(x^-1/4). Polynomial zeta bound removes chi.
C12 paper transfer complete: paperFT_riemannKernelDeriv+Plancherel imply A(n,k)=1/(2pi)integral t^(2k)|XiC(t)|^2 cos(t log n). GammaVerticalRatioAsymptotic.gamma_vertical_ratio_norm_rpow_tendsto at a=delta=1/4 plus exact HTGeometry.GammaVerticalModulus.norm_Gamma_half_add_I_sq yields |Xi|²~sqrt(pi/2)*t^(7/2)e^(-pi*t/2)|zeta|². p=2k+7/2,T=p/(pi/2),H=sqrt(2T/(pi/2)),B=T^p e^(-pi*T/2). Laplace/Gaussian difference <=C*T^-1/2*|s|³ e^-c s² on[T/2,2T]; untwisted C12g paysO(logT), other tails exponentially small, Gamma relative erroro1 uniform. A(n,k)/(sqrt(pi/2)*B*H*logT/sqrt(pi))->1/sqrt(n), divide n=1.
Thus C12 limit paper-proved and fixed finite rows eventually strictly positive. NO Lean C12 theorem yet; G1 only new formal input. Do not claim O(1/logk) for full Xi ratio: current Gamma input is only convergence. Classical-parent BRIDGE; no external scientific novelty claim. Does not settle coupled n~k or C11q.

NEXT CONJECTURE C13 (OPEN, exact PROOF statement): exists k0,M0 such that M>=M0,k>=k0,100k<=M implies sum_(2<=n<=M) Lambda(n)*A(n,k)/sqrt(n) >=(1/4)*log(k+2)*A(1,k). Competing arbitrarily-large failure. Source motivation: literal weilFullFunctional=poles-primes+gamma; WeilWorkPBAPJointCoercivity.joint_gamma_lower_log gives log(2+|t|)-(10+log4); actual derivative zero transforms; C10u full tail and C12 untwisted norm lower bound. MUST pay noncompact explicit-formula passage, pole signs/normalization, uniform factorial comparison, finite cutoff. Preserve low-order k<k0 exceptions; no full cone separation follows.
Plan: complete C12 analytical Lean assembly while attacking C13/complementary coupled-order C11q cost; do not add more unneeded representations.

Current-turn hgtl7 full skill read; all9 review answers posted; primary Oct2026 audit Tang/Baluyot/Motohashi/NIST/Paris, no endpoint theorem imported. Corpus queries gaussian-frontier,cutoff-frontier,c13-truncated-prime-dual all terminalpartial=false/errors=[], all candidate/source statements inspected; indexed68617/68618/68625 but only43 current compiler snapshots and incomplete background refresh, not absence certificates. Relevant exact files read: ZetaSquareStirlingAFE704-780, ZetaSquareDiagonalHarmonic464-505, SmoothAFECutoffGaussianTail whole, ZetaNotchResonanceCount1-265, Sieve/TwistedOffDiagonalSum1-120, ZetaMollifiedShortWindowMeanSquare1-180 and270-320, GammaVerticalRatioAsymptotic150-200, RiemannKernelCuspSeries535-559, WeilFullConeRiemannKernelRigidity252-277, WeilWorkPBAPPacketEnergy1-55 and JointCoercivity96-132.
Updated owned card, RESULT, PROOF, EVIDENCE, lean-audit.log. All latest G1 logs /tmp/wp06-c12g-gap-*; rawaxioms also persistent owned lean-audit.log.

---
Earlier checkpoints (historical):
# WP06 spectral-deficit frontier — 2026-10-08

## LATEST checkpoint — C11b completed; supersedes earlier counts/status below
ACTIVE/UNSOLVED goal. 21 finished owned modules /91 public theorem axiom audits.
New `formal/GaloisForLFunctions/RHTower/WeilWorkDeficitBesselCorrelation.lean` (about442 lines), namespace `RHTower.WeilWorkDeficitBessel`.
Seven public theorems:
- summable_divisor_bessel (279): complete positive-product divisor series.
- monomial_correlation_bessel (284): exact full theta monomial convolution.
- integrable_cusp_correlation (307), cusp_correlation_bessel (319): every real polynomial pair, every real shift, no hypotheses.
- derivative_correlation_bessel (354), integrable_derivative_correlation (370): every actual mixed derivative pair; k=l,y=log n identifies C11 matrix.
- riemann_correlation_bessel (395): κ(y)=e^(y/2) Σ_N d(N)[(x⁴+9x²)K0(x)-6x³K1(x)], x=2πN e^y. N=0 term has zero divisor multiplicity.
All positive factor pairs retained, absolute-integral sum proved, full finite coefficient assembly. K order j-l equals absolute order by evenness. BRIDGE with classical Koshliakov ancestry, no novelty/sign/cancellation/deficit-upper conclusion.
Validation terminal: target `lake --old build +GaloisForLFunctions.RHTower.WeilWorkDeficitBesselCorrelation` exit0,target99s/9883jobs; final unchanged `lake --old env lean GaloisForLFunctions/RHTower/WeilWorkDeficitBesselCorrelation.lean` exit0/empty; `/tmp/wp06-c11b-axioms.lean` exit0, all7 standard-only. Exact public types inspected. Umbrella import wired. Logs `/tmp/wp06-c11b-{build,final,axioms,lint}.log`; persistent output in owned lean-audit.log. Scoped whitespace clean. Latest lint15 unrelated reachability errors (6 HigherDenominator,1 Quantization,3 SettledPhase,5 HTGeometry), no WP06/forbidden finding. Do not fix unrelated modules. No full build, numerical experiments, heartbeat increase, commits. Scratch source/fragments removed; final audit files retained. All owned processes terminal. Both rounds of 9 review answers posted.

PROOF now has complete paper C11b B1-B6: arbitrary polynomial divisor-Bessel representation, absolute Fubini, U/V two-channel recurrence and leading coefficients, actual matrix. U/V recurrence remains paper-only; actual mixed-order identity is formal via generic polynomials. C11/C11q still OPEN.
C12 exact open conjecture: for every fixed integer n≥2, A(n,k)/A(1,k)→1/√n. Competing arbitrary-high-order negative ratio remains unrefuted. Positivity of two polynomial channels does not settle their difference.
Inspected `WeilZetaSquareMoments`, `WeilZetaSquareDilationRigidity`, `ZetaNotchTwistMainTerm`: broad windows; cannot specialize to gamma-weight concentration width sqrt(height). Tang Aug2026 arxiv:2608.14852 Theorem1/Remark3.1 read: δ>1/2, distinct odd primes, dual moment retained; no endpoint input.
Primary classical ancestry: Berndt–Dixit–Gupta–Zaharescu §13, https://adixit.people.iitgn.ac.in/wp/wp-content/uploads/2023/03/askey_special.pdf (Koshliakov1934 Xi-square integral).
Fresh searches all terminal/inspected: `/tmp/wp06-c11b-formal-frontier.json` (partial=false,68583 files), `/tmp/wp06-c12-fixed-twist-error.json` (partial=false,68594, mostly irrelevant), `/tmp/wp06-c12-divisor-boundary.json` (partial=false,68605). Compiler only43 current snapshots, most pending/stale; refresh incomplete, no absence certificate.
New useful source: `CCMFUSuzukiMobiusDivisorAbelProducer`1–80 read: primeFreeDivisorDefect=log(N!)-Σ_d≤N floor(N/d)+2γN, absolute bound24sqrtN. `DivisorUniformSquareRootBound`1–180 read: uniform source/channel ceilings; do not confuse them with κ coefficient asymptotics. Also `Sieve/TwistedMainTermMerge`1–100 and `EstermannGrowth`1–90 read: main-term pole cancellation and functional-equation edge bounds, not short-window estimate.
C12a paper estimate audit: even granting the leading complex Bessel reduction, naive Abel absolute bound from O(sqrtX) divisor remainder gives Laplace error O(σ^-4+|z|σ^-5). On radius(π/2)(1-1/K), angular arcK^-1/2 gives σ~K^-1,|z|~K^-1/2; absolute coefficient error bound K^4 exceeds expected K^(7/2)logK. This is a deficient bound, not C12 refutation. Complex-sector Bessel reduction and contour cancellation not proved. Next: pay angular/arithmetic cancellation or exact weighted twisted moment, or return directly to C11q construction/finite dual. Do not spend cycle merely re-formalizing real divisor bound or unnecessary U/V recursion.

## Earlier context (historical counts/checkpoint statuses superseded above)


## Goal / scope
ACTIVE, UNSOLVED unbounded user goal. Solve docs/reports/weil-work/06-spectral-deficit.md: for arbitrary hW : WeilPositiveFull lam, every eta>0 has frequently T atTop with actual deficitCount hW T/T <= eta. Deficit counts ALL XiZeroCopy multiplicities, off-line copies at unit cost, missing canonical critical atom shares. No upper-deficit producer proved. Receiver gives lam=vonMangoldt n>=2 and RH for a supplied positive datum; no positive datum produced.
User requires hgtl7 workflow EVERY goal turn, corpus-first conjecture/attack/paper proof/Lean loop, never retire for difficulty. No mathematical computations/numerical experiments, no added scientific premises/axioms, no heartbeat increases, no full/umbrella builds. One owned foreground Lean/build at a time. Target builds use lake --old build +Module; FINAL unchanged audit lake --old env lean path. Wire umbrella. No commits/pushes/subagents. Preserve concurrent unrelated changes. Docs architecture/testing absent at init. update_plan and multi_tool_use tools unavailable; working card carries plan. Serena ignores Lean files, so standard file edits after reading; use rg for text.

## Completed checkpoint: TWENTY modules /84 PUBLIC theorem axiom audits
Previous19/79 plus NEW formal/GaloisForLFunctions/RHTower/WeilWorkDeficitUniformDerivativeBudget.lean, namespace RHTower.WeilWorkDeficitDerivativeBudget, ~447 lines, five public theorems:
1 kernel_derivative_factorial_envelope line194.
2 packet_factorial_envelope line277.
3 correlation_factorial_bound line312.
4 weighted_correlation_factorial_bound line367.
5 weighted_tail_factorial_bound line418.
For 0<a<pi, exact C=3+4pi/(pi-a) and one B>0 work for ALL k,u:
 norm(Phi^(k)(u)) <= B C^k (k+2)! exp(-a exp(2|u|)) exp(-|u|).
Public packet k c = sum_j c_j Phi^(k_j); budget C k c = sum_j norm(c_j) C^(k_j)(k_j+2)!. Arbitrary finite complex packets/all orders. Literal full correlation integral integrable, bounded by B budget^2 exp(-2a exp|y|).
For 0<r<2pi, exact C_r=3+16pi/(2pi-r), one B_r bounds full actual weighted term and complete tail from N+2 by B_r budget^2 exp(-r(N+2)); tail summability is included. Weight reuses WeilWorkDeficitBudget.weight n = vonMangoldt(n+2)+WeilWorkPBAP.atomCost(logIndex n), not a surrogate. At r=pi, C_r=19 exactly. Constants precede all orders/counts/coefficients. This is BRIDGE, no scientific novelty, no positive cancellation construction, no sharpness claim.
Proof: coefficient weight abs(P_k.coeff j)*j!/delta^j, delta=(pi-a)/2, exact cusp coefficient recurrence and degree<=k+2. Uniform weight <=A C^k(k+2)!. Exponential-series sum bounds actual polynomial by A C^k(k+2)! exp(delta t). ENTIRE theta sum bounded geometrically, parity gives global envelope. Product-envelope identity 2exp|y|<=exp(2|u|)+exp(2|u-y|) gives integrability/full correlation; actual atomCost polynomial bound plus quadratic exponential absorption gives full weighted tail. Paper C10u recorded BEFORE Lean in PROOF.
Validation of FINAL strengthened source:
- /tmp/wp06-c10-explicit-build.log: target-only build exit0, target114s,13456 jobs mostly replays.
- /tmp/wp06-c10-explicit-final.log: final unchanged direct audit exit0, zero bytes.
- /tmp/wp06-c10-axioms.lean and /tmp/wp06-c10-explicit-axioms.log: all5 #print axioms and specialized arbitrary-degree real-packet tail / exact base19 examples exit0. All5 only propext, Classical.choice, Quot.sound. One harmless sequence-style warning in /tmp example; no target-source diagnostics.
- Umbrella import at formal/GaloisForLFunctions/RHTower.lean ~7088 (line can shift with concurrent work), explicitly wired.
- /tmp/wp06-c10-final-lint.log exit1: EIGHT unrelated reachability errors, no WP06 or forbidden declaration findings: WeilPaperPacketPrimitiveInterpolation, WeilWorkHigherDenominatorBesselBoundary, WeilWorkHigherDenominatorFourierBoundary, HTGeometry ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Do not fix outside scope.
- Scoped tracked whitespace checks exit0; source no-index check no diagnostics (exit1 means new file).
All owned processes terminal. No unfinished owned Lean source. /tmp analytic/tail draft fragments removed; audit source/logs retained. Latest RESULT/EVIDENCE/PROOF/lean-audit.log and pipeline card updated. Date rolled to Oct8 via environment message while working. hgtl75 anti-theatre and4 anti-laziness answers posted explicitly. No goal completion/blocking.

## Previous C8 completed (19/79 checkpoint)
WeilWorkDeficitXiApproximationCost.lean namespace WeilWorkDeficitApproximation. Four public: paperFT_error_at_zero, zero_approximation_cutoff_bound, exponential_budget_error_bound, double_exponential_variation_bound. For actual real Xi zero gamma, finite complex Phi-translate packet shifts[-a,a], variation V, physical L2 error E vs exp(-i gamma u)Phi(u), h=norm XiC0>0: exact FT error atgamma=-XiC0; h<=sqrt(2L)E+2B(V+1)exp(-exp(2(L-a))); V<=exp N gives h²<=8(a+log(N+K))E² with universalK>1; E>0 and exp(exp(h²/(8E²)-a)-K)<=V+1. No simplicity premise. /tmp/wp06-c8-{build,final,axioms,lint}.log alltargetaudits0 standardonly; lintthen5unrelated. Narrow failedcard docs/drafts/pipeline/5-failed/weil-work-06-cheap-strong-transfer.md retains full positive survivor. Refutes only UNIFORM cheap strong-L2 transfer covering all spectral shifts, not C7/finite forms or particular M-dependent Bernoulli witnesses. Spectral Plancherel bridge paper-only.

## Earlier core / distinctions
WeilWorkDeficitCoefficient capstone: eventually abs(lam n-Lambda n)/(4pi sqrt n)<=D(T)/T+eps. Exact shared critical submeasure, sharp mass identity, Poisson leakage/zero Fourier transport, deficitSquareCount/T->0. This is LOWER D bound, never an upper producer.
WeilWorkDeficitRestrictedXiDensity: complex Xi-weighted density of bounded-interval physical exponentials, qualitative; no quantitative coefficient rate.
WeilWorkDeficitRepairCost: actual atomCost<=C(n+1)sqrt n, four audited theorems.
WeilWorkDeficitRadicalBudget:9 audited theorems, short real shifts[-log2,0], cost=(sum abscoeff)^2, full actual weight, term/tail exp(-rM) for0<r<pi; ENTIRE weighted l1 truncation convergence, uniform majorants. No cancellation construction.
Restricted no-go C0 separate translates and C1g geometric grid outer-covariance law fully closed; survivor exact last sampled indexR+D/nonzero edge product and later vanishing formalized. Card ../5-failed/weil-work-06-restricted-radical-cancellation.md. Neither retires full coherent route.

## Live conjectures / exact next target
General C: positive near-radical families retaining spectral lower mass off actual Xi zeros, full actual weighted repair budget->0, zeta energy->0. Nullrepair then critical support/lamLambda receiver. Full assembly not Lean.
C7: some fixed aperture a>0, UNBOUNDED horizons M, real Phi-translate families shifts[-a,0], retain Phi, cancel b(n) n2..M, coefficient-square cost<=C exp(theta M), theta<2pi exp(-a). Paper implication toC complete; constructionOPEN.
C9: everyfixeda>0,epsilon>0 actual finite quadratic dual target-relative negative witness of variation<=1 and size C^-1 exp(-epsilon M) timesbaseline pairing; competing critical exponential witness obstruction. BothOPEN.
C10: existsc>0 and unboundedM>=2, finite REAL derivative packets orders<=M retainingPhi, total raw correlations b(n)=0 n2..M and sum_(n>M)(Lambda(n)+atomCost(n))abs b(n)<=exp(-cM). Uniform order bound now paid by C10u, but positive cone and affordable cancelling coefficients OPEN.
NEW C11 qualitative restricted cone: define REAL A(n,k)=integral Re(Phi^(k)(u))*Re(Phi^(k)(u-log n))du. For EVERY M>=2 conjecture nonnegative d0..dM, d0=1, sum_k dk A(n,k)=0 n2..M. Family sqrt(dk)Phi^(k), no cross terms. This is NOT diagonal translate C0. Competing finite dual: someM and alpha2..alphaM with sum alpha_n A(n,0)>0 and all sums for1<=k<=M nonnegative. Finding actual family/actual separating functional is OPEN CORE; generic separation is not new knowledge.
NEW C11q quantitative competitor: exists fixed0<theta<pi and UNBOUNDED horizonsM withC11 coefficients and sum_k dk*19^(2k)*((k+2)!)²<=exp(theta M). Actual singleton squared budgets sum exactly to this. C10u r=pi,N=M-1 gives tail<=Bpi exp(-pi(M+1)+theta M), hence C10 eventually foranyc<pi-theta. No unknown inverse constants. C11forallM andC11q unboundedM have different quantifiers: failure at oneM does not refuteC11q; cost condition can fail evenifC11true. Neither retires coherentC10/C7/C9. No newLeanpremise. Verdict SURVIVES PRELIMINARY ATTACK, no noveltycertificate.
Next attack ACTUAL matrix at coupled k~n, not fixed-k asymptotics/dimensioncount. Near-radical dimension and cuspdegree motivate scale but do not prove matrixsigns/positive minors. Do not assume TP/Chebyshev system.
Older C5p polynomialcost/C6diagnosticsOPEN; C4b quartic lowercostA>=cM4/(logM)^34 paper-only stripBlaschke bridge, notLean, no route retired. C2f fixedfinite positive feasibility paper via density+separation, no cost. Anchored Bernoulli spectral-shift cancellation paper cost2^(M-1), shiftsO(M/logM), baseline-relativedualnegative1/(2^(M-1)-1); fails to preserveXi factor.

## New working representation lead (NOT AUDITED; no new Lean draft)
Theta-pair substitution v=2u-y+log(n/m), t=ell exp y, suggests exact
 kappa(y)=exp(y/2) sum_(ell>=1)d(ell)[(16pi^4 t^4+36pi²t²)K0(2pi t)-48pi³t³K1(2pi t)],
where Knu(x)=1/2 integral_R exp(-x coshv)cosh(nu v)dv.
Derived by Phi evenness and P0(X)P0(Z), XZ=(nm exp y)², X+Z=2nm exp y coshv. Need audit normalization, absolute Fubini/regrouping, all-order differentiation BEFORE use. Could expose actual C11 coupled matrix via divisor-Bessel series. This is likely classical Xi²/Koshliakov ancestry, not a novelty claim. First inspect existing MaassZetaSquaredConverse (symbol overview read, relevant bodies NOT yet), EisensteinCuspTailImaginaryOrderBound. Do not create another routine formal bridge before checking exact relevance toC11sign/cost.

## Searches / fresh evidence this turn
All commands terminal, candidates/source_arguments/ingredients inspected. No search absence certificate.
/tmp/wp06-c10-actual-cone.json: deep300s,partialfalse,68547indexed,refreshincomplete.
/tmp/wp06-c10-factorial-frontier.json: deep300s,partialfalse,errorsempty,68550indexed,43compiledsnapshots,mostcompilerpending/stale.
/tmp/wp06-c10-uniform-exact.json: partialtrue Qdrantsemanticbudgettimeout, availablehitsinspected.
/tmp/wp06-c11-positive-collocation.json: partialfalse,errorsempty,68556indexed,43compiledsnapshots,backgroundrefreshincomplete.
/tmp/wp06-c11-bessel-frontier.json: partialtrue localdecompositiondeadline,68565indexed,43compiledsnapshots,backgroundrefreshincomplete. Returned relevant MaassZetaSquaredConverse.divisorCount, zetaSqCompleted, coeff_eq_divisorCount_of_functional_equation (HAS functional-equation/growth premises; notproducer), divisorBesselMajorant_le, imaginaryorderBesselbound and oldtailtheorem. Available20+20 inspected.
Exactrg: fixed-order derivative envelopes foundin WeilWorkExposingRayDifferentialParity/Width. Their ownheaders explicitlyexcludeuniformorderbounds. Cusp recurrence/degree/complete summability/derivativeparity reused. RiemannKernelSpectralLocalization localized_deviation_nonneg explicitly assumes bounded normDeficit and summability; readbody467–506. WeilFullConeRiemannKernelRigidity eq_vonMangoldt_of_weilPositiveFull_of_ge assumes lam>=Lambda, notproducer.

External primary audit opened:
- Paris https://arxiv.org/abs/1606.03576 (Toucharduniformasymptotic abstract; no numericillustrationimported).
- Jalowy/Kabluchko/Marynych https://link.springer.com/article/10.1007/s00365-026-09775-2 (11Sep2026), Touchard4.2 anddifferentialoperators5.2–5.3: zero-distributionlimits, notC11signs.
- Groechenig https://link.springer.com/article/10.1007/s44146-026-00264-3 (17Aug2026), sections1–3: collocationinverse results requireTPandwitness; noTPestablishedhere. Do not import sweeping formulations without auditing.
- NIST DLMF https://dlmf.nist.gov/1.9 classicalanalyticancestry.
- Berndt/Dixit/Gupta/Zaharescu survey https://adixit.people.iitgn.ac.in/wp/wp-content/uploads/2023/03/askey_special.pdf (openedintro,21pages2265lines; Koshliakovsectionstilltoread).
- https://arxiv.org/abs/1505.01552 (openedabstract), KoshliakovXiidentities parentlead.
- MDPI2026Koshlyakov https://www.mdpi.com/2227-7390/14/15/2715 failedfetch; nopropositionused.
BroadsearchRHproofclaims notused. Corpus/candidate mathematical statements always need exact source and Lean validation.

## Persistence / next turn
Owned working log docs/drafts/pipeline/1-in-progress/weil-work-06-deficit.md; result docs/reports/weil-work/results/06-deficit/{RESULT.md,PROOF.md,EVIDENCE.md,lean-audit.log}. Main goal remains ACTIVE/UNSOLVED. Previous turn classification PROGRESS in formal analytic coverage, not newscientificknowledge. Next init read hgtl7, relevant memories/frontier/target; verify completed source/emptyfinal/axioms then attackC11q actualpositiveconstruction or exactdualobstruction. Keep broader C7/C9/C10 and full actual deficit goal. No active owned processes or unfinished source.