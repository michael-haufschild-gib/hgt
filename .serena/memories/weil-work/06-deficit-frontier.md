# WP06 spectral-deficit frontier — 2026-10-08

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