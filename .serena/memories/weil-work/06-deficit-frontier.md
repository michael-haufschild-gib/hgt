# WP06 spectral deficit frontier — 2026-10-07

Goal ACTIVE, UNSOLVED. User requires hgtl7 every turn, corpus-first conjecture/attack/paper-proof/Lean loop until exact target:
∀ η>0, ∃ᶠ T→∞, deficitCount hW T/T ≤ η.
D includes every actual XiZeroCopy: off-line costs 1, critical costs max(1−μ{γ}/multiplicity,0). No producer existence or RH proved.

## Current substantive result: Candidate A COMPLETE
WeilWorkDeficitCoefficient.eventually_sub_vonMangoldt_div_sqrt_le_deficit:
for arbitrary hW:WeilPositiveFull lam, n≥2, ε>0,
eventually |lam n−Λ n|/(4π√n) ≤ D(T)/T+ε.
Improves old 4πn scale, no assumed upper deficit premise. Also:
- Re actual character gap G_(log n)(T)/T→(Λn−lam n)/(2π√n).
- Sharp canonical minus actual-zero mass (M(T)−N(T))/T→0.
Quantitative corpus advance; external scientific novelty NOT established.
This remains a lower deficit estimate, NOT the missing upper-deficit producer.

## Original capstone corpus: 13 modules,57 public theorems (later additions below)
All namespace RHTower.WeilSpectral; files formal/GaloisForLFunctions/RHTower/WeilWorkDeficit*.lean.
Recovery(8): bounded-window regularized atom/deficit recovery uniform over every prefix, no growing-height rate.
SharedMass(12): actual χ≤μ,ν, χ((0,T])=N−D; norm character gap≤M−N+2D.
MassBounds(5): logarithmic interval mass and finite Icc for canonical μ and actual ordinate ν=Σdirac γ; Cauchy-weight integrability.
PoissonLeakage(5): scalar L(T,r)=|countKernel T r−π1_(0,T]|; ≤π, ≤3/H away endpoints, ≤12T/(1+r²) far.
LeakageIntegral(6): integrability and ∫L/T→0 for BOTH actual measures; one private measure-general proof, canonical public APIs preserved.
FourierTransport(4): canonical σ=2 complex Fourier transport, norm error≤∫L dμ; normalized error→0 even arbitrary k(T). Inverting exponential multiplier is NOT uniform.
ArithmeticMean(2): exact cosine mean of Re(Φλ−ξ′/ξ) at σ>1 equals (Λn−λn)n^(−σ)/2, zero-frequency mean0.
SquareWindow(1): actual-copy admissible-window square-displacement bound from smaller uniform first weighted tail. Every finite F, no assumed symmetry; both sides/multiplicities paid.
SquareMoment(1): Q(T)=Σ_(0<γ≤T)(β−.5)^2, Q(T)/T→0 unconditional.
Projection(3): exact line-conjugate multiplier correction norm≤e^(−1.5|k|)*(k²/2 cosh(|k|/2))*Q(T); fixed-k normalized limit0.
ZeroKernel(2): per-copy Fourier integral error≤1.5L; complex dominated integration of actual Poisson copy series.
ZeroTransport(5): raw sum error≤1.5∫L dν, uniform k(T) normalized0; finite character sum equals sharp ν integral; projected ξ'/ξ Fourier error/T→0 fixed k.
Coefficient(3): exact real logn gap limit, M−N=oT, eventual √n bound.

## Current validation checkpoint
No ACTIVE OWNED PROCESS. No unfinished owned Lean source.
All13 imports wired in RHTower.lean. 57 public axiom audits standard-only [propext,Classical.choice,Quot.sound].
Newest:
- ZeroKernel final direct /tmp/wp06-zero-kernel-second.log exit0 empty; target build0(225s).
- ZeroTransport final direct /tmp/wp06-zero-transport-third.log exit0 empty; target build0(115s).
- Coefficient final direct /tmp/wp06-coefficient-third.log exit0 empty; target build0(151s).
- Combined /tmp/wp06-coefficient-axioms.log exit0, ten public theorems standard-only.
- Final lint /tmp/wp06-coefficient-final-lint.log exit1 ONLY6 unrelated reachability errors:
  RHTower.WeilWorkSettledPhaseCanonicalDisorder;
  HTGeometry.ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra.
- Scoped whitespace check0. No numerical experiments, full/umbrella builds, raised heartbeats, new mathematical axioms, commits/push.
- Obsolete /tmp/wp06-coefficient-draft.lean removed. Audit scratches/logs retained.

## Next research cycle
Candidate A is FINISHED. Do not keep rebuilding it or adding routine coefficient receivers.
Main upper estimate for growing-height ACTUAL atom overlap is open; off-line copies cost1 regardless of Q=oT.
Fixed-frequency bridge has its complete application; next conjecture must use exact Weil datum/source arithmetic to control overlap.
Known prior limits:
- WeilPaperDeficitInverseEnergy:4I≤D,D²≤16NI,off-linecount≤4I. InverseRecovery recovers I only at fixed bounded height. No I decay producer.
- WeilWorkQuantizationFiniteRemainderRigidity: GLOBAL finite residual measure forces rigidity. Does not imply residual finite from a linear-scale bound.
- WeilConeWindowRigidity relative Wiener theorem assumes vonMangoldt producer (RH); cannot use unconditionally.
- Paper krein-producer-loops L111–L112 already explains low-frequency blindness; smoothing zeros loses atoms while altering exact archimedean datum. Do not rediscover as new no-go.
- WeilFibreBochnerLaw excludes both signs of nonzero Cramér-restored profile, despite rough-sign-only failure.
External: Ford–Zaharescu math/0405459v2, descendant0805.2745v3, simultaneous1511.06814v2 give classical fixed-character normalization. Booker1308.3067v2 Theorem1.6 uses sublinear total spectral variation with discrete almost-integral L-data assumptions, not general canonical measures. No external novelty certificate.

## Latest searches
All candidate/source statements inspected:
- /tmp/wp06-zero-transport-frontier.json: actual copy Fourier transport; partialfalse/errors[].
- /tmp/wp06-sharp-frontier.json: sharper coefficient query; no old exact capstone located.
- /tmp/wp06-next-overlap-frontier.json: inverse energy etc; partialfalse/errors[],68402files,43compiled snapshots,51936pending,2660stale. Includes own then-unchecked source; never count that as independent proof.
- /tmp/wp06-atom-rigidity-frontier.json and /tmp/wp06-linear-residual-frontier.json: partialfalse/errors[], finite residual/conditional relative Wiener receivers, no upper-deficit producer.
Run documented research command directly, do not inspect help/source first. Search coverage remains predominantly source-only.

## Source/log locations
docs/drafts/pipeline/1-in-progress/weil-work-06-deficit.md
docs/reports/weil-work/results/06-deficit/{RESULT.md,PROOF.md,EVIDENCE.md,lean-audit.log}
Updated to13modules57theorems and main OPEN. Main card gates remain open.
Owned code WeilWorkDeficit*.lean plus their umbrella imports. Existing modules read-only, preserve unrelated concurrent edits.

## Tool/Lean gotchas
One foreground Lean/build process at time; poll terminal owned handle before starting next. Targeted lake --old build +Module; final lake --old env lean path. Never full/umbrella build.
Serena rejects Lean symbol operations as ignored; read-source/ordinary file fallback documented. update_plan,multi_tool_use.parallel unavailable; card plan and Promise.allSettled independent reads.
Do NOT coimport WeilFullConePoissonCountingIdentity with WeilConeSpectralCounting: duplicate fully qualified integral_poissonKernel_eq with incompatible signatures. Reused complex dominated-sum proof directly.
RCLike.re vs Complex.re: explicitly change integral_re or continuous_re composition type before rw/simp.
lt_mem_nhds gives eventual lower bound; gt_mem_nhds is upper.
Use explicit denominator positivity when rewriting abs_div; generic abs_of_pos may target numerator.
Explicitly unfold private wrappers and deficitOrdinateMeasure before rewrites.
tsum subtraction body needs parentheses.
HasSum.congr and root tsum_le_tsum absent; use finite support and Summable.tsum_le_tsum.
Audit recalled mathlib names in /tmp specialized have:=@Name; polymorphic APIs may need explicit types.


2026-10-07 radical-repair cycle: main goal remains ACTIVE/UNSOLVED. Fourteen finished owned modules, 58 public theorems. New WeilWorkDeficitRadicalTranslateObstruction proves ∃δ>0 uniformly over every finite positive mixture of separately translated truncated Riemann kernels (each L≥log2+1): δ Σw|FT f(r)|²≤Σw logValue f 2. First direct lake --old env lean audit passed empty; targeted build passed (205s); public axiom/API audit passed standard-only; umbrella wired. Final lint has 15 unrelated reachability errors (exact list in owned EVIDENCE), no WP06 issue. No active owned build or unfinished Lean source.
Important frontier correction: fresh @-type audit of eq_vonMangoldt_of_boundaryMeasure_criticalZeros confirms carrier support alone suffices, without atom bound or RH. Old paper's arbitrary/unbounded mass uniqueness case is already settled. WeilConditional.Decomposition.riemannHypothesis requires mandatory D section argument; not unconditional hW-only. Reciprocal H² means do not give exceptional-height or forward-energy estimates. Existing RiemannKernelModulatedWindowTests already handles universal logarithmic deviation bound; existing positive-definite deviation potential/translation bound must not be rediscovered.
Current exact Conjecture C (PROOF): finite positive test mixture S≥1 on compact K outside actual critical zeros, actual zeta energy R→0 and full weighted arithmetic repair B→0. Existing nullRepair then gives zero-defect small-energy majorants and critical carrier support. Construction OPEN. C0 translated-only family FALSE; exact positive survivor above formalized. Elementary corpus consequence, no significant scientific novelty this cycle.
Next conjecture C1: for each compact K outside critical zeros, ∃A≥0,C>A+3 such that all large N admit coefficients a_ij (i,j≤N), sum|a|²≤N^A, tests f_i=Σ_j a_ij Φ_(L_N)(u−log j), L_N=1+.5 log(C logN), with sum_i logValue f_i n=0 for EVERY n≥2 and sum_i|FT f_i(r)|²≥1 onK. Only n≤e² C NlogN can contribute. Existing actual-copy tail bound would give total zeta energy ≤M N^(A+2−C)→0. OPEN CORE: positive covariance feasibility plus quantitative normalization, not a dimension count. First complete paper attack: extreme ratio support isolation forces Re Q_N1=0 for N≥2,L≥1; for symmetricK can average Q andconjQ and take realQ. This does not killC1. Next investigate support peeling through rational ratios or construct bounded-cost covariance; do not formalize C1 without proof. Exact statements, paper implication and attack in owned PROOF; newest searches in EVIDENCE. No numerical experiments or new premises.


## Latest authoritative checkpoint — 2026-10-07, C1g and C2
Goal ACTIVE / UNSOLVED. Current completed total supersedes older counts: 15 owned modules, 60 public theorem axiom audits.

New module `WeilWorkDeficitGeometricRadicalObstruction.lean` (umbrella-wired) has two public theorems: `RHTower.WeilSpectral.geometric_radical_outer_autocorrelation` (line 159), exact outer-support law for actual coherent truncated-kernel autocorrelations on any real spacing c>0, L>=c+1; and `logValue_geometric_radical_eq_zero_iff` (line 194), cancellation at all positive powers of integer b>=2 iff every coefficient vanishes. Positive invariant: kernel last index R>=1 and covariance last index D>=0 give last correlation index R+D, exact coefficient C(D)κ(R), all larger samples zero. Nonzero covariance trace prevents triviality. REDISCOVERED Laurent-polynomial parent algebra / corpus specialization; no scientific novelty claim, no degree-uniform lower cost, no upper deficit bound. No-go audit explicitly strengthened the public result beyond a restated impossibility. Closed card `docs/drafts/pipeline/5-failed/weil-work-06-restricted-radical-cancellation.md` covers both C0's uniform coercivity and C1g's positive invariant.

Final direct source audit `/tmp/wp06-geometric-strong-first.log` exits 0, empty diagnostics; targeted build `/tmp/wp06-geometric-strong-build.log` exits 0 (82s); both axiom/API audits `/tmp/wp06-geometric-strong-axioms.log` exit 0, only propext/Classical.choice/Quot.sound. No full build/heartbeat increase/added scientific premise/commit. Final lint `/tmp/wp06-geometric-final-lint.log` exits 1 on 17 unrelated reachability errors, none WP06. Scoped diff check exits 0. No owned active process or unfinished Lean source remains; temporary strengthened-source duplicate removed.

Current next conjecture C2 (OPEN, exact statement and full support/energy reduction in PROOF): for compact K disjoint actual critical zeros, seek A>=0,C>A+1 and for all large N real coefficient rows a_ij, i<=N,j in [ceil(N/2),N], total squared coefficients <=N^A. Let L_N=1+.5 log(C log N), x_j=log(j/N), f_i=Σ_j a_ij Φ_LN(u-x_j). Require total logValue zero for integers 2<=n<2 exp(2) C log N and Σ_i|FTf_i|²>=1 on K. Support then cancels all larger integers automatically (shift diameter <=log2). Existing `WeilExcess.norm_W_shiftComb_le` bounds total remainder <=2 M N^(A+1-C)->0; common translation preserves autocorrelation and W. This gives C with B=0 IF constructed. Missing core: positive covariance feasibility plus polynomial normalization, not dimension count. Geometric-grid outer peeling does not cover dense rational ratios. C1 remains OPEN as well; C2 is a sharper candidate, not its disproof.

Fresh covariance, inverse-approximation, short-block and centered-energy searches all partial=false/errors=[]; all candidate/source statements inspected. Latest coverage 68,448 files, 43 compiler snapshots, 51,974 pending, 2,660 stale. General real shift-combination source read and confirmed. LebesgueAtomWeilPositivity source checked: uses noninteger measure weights, not a counterexample in the assigned integer-weight domain. External parent audit: Plonka's autocorrelation-symbol paper and mathlib Laurent-polynomial docs; global Dirichlet Lq bounds and Bessel-series abstracts did not supply the missing producer. Do not restart a broad route survey. Continue hgtl7 every goal turn with C2, keeping main actual-copy deficit target and no-go closure rules intact.


LATEST AUTHORITATIVE WP06 CHECKPOINT, 2026-10-07 after restricted-density/C3 cycle: Goal ACTIVE, UNSOLVED. Sixteen finished modules / 62 public theorem axiom audits. New `formal/GaloisForLFunctions/RHTower/WeilWorkDeficitRestrictedXiDensity.lean` proves `WeilSpectral.xi_interval_integrals_eq_zero_iff` (line 78) and `dense_span_deficitXiShiftLp` (line 114): actual XiC(r) exp(-itr) profiles for t in any nonempty real interval have dense complex span in L². Reuses `XiPolynomialDensity`, `ExpDecayFourierAnalytic`, actual xi nonvanishing ae, and Riesz duality. Classical BRIDGE, not scientific novelty or coefficient bound. Final unchanged direct source `/tmp/wp06-restricted-density-second.log` exit0 empty; target --old build `/tmp/wp06-restricted-density-build.log` exit0 96s; axioms `/tmp/wp06-restricted-density-axioms.log` both standard propext/Classical.choice/Quot.sound; specialized API `/tmp/wp06-c2f-api-specialized.log` exit0. Umbrella wired. Latest lint `/tmp/wp06-restricted-density-lint.log` exit1 seven unrelated unreachable modules: RHTower.WeilWorkSingularArithmeticCauchyReflection, WeilWorkSingularArithmeticHerglotzPairing; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. Scoped diffcheck0. No owned active process or unfinished Lean source remains.
C2f complete PAPER proof near top of owned PROOF: every FIXED integer horizon M and compact K excluding actual critical zeros admits positive REAL coherent Phi_L mixtures on centered grids log(j/N), j in [ceil(N/2),N], for all sufficiently large L,N, cost bounded by a finite B(M,K). Real restricted-translate L² density; nonzero finite cosine dual q has zero mean but positive mean square, hence changes sign; finite sphere cover gives positive defect-cone interior; add Phi baseline to preserve spectrum; round shifts and truncate, preserve interior and uniformly bounded weights. Only complex-density component formalized, NOT full real/cone/grid claim. This gives no joint growth bounds on B,L0,N0 and does NOT prove C2.
New selected C3 OPEN: untruncated actual real Phi; for every sufficiently large M require finite positive coherent family f0=Phi, fi=sum_j aij Phi(u-xij) with real aij, shifts in [-log2,0], all moments b(n)=sum_i 2/sqrt(n) autocorr(fi)(log n)=0 for 2<=n<=M. Require A_M=1+sum_i>=1 (sum_j |aij|)^2 <= C exp(theta M), constants C>0 and 0<=theta<pi/2. C2f gives finite feasibility but NO rate. Fixed baseline covers any off-zero compact after constant scaling; no separate spectral interpolation. This decouples physical truncation L from arithmetic horizon M and is less restrictive than C2.
Complete PAPER reduction C3r and C3t in owned PROOF, NOT Lean-audited yet: actual `atomCost(n)<=C(n+1)sqrt(n)`. Source `narrowBump` equals fixed smooth eta(u/delta), delta=1/(8(n+1)), by Mathlib ContDiffBump.toFun with radius ratio2; eta=1 on[-1,1], support[-2,2]. FT scale delta H(delta r). Pair factor |1±exp(ir logn)|<=2. Corpus `WeilFullConeBochnerMeasure.abs_gammaBracket_le` gives |gammaBracket r|<=G+|r|, so gamma numerator <=const*(G delta int|H|²+int|r||H|²), uniformly bounded; pole terms bounded by const delta²(1+sqrt(n))². Divide by atomWeight=2delta int eta²/sqrt(n). Smooth compact eta pays both Fourier moments by two integrations by parts.
C3 tail uses VERIFIED source `riemannAutocorr_two_mul_le` and explicit `riemannShiftRatio(x)=exp(-pi(x-1))*((4pi²x-6pi)/(4pi²-6pi))²`. For shift differences in[-log2,log2] and n>=4, shifted autocorr <=const n² exp(-pi n/2). Thus |b_M(n)|<=const A_M n^(3/2) exp(-pi n/2). Weighted (Lambda+atomCost) tail <=const A_M sum_n>M n³ exp(-pi n/2) ->0 if theta<pi/2. For each fixed family smooth truncation preserves pointwise domination 0<=Phi_L<=Phi; same summable majorant pays ENTIRE weighted budget convergence, including new active integers. Fixed-family actual zeta energy tends0 by existing norm_W_shiftComb_le. Choose L(M) separately to make energy and budget errors <=1/M and baseline spectrum >=1 on K after fixed normalization; actual PBAP nullRepair adds positive spectra and exact integer cancellation with energy <=R+B. Hence C3=>C is now dependency-closed on PAPER, unformalized. C3 rate itself is the main hard conjecture; no target solution claim.
Current cycle searches in /tmp/wp06-c2-*.json, c3-analytic-density, c4-christoffel, c5-autocorr-halfplane completed partialfalse; formal-density deep query partialtrue semantic/reranking deadlines, available hits inspected; targeted rg found stronger XiPolynomialDensity machinery. Latest c3-repair-cost query partialfalse/errors[] all candidate/source statements inspected, coverage compiler mostly pending/stale. Found separate ExposingRayFiniteRealization repair (requires IsPolarTest), not substituted for actual PBAP cost. External density ancestry Bruna-Olevskii-Ulanovskii arxiv math/0307323v1 and Olevskii-Ulanovskii1612.00811v2; L² versus L¹ distinction essential. Recent Zhu2608.24827, Groskin2607.02828, Desogus2609.20367 claims inspected but no closing theorem adopted. No computations. hgtl7 anti-theatre/anti-laziness reviews posted. Next turn: apply skill again; continue actual target-specific exponential coefficient cost and formalize exact C3r/C3t or remaining C2f obligations, do not resurvey or call bridges a solution. Owned PROOF/RESULT/EVIDENCE/card/audit log updated, global frontier and STATUS untouched.


## Authoritative latest checkpoint: C3r COMPLETE, 17 modules / 66 public audits
2026-10-07. Main goal ACTIVE/UNSOLVED. Latest turn PROGRESS/BRIDGE; anti-theatre and anti-laziness answers posted in chat. No significant external scientific novelty claimed.
New module formal/GaloisForLFunctions/RHTower/WeilWorkDeficitRepairCost.lean (namespace RHTower.WeilWorkPBAP):
- narrowBump_eq_scaled_zero line23: h_n(u)=h_0((n+1)u).
- paperFT_narrowBump_scale line35: exact complex-frequency scaling.
- integral_narrowBump_sq_scale line58.
- atomCost_le_polynomial line255: ∃C>0,∀j:LogIndex, atomCost j≤C(j+1)√j.
All exact actual PBAP definitions; no new scientific premise. Uniform gamma numerator from g(r)=|FT h0(r)|²(G+|r|), majorant (4/(n+1))g(r/(n+1)); strip bound |FT pair(z)|≤e∫h0 for |Imz|≤1 pays BOTH poles.
Final direct lake --old env lean source /tmp/wp06-cost-final.log exit0/empty; target build /tmp/wp06-cost-build.log exit0/103s; /tmp/wp06-cost-axioms.lean/log exit0, four public declarations only propext/Classical.choice/Quot.sound. Specialized APIs verified in same scratch. Initial integrable_zero scratch call needed explicit ℝ ℝ volume. Umbrella import wired. No source change after successful direct audit.
Global lint /tmp/wp06-cost-lint.log exit1: 9 unrelated reachability errors: RHTower WeilWorkSettledPhaseForwardRegularPart, WeilWorkSettledPhaseForwardSummatory, WeilWorkSingularArithmeticCanonicalGaussian, WeilWorkSingularArithmeticPoleCancellation; HTGeometry ApertureConeCalculus,ConeWinding,LogTranslation,OpenHistoryIdeal,BoundaryCoronaCStarAlgebra. No WP06 or forbidden issue. Own diff-check0. All owned processes terminal; no unfinished owned Lean module.
PROOF/RESULT/EVIDENCE/audit.log/card updated. C3r is formally complete; C3t weighted-tail/full-budget truncation reduction still PAPER ONLY.

New cost attack C4b (complete PAPER proof, NOT Lean-audited): any finite REAL translated-Phi family retaining separate Phi baseline, cancelling all total logValue n=2..M, has coefficient cost A_M≥c M^4/(log M)^34 for all largeM. Shifts arbitrary, no restriction needed. Cannot retire bounded-cost route until positive boundary formally audited. Does NOT kill C3 subcritical exponential rate.
Proof: H=FTPhi=XiC. G(r)=|H(r)|²(1+Σ|P_i(r)|²)≤A_M|H|², even nonnegative. F(z)=(1/(2π))∫G(r)e^{-irz}; F0≥κ0>0, F(±logn)=0. Source ThetaCuspChargeXiStripBound gives xiStripConst(π/4−ε)≤Cε^-8: formula γ^-3*(S4γ+S2γ), Gaussian sums ≤Cγ^-5,γ^-3 and γ≥2ε. Thus |H(r)|≤Cε^-8 exp(-(π/4−ε)|r|). F bounded by CA_M ε^-17 on strip b=π/2−4ε. Finite disk Blaschke division under w=tanh(πz/(4b)) bounds F0 by CA_M ε^-17 ∏_{n=2}^M ((n^p−1)/(n^p+1))², p=π/(2b). Choose ε=(logM)^-2. p−1≤16ε/π, Σn^-p≥logM−O(1), product≤CM^-4. Lower bound follows. Generic analytic parent is classical; verdict BRIDGE, not scientific novelty.
Directly read: ThetaCuspChargeXiStripBound.lean lines1–21,160–244; norm_XiC_ofReal_le_strip line192, thetaGaussianPowerSum_le223. ThetaCuspComplexStrip explicit source proof458–548 and xi decay856. ThetaCuspChargeDominance.xiStripConst_chBeta_le line13 also gives bound3000000/t^16, but C4 proof uses θ direct. RiemannAutocorrFourier.riemannXi_eq_XiC around74 fixes normalization.
External primary: Platonov Spectral synthesis..., author upload https://www.researchgate.net/publication/267177344_Spectral_synthesis_in_some_topological_vector_spaces_of_functions §3 explicit strip Blaschke. Calder–Kempf quant-ph/0405065; Kempf–Ferreira quant-ph/0305148; diDio–Schmüdgen1809.00584; Karvonen–Suzuki2209.12473. These do not give exact C3 rate. Ferreira authorPDF403; arXiv available.
Fresh searches /tmp/wp06-c3-turn-frontier.json partialfalse,68,482indexed, refreshincomplete/backgroundindexer, compiler mostlypendingstale; /tmp/wp06-c3-cost-boundary.json partialtrue. Candidate and source statements inspected, direct sources used. No absence/novelty certificate.

Next hard conjecture C5p OPEN: ∃C,K>0,M0,∀M≥M0 finite real translatedPhi family with shifts[-log2,0], separate baselinePhi, cancellation n2..M, A_M≤CM^K. C4b forces K≥4. StrongerthanC3 and would implyitsrate, but [OPEN CORE] target-specific positive covariance construction. Do not price arbitrary unit defect cone instead of particular −b(Phi). Generic Blaschke zero-enforcement of autocorrelation does NOT establish Fourier factor |XiC|² times positive restricted exponential square sum: preserve this constraint. No upper construction or bounded inverse proved.
Continue corpus-first hgtl7: attack C5p; formalize exact paper C4b positive boundary and C3t dependencies as needed. Main target not solved; never mark complete.
