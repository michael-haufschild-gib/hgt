# Boundary moment repair: current source attack

[R] remains OPEN, RH NOT proved. Goal ACTIVE (automatic continuation), no budget. Do not mark complete or blocked because math is hard. No subagents authorized/spawned. Preserve concurrent external edits/commits; we did not commit/push. Latest turn made progress: two dependency-closed paper proofs and completed numerical source experiment. No new Lean code/build this turn. Existing chronological formal total remains12 leaves/154 public, standard axioms only; latest completed formal module is HarmonicCharge. Read prior memory `mem:research/chronological-escaping-averages-charge-2026-09-06`.

Current compact card:
docs/drafts/pipeline/1-in-progress/chronological-boundary-moment-repair.md.
Main chronological-bounded-repair-attack.md updated with new paper statuses.

## New paper theorem [K-finite], not yet Lean
docs/drafts/pipeline/2-fully-proven/chronological-finite-tail-obstruction.md
For fixed0<theta<1 and any fixed finite-dimensional real V subset C1([theta,1]), freeze a_k=mu(k) for k<=theta N; tail a_k=f_N(k/N), f_N in V. Then E_N=inf_f ||actual residual||2 has a positive cofinal floor. NO coefficient bound needed. Stronger than original bounded fixed-family hunch, independently frozen before finishing proof. Growing-dimensional repairs remain OPEN. No route retired until exact theorem and positive survivor are Lean-audited.

Paper proof:
H=L2([1,2],complex), inner=<v,w>=integral conj(v)*w.
F_f(u)=integral_theta^1 f(x)h(xu)dx; W=complex span of these.
K_rho(u)=integral_0^theta x^(rho-1)h(xu)dx, one unconditional Hardy critical zero rho.
K_rho not in W: analyticity in u extends local equality to all positive u. Mellin in real0<s<.5 yields theta^(rho-s)/(rho-s)=integral_theta^1 f(x)x^-s dx after cancellation of strictly positive Mellin h. RHS entire; analytic continuation to Re s<.5 and s=rho-delta contradicts pole. Same argument+polynomial density proves f->F_f injective.
Q=orthogonal complement projection, d=||QK_rho||>0, psi=QK/d.
DISCRETE F_jN=N^-1 sum_(thetaN<k<=N) f_j(k/N)h(ku/N). C1 Riemann error O(1/N), limiting Gram positive definite, projection Q_N converges operator norm O(1/N). psi_N=Q_NK/||Q_NK|| is unit, differs psi byO1/N, and annihilates ALL actual discrete tail coefficients EXACTLY. This avoids needing any bound on f_N.
H0(x)=integral_1^2 conj(psi(u))h(xu)du is C1 at0 using analytic extension h(0)=1/2.
T(X)=sum_(k<=theta X)mu(k)H0(k/X).
Cauchy–Schwarz after u=Nt gives uniform observation:
|T(N)|/sqrtN <= ||r_(N,f)||2 + O(N^-1/2), all f, with constant independent f.
Only bounded Möbius head pays projection error. T(X)-T(floorX)=O1 using bounded H0,H0'.
If E_N->0, T(X)=o(sqrtX).
B(s)=integral_0^theta H0(x)x^(s-1)dx analytic Re>0.
A(s)=integral_1^infty T(X)X^(-s-1)dX analytic Re>.5.
Absolute Dirichlet identity A*zeta=B for Re>1, then identity theorem via(s-1) extends Re>.5.
Direct Abel split delta*A(rho+delta)->0; zeta(rho+delta)=O(delta); B(rho)=0 contradicts B(rho)=<psi,K>=d>0.
Positive survivor: d=distance(K,W), exact uniform observation, cofinal error floor all coefficient choices. If L=limsup E finite and zeta'(rho)!=0 then L>=d/|zeta'|; if derivative0 then L=infinity. Not a liminf/eventual floor.
Successful fixed-proportional-prefix tails must leave every fixed V cofinally. Bounded-degree eventual membership impossible; do NOT claim degree tends to infinity on every subsequence.

Lean obligations (NONE implemented yet): actual compact-weight Mobius Mellin identity/critical-zero obstruction; heat-transform separation; C1 Riemann Gram projection estimate; actual norm observation. Existing raw Laplace obstruction does not replace weighted lemma.

## New positive source [BRIDGE K-growing-jet], paper proved, Lean pending
docs/drafts/pipeline/2-fully-proven/chronological-growing-moment-source.md.
For fixed m, v(x)=(x^-1,1,x,x^3,...,x^(2m-1)) on[.5,1].
G_N=sum_tail v(k/N)v(k/N)^T,
b_N=tau-sum_head mu(k)v(k/N).
tau_-1=0,tau0=-2,tau_(2j-1)=(-2j/B2j)*N^(-(2j-1)).
c_N=G_N^-1 b_N, tail a_k=c_N^T v(k/N).
Exact charge0,sum a=-2, first m odd cancellation moments; unique least squared-coefficient tail by Pythagoras.
For each fixed m, G_N/N->positive integral Gram; N*G_N^-1 bounded.
PNT Mertens=oX and harmonic sum mu/k->0 give b_N/N->0, hence c_N->0 and tail max->0.
Select largest admissible m<=N with invertible Gram and tail max<=1; if none, entire row0. Every fixed m eventually admissible, hence m_N->infty, only finitely many empty rows. Unit coefficient bound throughout, exact half-prefix/charge/moments eventually.
No quantitative m_N growth supplied.
Absolute Lambert divisor identity sum mu(k)/(exp kt-1)=exp(-t).
Charge0 and frozen headM imply actual |r_N(t)|<=2 exp(-(M+1)t)/(1-exp(-t))^2.
Therefore fordelta>0:
||r_N||L2([delta,infty)) <= sqrt2 exp(-(M+1)delta)/[(1-exp(-delta))^2 sqrt(M+1)].
Full norm near0 still OPEN; finite feasibility/diagonal cannot prove it.

IMPORTANT jets use RIGHT-HAND ANALYTIC EXTENSION h(0)=1/2. Existing corpus positive-half-line function assigns0 at0; do not claim derivative results for that point-defined function without defining extension. All positive-t values/L2 same.
Derivative identity: r0=1+.5 sum a, r^(2j)=1, r^(2j-1)=-1-B2j/(2j)*sum a k^(2j-1).
Existing read arithmetic inputs:
RHTower.deningerHarmonicPartial_tendsto in DeningerHarmonicPartial.lean;
RHTower.deningerHarmonicLimit_eq_zero in DeningerMobiusHarmonicZero.lean;
RHTower.Sieve.deningerMertensM_log_pow_four_rate in Sieve/MoebiusHarmonicLogRate.lean.
Could simplify weighted moments via harmonic Abel/Kronecker; not newly formalized.

## K-test completed, all results downloaded
Local docs/drafts/pipeline/2-fully-proven/computations/chronological-boundary-moments-2026-09-06/
Remote /root/chronological-boundary-moments-20260906
Authorized ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519
27 cases N512/2048/8192, half prefix, m0..8. Fixed minimum coefficient-l2 interpolation; no residual optimization/clipping. mp100 Gram/coefficients,3 workers*4BLASthreads;9.183sec inclvalidation.
Best unit norms:
512,m3:4.047746034e-6.
2048,m7:1.284727763e-6. Overallbestm8:5.740579672e-7, coefficientmax1.668729.
8192,m5:5.202639689e-7; all m0..8 unitbounded.
512,m8:1.594275157e-5, coefficientmax10.25581583. More moments can worsen fullnorm.
N8192 m0 .003581989488, m1 .000290138819, m2 5.445263e-6, m3 1.4244331e-5,m4 5.2158341e-6,m6 1.5422287e-6,m7 1.2762475e-6,m8 6.2421283e-7.
Best unit energy fraction belowt1/N:512 8.65557e-5,2048 8.40810e-7,8192 5.00659e-9. Remainder mostly beyond Taylor scale.

TraininglogGauss24; shiftednarrow60validation; actual coefficient budget omittedleft bound max2.62542e-29; exactfloatcharge tail S²/80 and exponential norm upper [1+C/(1-e^-80)^2]e^-80/sqrt2.
Quadrature normdiffmax1.16173e-16. Fourmp100 residualchecks/vector Nt=.01,1,10,100, maxdiff2.95616e-14. Highprecision scaled moment defects~1e-101..1e-93, savedfloatmax1.19298e-15. No rigorous quadrature interval proof.
No zero inputs, no proof inputs.
moments.py imports sibling arithmetic-averaging-20260906/kernel_reference.py; all archivedlocalpreviousfolder.
summarize.py uses matplotlib PYTHONPATH=/root/chronological-bounded-repair-20260906/deps.
REPORT.md,results JSON,all27 CSV,3vectorsNPZ,summary.json,run.log,plotsPNG/PDF archivedlocal+remote. Plot visuallychecked clear2panels.
Correct report relative card path ../../../1-in-progress/... fixed bothlocalremote.

## Process and next work
No Lean process started this turn, so no Lean checks claimed/repeated. Existing154 unchanged.
Remote moments.py and summarize.py completed, pgrep exactownedpath audit exit1/nooutput (none running). All SSH/SCP sessions exited; no live handles.
git diff --check ownscope passed. External concurrent commits picked up files while we worked; no git mutation by us.
Primary literature: https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1227.pdf (Alouges–Darses–Hillion2022, polynomial density does not supply coeffcontrol), and Baez-Duarte2002 classical naturalapprox divergence §4 https://www.kurims.kyoto-u.ac.jp/EMIS/journals/HOA/IJMMS/Volume31_7/242719.pdf (search primarytext retrieved, lateropenfailed). No priorityclaim.

Next: attack quantitative growing-m source near0, while formalizing exact fixed-space boundary and positive source, not another abstract RH receiver. General weighted Mellin implementation likely starts actual S_w(t)=tsum mu(n)w(nt), compactpiecewiseC1 w, absolute Mellin factor M(S_w)=M(w)/zeta forRe>1, then littleo halfpower ray contradiction. Toolchain Mathlib files:
Analysis/MellinTransform.lean (not Mellin/Transform),
MeasureTheory/Integral/DominatedConvergence.lean has hasSum_integral_of_summable_integral_norm, integral_tsum_of_summable_integral_norm.
NumberTheory/LSeries/MellinEqDirichlet.lean has hasSum_mellin but expkernel-specific.
RHTower/MobiusLaplaceCriterionFrontier.lean 1182 mobiusMellin_weight_summable,1195 expkernel identity; existing normboundinterchange canbeadapted.
OneforegroundLean peragent, scratch lake env lean; final requestedleafonly LEAN_NUM_THREADS=1 lake build --old; wireumbrella nofullbuild, printaxioms scratch, lint. No new computation local.