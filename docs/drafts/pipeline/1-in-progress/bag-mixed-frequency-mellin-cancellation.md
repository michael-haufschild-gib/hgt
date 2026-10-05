# BAG mixed-frequency Mellin cancellation

Continuation01aq. Full pointwise joint near-pole source law and exact
physical moving-line pairing are audited. Full signed
physical cancellation remains the target, including frequency regions where
only ONE Mellin variable is within O(1/logN) of its pole.

Corpus basis: JointBaseLimit moving_local_factor/joint_base_factorization,
its locally uniform regular cubic correction and cubicEulerCorrection_zero_left;
CriticalMellinDeformation exact one-balanced formulas; MovingLabelRows four
rational profiles; full physical ConeMellin/MovingMellin/Transverse.
Search36022 nonpartial65921files gen1245688, noerrors/backgroundrefresh
incomplete; all20candidate+20source entries inspected. The fixed-window
Mertens theorem does not justify rapidly oscillating log-prime tests.
Search40490 nonpartial65920files gen1245673: exact transition retrieved;
proposed unrelated D4BM remainder lemmas do not supply physical BAG control.

Conjecture M1 (NOT PROVED): let L=logN, s=1+u/L,
t=1+v/L+i*tau, with fixed u!=0, fixed v and real tau!=0. Then the full
original completed labelled source divided by L^2 tends to
  exp(-2*gamma) * G(u),
  G(u)=exp(P(u))*(1-E(u))^2/u,
  E(u)=integral_0^1 exp(u*x) dx,
  P(u)=integral_0^1 (exp(u*x)-1)/x dx.
The limit is conjectured independent of v and nonzero tau. Domain/integrability
and every normalization require proof; no statement is placed in production.

Derivation to test: the exact Euler factorization retains R(u-v_N)R(v_N-u)/
(R(u)R(v_N)), v_N=v+i*tau*L. Boundary Euler products, if proved uniformly
under the O(1/L) shifts, predict H_N/L -> exp(gamma+P(u))/zeta(1+i*tau).
The regular correction tends to1 at the zero-left boundary. Original zeta
cofactors cancel the displayed zeta factor, leaving the unlabelled trace/L^2
->exp(gamma+P(u))/u. The leading actual rows divided byL should tend to
1-E(u),1,1-E(u). All collisions still need control. Mertens normalization
then predicts M1. This is a corpus-grounded derivation with open analytic
steps, not a proof by substituting unbounded parameters into the joint law.

Theorem M2 (LEAN PROVED, production13632): G has a removable zero at u=0 and its signed
vertical integral is zero on every positive real line. This would permit
cancellation inside the mixed-frequency leading term, rather than estimating
its absolute mass. It does not itself control the actual remainder or tails.

Candidate paper mechanism for M2: E(0)=1, hence the numerator has a double
zero. P is entire. In the left half-plane, write Re(P(u)) as the real integral
of (exp(Re(u)*x)*cos(Im(u)*x)-1)/x. Split at1/|u|. If -Re(u) dominates |u|,
exponential decay bounds the remaining positive term. If |Im(u)| dominates,
integration by parts against sin(Im(u)*x) bounds it using the decreasing
amplitude exp(Re(u)*x)/x. Both suggest Re(P(u))<=C-log|u|. A fixed positive
horizontal shift changes P by a bounded integral. Consequently G is O(|u|^-2)
on large left semicircles. Cauchy closure gives zero vertical integral.
Each inequality, holomorphy, and improper-contour passage must be audited.

Required hard work: prove M1 with actual prime oscillation and boundary Euler
products; couple the proved M2 cancellation to the ACTUAL moving physical profiles
and near-cone/tail sectors with uniform remainders at o(N/log^2N). Growing
moments/cofactors and deterministic common-height return remain open.

Corpus contour receiver found and read: HTGeometry/VerticalStripContourShift,
GaloisForLFunctions.HTGeometry.integral_vertical_line_eq_of_horizontal_tendsto
and tendsto_intervalIntegral_of_tendsto_bound. Search96015 nonpartial65925files,
gen1245723, noerrors/background refresh incomplete, all20+20 inspected.
The generic strip theorem supplies the final contour step once G is entire
and its actual decay is proved. No generic theorem's hypotheses are being
counted as a solved BAG estimate.

Stronger paper argument for M2: for Re(u)<=0 and R=|u|>=2, split the real
P integral at1/R. The small segment is nonpositive. On[1/R,1], subtracting1
integrates to-logR. If -Re(u)>=R/2, the remaining exponential integral is
bounded after scaling x byR. Otherwise |Im(u)|>=R/2. With
q(x)=exp(Re(u)*x)/x decreasing, integration by parts against sin(Im(u)*x)
bounds the remaining cosine integral by2*q(1/R)/|Im(u)|<=4. Hence
norm(exp(P(u)))<=C/R throughout the left half-plane. For fixed c>0,
P(u)-P(u-c)=int_0^1 exp((u-c)*x)*(exp(c*x)-1)/x dx has norm<=P(c)
when Re(u)<=c. Also norm(E(u))<=E(c). Thus G(u)=O(|u|^-2) on each such
half-plane outside a fixed disc; its zero at0 removes the apparent pole.
For each X>1, use the corpus rectangle theorem to shift the c-line to-X;
horizontal edges vanish by the uniform inverse-square estimate. The latter
line integral has norm<=C*int_R 1/(X^2+t^2)dt=pi*C/X, hence tends to0.
This proves the proposed signed zero on paper, subject to formal audit of
entireness and the stated elementary integral bounds. M1 still unproved.

01aq: prior turn classified PROGRESS. New M2 proof mechanism: F=exp(P),
P'=E and u*E=exp(u)-1 imply (uF)'=exp(u)*F. ReP(u)<=P(c) on Reu<=c.
The derivative therefore decays exponentially toward the left. Corpus
norm_integral_vertical_le_of_halfPlane_decay, reflected, should bound its
vertical primitives; real negative-axis integration bounds the base. This
gives bounded uF on left half-planes and inverse-square decay of actual G,
without the previously proposed oscillatory cosine split. Build P/E/G
entireness and exact ODE first, then discharge this actual derivative bound
and the existing contour-shift receiver. No new convergence premise.

01aq M2 complete: scratch58685 and production13632 empty PASS. The 436-line
ChiRamanujanMixedProfileCancellation leaf proves the actual compact-integral
P derivative, entire G, G(0)=0, exact nonzero formula, primitive ODE, left
half-plane inverse-square bound, full vertical integrability and signed
integral zero. Wired once; index21794 PASS, 11 public declarations.
Axioms52462 PASS, all11 public declarations use only the standard three axioms.
Lint15411 has unrelated unreachable modules/existing warnings, none in this leaf. No M1/physical saving claimed.

Next M1 mechanism, grounded in PrimeZetaOneLineConvergence and
PrimeZetaUniformCompactFrequencyTail: the actual prime-ordered sums
S_tau(x)=sum_(p<=x) p^(-1-i*tau) converge for tau!=0. For a fixed smooth
logarithmic profile H and L=logN, finite summation by parts gives
 sum_(p<=N) p^(-1-i*tau)*H(logp/L)
 = H(1)*S_tau(N)-int_0^1 H'(t)*S_tau(N^t)dt.
Bounded convergent S_tau and DCT should give H(0)*lim S_tau. For H(t)=exp(wt),
this preserves the boundary sum; H(t)=t*exp(wt) gives zero for the normalized
oscillating response rows. This attacks the actual growing prime source;
it does not substitute unbounded parameters into the old fixed-window law.
Boundary Euler identification and collision/remainder transfer remain to prove.

Search56539 partial65935files gen1245994, text/source stages interrupted,
background refresh incomplete; all20 candidates+20 source entries inspected.
Search2747 nonpartial65935 gen1246061/current1246067, coverage older generation,
no errors, background refresh incomplete; all20+20 inspected. It retrieved
primePhaseSum; following its actual source gave exists_tendsto_primeCpowSum
and the compact-frequency PNT error tail. No assumed prime convergence.

M3: actual off-pole moving Euler ratio. For tau!=0 and fixed complex u,
 product_(p<=N) [1-p^(-1-i*tau+u/logN)]/[1-p^(-1-i*tau)] -> 1.
Derivation: the signed linear log difference tends to zero by the proved-on-
paper oscillatory logarithmic-window law. Uniformly once |Reu/logN|<=1/4,
the moving and fixed nomes have norm<=3/4 and square norm<=p^(-3/2).
Thus log(1-q)+q remainders have a summable common majorant and converge
pointwise to their fixed counterparts. DCT pays their complete growing
prime sum; exponentiating the actual finite logarithmic identity gives M3.
This is stability relative to the exact boundary product; it does not yet
identify that product with 1/zeta(1+i*tau). It directly pays the moving-shift
part of M1 and will retain the original product cutoff.

Latest search83770 partial65942files gen1246214, interrupted text/source
stages, stale coverage snapshot/background refresh incomplete; all20+20
inspected. No retrieved Euler-boundary identification theorem verified.
Search7947 nonpartial65938files gen1246120, noerrors, coverageolder/background
refresh incomplete; all20+20 inspected. Its bounded-partial-sum proof supplied
the actual floor-extension bound used in the new prime-window proof.

Actual oscillatory windows: scratch11875 and production93239 empty PASS.
ChiRamanujanOscillatoryLogWindow243lines wired once; main theorem retains
original primes<=N and all fixed complex tilts, with common boundary limit.
The full exponential difference prime sum tends to0. Axiom/index audit pending.
M3 full actual Euler-ratio scratch now auditing. No M1/physical saving yet.

M3 proven: scratch13235 and production57574 empty PASS; new
ChiRamanujanMixedEulerTilt256lines wired once. The literal complete prime
Euler ratio tends to1, including its actual linear term and complete summed
nonlinear log remainder. Main theorem takes only nonzero frequency domain
and fixed complex displacement; no unproved convergence hypothesis.
Together with prime-window production93239 this pays two actual-source
inputs of M1. Full M1 identification and physical norm saving remain open.

Next M4: identify the boundary Euler product with1/zeta(1+i*tau), then use
M3. Corpus search58506 nonpartial65945files gen1246322/current1246326,
noerrors, older coverage/backgroundrefresh incomplete; all20+20 inspected.
It found DeningerDirichletAbel/Limit. Read DeningerAbelianLimit,
DeningerAbelAverage, DeningerAbelSummation and relevant bounded-partial-sum
continuation definitions. Proposed proof: (i) actual boundary prime-sum
convergence plus summable log remainder gives a nonzero boundary product;
(ii) extend the real Abel probability-weight theorem to complex partial sums
by their real and imaginary parts; (iii) identify the absolutely convergent
right-hand prime series with its Abel average; (iv) take sigma down to0,
using the same summed log remainder and zeta continuity away from its pole.
Every atom and actual cutoff remains present. M4 is not Lean proved yet.

Final actual-source audit01aq: production93239/57574 emptyPASS, axiom25259
all8 public declarations standard3, index95668 PASS/API6+2/importseachonce.
Final lint24717 running. P2/P3 actual prime-window and Euler tilt-stability
cards current; frontierag.13 records exact scope. M4 is next, without pivot.

Closure01aq: lint24717 terminal1,17unrelatedunreachablemodules174warnings,
none in the three new leaves. All owned Lean/search/index processes terminal.
Production436+243+256lines,19publicAPI total, allstandard3/noextraaxioms.
Owned completed scratch sources/templates removed; logs/searchJSON retained.
Next M4 has dependency-closed paper proof in P2 bag-boundary-euler-identification,
Lean not started. All actual labelled/physical M1 remainders stay open.

Continuation01ar, BAG. Prior01aq PROGRESS (three audited frontier obligations).
Active M4: actual boundary Euler product identification. Preserve full scope:
complex Abel limit of convergent actual prime partial sums, original prime
product, all nonlinear log remainders, right-half-plane Euler identity and
boundary zeta continuity. Lean work starts in /tmp/bag-boundary-euler-01ar.lean.
No active owned build at init; search92754 running. No subagents.

01ar M4 COMPLETE: criticalBoundaryEulerProduct_tendsto and
criticalMixedEulerProduct_tendsto in ChiRamanujanBoundaryEulerProduct,
313lines/API2, original cutoff throughout. Scratch61580, production35732,
axiom20469 PASS; both public conclusions standard3 only. Production has one
nonfatal ring information message. Index35848 PASS/importonce; lint35721
has unrelated findings only. No full/umbrella build. Next M5 actual mixed
rational rows/collisions has dependency-closed paper proof in P2
bag-mixed-frequency-label-rows. Scratch24248 running compact-phase window
error and actual rational denominator foundation. M1 remains unproved.

01ar paper M1 closure: P2 bag-mixed-frequency-completed-source now gives
full dependency-closed pointwise derivation, including original finite
Euler ratios at both signs of tau, local uniform cubic correction at
(1,0,i*tau), both original cofactors, actual rows/collisions and full masked
assembly. The limit is exactly exp(-2*gamma)*G(u). No growing parameter
substitution into a fixed-window theorem. Lean M1 assembly still pending.
M5 scratch77776 emptyPASS foundation;14241 current row/collision audit.
After M1 formalization, actual uniform physical-profile/tail control remains
hard; zero signed integral of G alone does not pay the physical remainder.

01ar M5 COMPLETE: ChiRamanujanMixedLabelRows664lines/API5.
Actual four rows /L ->1-E(u),1,1-E(u),1-E(u); every exact collision/L->0
for ALL real tau including0; full original masked response/L^3->(1-E(u))^2
for nonzero tau. Scratch14241 and production7092 emptyPASS. Axioms35601
all5 standard3; index41583/importonce/API5. Lint66985:11unrelatederrors,
174warnings, noneowned. P2/P3/frontierag.13 current. Full M1 pointwise
paper proof in P2 bag-mixed-frequency-completed-source; next Lean target
is its actual mixed unlabelled product/cofactor and complete assembly.
No numerical computations or assumed bounds. Physical saving remains open.

Continuation01as, BAG. Prior01ar PROGRESS: actual boundary/moving Euler
identification and full mixed rows/collisions/masked response audited.
Init memory read; architecture/testing docs absent; frontierag.13/ag.19
and STATUS MUST-561 checked. No active owned build at start. No subagents.
Plan: formalize exact mixed unlabelled finite Euler factorization and limit,
attach both original cofactors, prove full original completed M1 limit;
foreground leaf and axiom audits, wire/index/lint, then attack actual
uniform physical-profile/tail transfer. P2 bag-mixed-frequency-completed-source
read; no analytic or RH premise may be assumed. Corpus search running.

01as mixed-base scratch39831 PASS (unused simp removed); final production63164
emptyPASS, ChiRamanujanMixedBaseLimit341lines/API4, wired once. Actual full
H_N/logN limit and complete unlabelled trace/logN² limit proved, with both
original cofactors and simultaneous full-cutoff local nonvanishing.
Updated existing MaskedMellinSource with one actual mixed-response theorem,
reusing its exact private finite algebra; production audit running.
M1 final profile assembly scratch prepared, dependent audit not started.
