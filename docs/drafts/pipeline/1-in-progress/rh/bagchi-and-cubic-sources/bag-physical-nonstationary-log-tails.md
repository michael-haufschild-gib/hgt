# BAG actual physical tails before logarithmic pullback

01ax. Active frontier preparation, not a theorem closure. Route BAG actual
moving cubic transfer. Finish selected-kernel strong convergence audit first.

Exact source facts: ChiPrimeGaussianCubicFourierLattice defines the full
physical amplitude with reciprocal factor 1/r, not 1/r². The latter belongs
to the SECOND Fourier kernel. Consequently the expected normalized physical
cone identity, after p=NP,q=NQ,r=NR, is
 H_N(x,y)=2*pi*N * integral_RQP
 F_N(P)F_N(Q)conj(F_N(R))/R * W(PQ/R)
 * exp(2*pi*i*N*(PQ/R-xP-yQ+xyR)).
The prefactor is N, not N². This is a source-derived normalization check;
its exact Lean identity remains to be supplied before tail conclusions.
Transverse.integral_three and the existing positive-dilation integral
identity are the relevant audited change-of-variable mechanisms.

Conjecture: every fixed polynomial weight times H_N and each pure first/
second physical coordinate derivative is uniformly small outside a fixed
positive box containing[1/2,2]^2, with enough square integrability for the
positive log pullback. Prove a decay estimate for arbitrary fixed derivative
and weight orders, rather than assuming a uniform Schwartz budget.

Mechanism to prove. The phase equals (P-Ry)(Q-Rx)/R. Its P-gradient is
Q/R-x and its Q-gradient is P/R-y. With P,Q,R in[1,2], stationary physical
coordinates lie in[1/2,2]. Outside[1/4,4], the relevant gradient is separated
from zero by a constant times1+|coordinate|. Pick the larger outside
coordinate; if the other coordinate is larger, it too is outside. This
selection controls polynomial factors in both physical coordinates.
Pure x-derivatives of order j multiply the integrand by
(2*pi*i*N*(-P+yR))^j; pure y-derivatives are symmetric. Mixed derivatives
are not given by the naive product because the phase has nonzero xy second
derivative. Avoid that false shortcut: pure second derivatives suffice for
the Fourier H² bound and for pure log-coordinate second derivatives.

Repeated integration by parts in the selected compact P/Q coordinate uses
actual all-order amplitude budgets, with fixed window and polynomial factors
attached BEFORE estimating derivatives. It gains N^-n*delta^-(n-1).
Including the correctly checked physical prefactor N and j derivatives,
delta=N^-3/4 gives N^(j+1/4-n/4). For arbitrary fixed j and polynomial weight,
a sufficiently large fixed n makes this tend to zero and leaves an integrable
position majorant. Formal obligations: exact physical identity; derivative
under the full compact integral; polynomial-window amplitude budgets;
nonstationary bound including both outside-coordinate cases; full weighted
integrability and log-coordinate measure/Jacobian control.

The log profile at sigma_i=1+rho_i/logN multiplies by x^sigma1*y^sigma2;
du dv=dx dy/(xy). Near the axes, sigma_i>=1 should pay the Jacobian; at
infinity eventual sigma_i<=2 gives fixed polynomial weights. This still
needs proof. Inside the positive box, fractional regularity under smooth
log coordinate change is a separate missing theorem; ordinary weighted
Fourier convergence does not automatically provide Mellin line-tail control.

Search58802 /tmp/bag-physical-log-tail-search-01ax.json: nonpartial,
all66743files indexed, noerrors; index1253192, coverage1253197/current1253198;
semantic coverage unmeasured, background refresh incomplete. All20 candidate
and20 source statements plus proposed ingredient set inspected. Its D4
nonstationary-core ingredients concern another integrand and are not a proof
for this actual BAG family. Useful exact source pairing:
ChiPrimeGaussianCubicMovingMellin.criticalRationalCone_physical_line_hasSum.
Direct sources inspected: actual amplitude, controlled physical Schwartz,
Transverse.integral_three, normalized Fourier rescaling, PositiveQuadrantLog
Schwartz public signatures, and scalar GagliardoFourierConstant. The last
supplies fractional phase-integral control, not yet coordinate-change bounds.

Subsequent hard work remains: log pullback and Mellin line tails, lower-growth
complete arithmetic envelope, moving signed cancellation, full sharp-action
bridge, growing moments/cofactors and deterministic common-height return.
RH remains open. No stationary substitution or analytic bound assumed.

Stronger survivor to target after the exact identity: rapid weighted decay
of every fixed pure physical jet outside the positive stationary box.
For arbitrary j,m,k, aim for oneC and eventuallyN, uniformly positive x,y
outside[1/4,4]^2,
 N^k*(1+x+y)^m*|partial_x^j H_N(x,y)| <= C,
and symmetrically for y. This pays all fixed polynomial weights needed by
the logarithmic Jacobian, rather than only one numerical bound.

Coefficient normalization: divide (-P+yR)^j by(1+|y|)^j. Its base becomes
alpha*P+beta with |alpha|<=1,|beta|<=2. If integrating Q instead, the same
polynomial is constant in Q and its normalized value still lies in[-2,2].
The actual fixed window is W(kP), |k|<=2. Therefore all derivative bounds
for (alpha*P+beta)^j*W(kP) onP in[1,2] follow from joint smoothness and a
compact parameter box. A generalized partial-derivative smoothness proof,
Leibniz and the already audited actual F budgets give the full attached
L1 derivative budget C_(j,n)/delta^(n-1). Candidate private proof is in
/tmp/bag-physical-tail-budgets-01ax.txt, not yet compiled or claimed.

For positive x,y outside the box, select a coordinate depending only onx,y
such that its phase gradient is bounded below by a constant times1+x+y,
uniformly in the compact physical variables. If max(x,y)>4, use the larger
coordinate. Otherwise both<=4 and one<1/4, giving a fixed separated gradient
and bounded position weight. This avoids a hidden unbounded other-coordinate
integral. After n integrations, the weighted jet has powers
 N^(j+1/4-n/4)*(1+x+y)^(m+j-n).
Choose a fixed n satisfying both required exponent inequalities. Full jet
admission, the two coordinate cases and derivative identification remain to
be formally proved. Do not silently replace those with a pointwise value bound.

Exact physical phase CLOSED in production36893emptyPASS:
ChiCubicNormalizedPhysical152lines/API2, both axiomprints28398standard3,
index42693PASS/importonce, lint74659pending. P2 bag-normalized-physical-phase.
Current one owned Lean11988 /tmp/bag-physical-nonstationary-tails-01ax.lean:
compact polynomial-window budgets, literal cube admission for all pure jets,
derivative under the integral, and identification with actual iterated
physical derivatives. First budget audit28398 found missing explicit complex
linear-map smoothness and one reducible-function rewrite; corrected.
New jet admission is not yet claimed. Consumed template copies are stale;
current scratch is source of truth after each fix.

01ax exact NORMALIZED PHYSICAL phase CLOSED: ChiCubicNormalizedPhysical
152lines/API2. Actual physical prefactor2pi*N, reciprocal1/R and phase
2pi*N*(P-Ry)*(Q-Rx)/R, every original factor retained. Scratch74577PASS;
production36893emptyPASS; both axiomprints28398standard3; index42693PASS,
umbrellaonce; scoped diffcheckPASS. Lint74659terminal1: unrelated
KuznetsovEisensteinGrowth and HTGeometry.ResetPathSingularity unreachable,
362warnings,no ownedleaf finding. P2/P3 and BAG frontier updated.
Current one owned Lean43397 /tmp/bag-physical-nonstationary-tails-01ax.lean:
polynomial-window all-order budgets checked in11988; derivative-jet admission
retry fixes absolute-value lexer collision, convert! for calculus instances,
and eta-expanded integral rewriting. Full physical nonstationary bound is
still open. Consumed exact-identity scratch removed; its logs retained.

2026-10-06 01ax: scratch65948/log04 terminal0PASS. Closed private mechanisms:
all-order polynomial-window attached derivative budgets, literal full cube
admission of every pure x jet, differentiation under the integral, exact
identification with actual iteratedDeriv, and linear-polynomial row IBP.
Full physical tail theorem remains active. Audit95865/log05 found variable
power factorization, interval projection, and tactic-layout gaps in the new
full-row attachment; corrected, next single audit log06. No resource hacks.

New conjecture/mechanism: uniform derivative tail of every fixed order and
weight, using a coordinate chosen solely from x,y. On positive exterior of
[1/4,4]^2, one full row gradient has absolute value at least(1+x+y)/36.
Exact P/Q phase factorizations retain reciprocal1/R and all three slices;
full jet integrability justifies both nested orders. Their row estimates
integrate against actual L1 slice budgets. Selected delta=N^-3/4 then
pays arbitrary fixed N-saving by choosing a sufficiently high fixed IBP
order. This is all-order localization, not a numerical bound optimization.

Corpus search25532 /tmp/bag-physical-gradient-rows-search-01ax.json:
nonpartial,66760allindexed,noerrors,index1253828,coverage1253845=current;
semanticcoverage unmeasured. All20candidate/20source statements and proposed
ingredient set read. Generic candidates concern other phases and do not
supply the actual BAG result; actual attached amplitude budgets and native
IBP remain the applicable foundation. Scratch is source of truth; consumed
polynomial-oscillation template deleted. Row templates pending cleanup after
incorporated proofs pass. No RH closure claimed.

2026-10-06 01ax physical exterior jets CLOSED. ChiCubicPhysicalExteriorDecay
830lines/API2: arbitrary fixed pure derivative/position weight/N-saving
on positive exterior of[1/4,4]^2 for literal selectedfamily. Scratch90088
log09PASS, production52566emptyPASS, bothaxiomprints58537standard3.
Index93916PASS/importonce/diffcheckPASS. Lint41440terminal1: six unrelated
unreachablemodules362warnings, noownedleaf finding (P2/P3 list exactnames).
No assumed budgets or resource hacks. P2/P3 bag-physical-exterior-jets and
BAG frontier updated. Finished tail templates/scratch removed; logs retained.
Next hardtarget: actual localized fractional log-coordinate transfer,
P1 bag-local-log-fractional-transfer. Current scratch
/tmp/bag-directional-gagliardo-01ax.lean extends corpus scalar Gagliardo
identity via translated Schwartz Plancherel and nonnegative Tonelli. First
candidate58537 exposed scalar-zero character simp, abs rewrite loop,
inner-space argument and Fourier-map elaboration gaps. Corrected; log02
audit active, including full spectral admission. Not yet a closedtheorem.
RH remains open; arithmetic moving source/fullsharpaction/selfreturn unpaid.
