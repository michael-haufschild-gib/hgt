# BAG localized logarithmic fractional transfer

2026-10-06, 01ax. Active next obstruction after actual physical exterior jets.
No theorem closure asserted here. BAG route only.

Corpus evidence: selected reciprocal kernels have strong full-plane weighted
Fourier convergence for every fixed s<3/2. Exact normalized physical/Fourier
identities retain all amplitude factors. PositiveQuadrantMellinLines gives
Schwartz membership for each weighted logarithmic pullback, but its bounds
use Schwartz seminorms which need not be uniform for shrinking cutoffs.
GagliardoFourierConstant gives the scalar phase-difference integral, not the
complete fractional composition estimate. Mathlib SchwartzSpace/Fourier
provides integral_norm_sq_fourier; VectorFourier provides translation phase;
SchwartzMap.compSubConstCLM supplies admitted translated Schwartz functions.

Search18926 /tmp/bag-local-log-fractional-transfer-search-01ax.json:
nonpartial,66762allindexed,noerrors,index1254019,coverage1254028=current;
semanticcoverage unmeasured. All20candidate/20source statements and proposed
ingredient set read. BV composition does not prove fractional Sobolev
composition. Vendor SmoothDiffeoBounded/ChainRule inspected by declarations;
no fractional theorem surfaced. Do not assume a missing composition bound.

Target: for fixed smooth cutoff equal to one on[1/4,4]^2 and compactly
supported inside the positive quadrant, the operator
 T_sigma f(u)=exp(-sigma_1*u_1-sigma_2*u_2)*chi(exp(-u))*f(exp(-u))
has uniformly bounded Fourier H^s energy, for sigma_i in[1,2] and 1<s<3/2,
in terms of the same ordinary physical H^s energy. Combine this with the
actual exterior jet theorem, not an assumed uniform Schwartz budget.

Paper mechanism to formalize:
1. Extend the corpus scalar difference-symbol integral to every signed
frequency, with finite strictly positive constant for0<theta<1.
2. Plancherel for each translated Schwartz difference and nonnegative
Tonelli give the exact directional Gagliardo identity in Euclidean space:
 integral_(h>0) h^(-1-2theta) integral_x |f(x+h*v)-f(x)|^2
 = c_theta integral_xi |inner(v,xi)|^(2theta)|Fourier f(xi)|^2.
No interchange before admission; ENNReal first avoids circular integrability.
3. For the localized log pullback, split shifts into a fixed small window
and its complement. Large shifts cost its L2 norm. On small shifts where
at least one cutoff is nonzero, both physical points lie in one larger
compact positive interval. The log map is bilipschitz there; both Jacobians
are bounded. Apply the exact two-point product decomposition to the weighted
cutoff times f. Its squared difference is bounded by a constant times the
physical squared difference plus |x-x'|^2*|f(x')|^2. The second term integrates
against |x-x'|^(-1-2theta) because theta<1. The first is the physical directional
Gagliardo seminorm. All cutoff/weight constants are uniform on compact sigma.
4. Apply that fractional estimate to each first log derivative. The exact
Euler derivative is -sigma_i*f-x_i*partial_i f, plus the cutoff derivative.
This costs only ordinary H^(1+theta) energy; no mixed-jet product shortcut.
5. Actual exterior pure jets through order2 pay global logarithmic tails,
including near-axis Jacobians. Uniform H^(1+theta) Mellin energy then yields
weighted L1 tails against any arithmetic envelope of exponent<theta.

Further hard obligations remain: lower-growth complete arithmetic envelope,
moving-test signed cancellation, full original sharp-action bridge, growing
moments/cofactors and deterministic common-height self-return. RH open.

Actual exterior jets are now production-closed: ChiCubicPhysicalExteriorDecay
830lines/API2, production52566emptyPASS, both public axioms58537standard3,
index93916/importonce, lint only unrelated unreachable modules. P2/P3
bag-physical-exterior-jets has exact evidence. This pays the full exterior
part once the logarithmic measure and Euler-derivative attachment is supplied.

Current Gagliardo candidate /tmp/bag-directional-gagliardo-01ax.lean now has
an exact nonnegative double-integral identity in arbitrary finite-dimensional
real Euclidean space, with a strictly positive constant and admitted spectral
integral for every Schwartz function. Scratch48863/log02 found only three
elaboration gaps: inner bilinear map unfolding, Fourier instance conversion,
and explicit real scalar for inner-product Cauchy-Schwarz. All scalar signed
frequency cases, positivity of the constant, Tonelli, and spectral-majorant
steps otherwise checked. Corrections under log03 audit; full theorem not yet
claimed. This closes the fractional-energy bridge needed by the two-point
log pullback mechanism, not the log composition estimate itself.

2026-10-06 01ax directional fractional-energy bridge CLOSED.
HTGeometry.DirectionalGagliardoFourier243lines/API1: exact full directional
Gagliardo/Fourier identity, positive constant and admitted spectral integral
for every Euclidean Schwartzfunction. Scratch24986/log03PASS, production
42806emptyPASS, public axiomprint89019standard3. Index21971PASS/importonce;
lint55347terminal1:8 unrelated unreachable362warnings, noownedleaf finding
(exactnames P2/P3 bag-directional-fractional-energy). Frontier updated.
Completed Gagliardo scratch/templates removed;logs retained.
Current oneowned Lean /tmp/bag-log-fractional-composition-01ax.lean log02:
nonnegative logarithmic substitutions and exact two-point kernel candidate.
First89019 errors were beta-reduction, derivative conversion, set/univ
constantnames and explicit membership positivity. Corrected, no resourcehacks.
Local compact log-composition bound remains open and is the next hardtarget.
Search86614 /tmp/bag-log-composition-admission-search-01ax.json nonpartial,
66771allindexed/noerrors,index1254416=coverage=current,semanticunmeasured;
20candidate20source+ingredientsetread. Useful PhysicalLogChart and existing
MellinLinePlancherel log substitution; proposed slowLog recipe insufficient.
Actual proof uses installed one-dimensional nonnegative Jacobian theorem.
RH remains open; no assumed composition bound or moving cancellation.

Current exact log two-point mechanism: transform u to x=exp(-u) and
positive shift h to y=x*exp(-h), giving
 integral_(x>0) integral_(0<y<x)
 |f(x)-f(y)|^2*(-log(y/x))^(-1-2s)/(x*y).
A general nonnegative substitution is being proved before specializing the
kernel, so the same admitted identity accepts small/large-shift masks.
Scratch1777/log02 reduced the earlier substitution issues to an explicit
mul_one and a membership-to-positive cast; corrections are in log03 audit.

For f supported in[a,b] within the positive line and shift<=1, any nonzero
difference forces BOTH physical points into[a/exp(1),exp(1)*b]. There,
 -log(y/x)>=(x-y)/x>=(x-y)/B
and1/(xy)<=1/A^2. Thus the full logarithmic fractional kernel is bounded by
(B^(1+2s)/A^2)*(x-y)^(-1-2s). This comparison and the support-pair statement
have been appended to the same scratch for audit. No assumed log distortion
or Jacobian bound. Large shifts must still be integrated via admitted L2
mass, then the near-shift kernel comparison must be assembled and attached
to the planar weighted/Euler-derivative family. These are not yet claimed.

Continuation 2026-10-06, 01ax: exact nonnegative one- and two-point log
substitutions, compact support-pair localization, and logarithmic kernel
comparison passed scratch6843/log04. The assembly now compares ordered
physical pairs directly to negative-direction Gagliardo energy through
x-h; no translation/integrability assumption is hidden in this step.
Large-shift proof uses the squared-difference bound, translation-invariant
mass and the admitted rpow tail; pullback mass costs at most1/a.
Scratch18881/log06 found a residual convert/simp sequencing issue in the
near bound and beta-reduction before an ENNReal rewrite in mass domination.
The other large-shift and tail-integral steps checked. Corrections and full
near/far assembly plus Schwartz spectral corollary are under log07 audit.
No full log composition theorem is claimed until this audit passes.

Search49330 /tmp/bag-log-ordered-pairs-search-01ax.json:
nonpartial66784allindexed,noerrors,index1254831,coverage1254846=current;
compiler snapshot statuses reported, semanticcoverageunmeasured.
All20candidate/20source statements and ingredient set inspected. Proposed
EntireFractionTranslation/nonnegative-pair recipe does not establish the
required real logarithmic fractional composition. Actual argument instead
uses the native Jacobian theorem and measured Haar translation invariance.
Next mathematical obligations: uniform weighted compact multiplier, planar
axial integration and first Euler derivatives, then actual exterior tails.
These remain on the same BAG moving-test route; no pivot to another route.

2026-10-06 01ax compact fractional log-chart transfer CLOSED.
HTGeometry.LocalLogFractionalEnergy518lines/API3: scalar continuous-energy
bound, finite Schwartz spectral corollary, and full two-coordinate axial
log-chart bound with transverse Jacobian paid. Constants independent of the
supported function; no assumed norm/admission budget. Scratch73895/log08 and
81332/planarlog01PASS; final production60539/log02emptyPASS; all3 production
axioms35000standard3; index94569PASS/API3/importonce; scoped diffcheckPASS.
Final lint22415/log02:12 unrelated unreachable,362warnings,noownedfinding;
exact names P2/P3 bag-local-log-fractional-energy. Global lint not clean.
This advances the actual BAG moving-kernel transfer. Weighted compact
multiplication and first Euler derivatives for1<s<3/2 remain open, followed
by exterior attachment/Mellin tails, lower-growth full arithmetic envelope,
moving cancellation/full sharp-action bridge/common-height return. RH open.
Next active paper/proof card: bag-fractional-compact-multiplier. Native compact
C1 bounds and exact product difference yield an admitted near/far increment
remainder; no uniform Schwartz premise is added. Scratch1448/log01 checked
pointwise product/increment estimates; scalar indicator admission needs an
explicit IntegrableOn helper invocation. Corrected before next audit.

2026-10-06 01ax compact parameter fractional multipliers CLOSED.
HTGeometry.FractionalCompactMultiplier269lines/API3: complete C1 multiplier
energy bound, uniform joint-parameter version, finite Schwartz spectral
corollary. Compactness and differentiability derive coefficient budgets.
Scratch64419/log05PASS; production26654emptyPASS; imported axioms29266standard3;
index17064PASS/API3/importonce; scoped diffcheckPASS. Lint49753terminal1:
15 unrelated unreachable,362warnings,noownedfinding; exactnames P2/P3
bag-compact-parameter-fractional-multipliers. Generic multiplier mechanism
closed; actual Mellin coefficient/Euler family remains the next obligation.
P1 bag-compact-mellin-coefficients and scratch /tmp/bag-compact-mellin-coefficients-01ax.lean
now construct literal compact parameter/physical cutoffs and the coefficient
eta(sigma)*chi(x)*exp(sum sigma_i log x_i). Smoothness uses positivity on
physical support and local zero extension off it; no assumed uniform norm.
Initial coefficient audit22339/log01 running. RH/open BAG endgame unchanged.

2026-10-06 01ax actual compact Mellin localization CLOSED.
CompactMellinLocalization343/API21: production56153 emptyPASS, all21 imported
axioms10859 standard3, index75708PASS/importonce/scoped diffcheckPASS.
Lint30292:362warnings,18 unrelated unreachable, no ownedfinding; exactnames
P2/P3 bag-actual-compact-mellin-localization. Actual A,B_i,C_i, uniform mass
and fractional bounds, exact first Euler law and exact Schwartz realization
are closed. Full log H^(1+theta) assembly is active in
P1 bag-local-mellin-sobolev-transfer; no RH/endgame closure claimed.

2026-10-06 01ax full local Mellin H^(1+theta) transfer CLOSED.
LocalMellinSobolevTransfer630/API1: scratch81394/log08PASS, production14804
emptyPASS, imported axioms61350standard3, index6054PASS/API1/importonce16686,
scoped diffcheckPASS. Lint49164terminal1:362warnings,10 unrelated unreachable;
exactnames P2/P3 bag-local-mellin-sobolev-transfer, noownedfinding/globalnotclean.
The actual compact log operator is bounded uniformly over EVERYsigma in[1,2]^2
for every0<theta<1 and Schwartz input, in the FULL planar Fourier weight.
It derives admission and pays both Euler terms/Jacobians without a uniform
high-Schwartz premise. Next P1 bag-selected-local-mellin-energy attaches
literal normalized physical cone profiles with curvaturetau=1/(2*pi), then
exterior log energy/Mellin tails remain. RH and BAG endgame remain unproved.
