# BAG actual physical height averaging and moving-profile transfer

01aw. HARD OPEN. Route BAG; follow U4, not a replacement for its audit.
Corpus: ChiPrimeGaussianCubicMovingMellin, CubicConeMellin,
CubicTransverse, CubicWindowTransition, ChiHyperbolicFourierTransition,
CubicSharpEdges. Search35342 nonpartial66002files, generation1248427=current,
noerrors, refreshincomplete. All20 candidate+20 source statements inspected;
exact physical amplitude/transition/window definitions inspected.

The normalized actual test is L³/N times bagCubicConeLineProfile. Its log
node is exp(-u), its Mellin line is sigma+2pi*i*t. The height window is the
literal smooth bump centered3/2, supported[1,2]. Original cutoff edges
have width N^(1/4), hence relative width N^(-3/4). The sharp/smooth error
is proved at that scale. Replacing these with fixed relative edges is not
paid by the current error theorem. No uniform Schwartz seminorm is known.

Conjecture P1: the full normalized cone profile has a stationary limit
H(x,y)=2pi*integral_R F(Ry)*F(Rx)*conj(F(R))*W(R*x*y), where
F=1_[1,2]*smoothAFECutoff and W is the ACTUAL height window. This formula
is only a conjecture for the actual profile: neither stationary replacement
nor a norm remainder is proved. It follows formally from the corpus exact
bilinear multiplier after scaling r=NR, its dual frequencies by1/N, and
letting multiplier exp(-2pi*i*R*xi*eta/N) tend to1. Dominated convergence
cannot be asserted uniformly for the shrinking-edge Fourier amplitudes.

If P1 holds, its Mellin transform at s_i=1+2pi*i*t_i is exactly the triple
box integral with amplitude
  2pi*F(p)*F(q)*conj(F(r))*W(p*q/r)*q^(s1-1)*p^(s2-1)*r^(-s1-s2).
Thus its three log frequencies are t1,t2,-t1-t2. One integration by parts
in EACH of the independent p,q,r variables suggests the anisotropic bound
C/((1+|t1|)*(1+|t2|)*(1+|t1+t2|)). This uses only uniform first variation
of each cutoff, not arbitrarily high derivatives. It gives axial quadratic
decay and full-plane integrability. An actual-family counterpart plus
convergence in the corresponding source-weighted topology is the target.
Neither the formal stationary triple integral nor this decay bound has yet
been audited. U3's T^54 envelope alone is insufficient for this class.

Exact structural identity exposed by the original phase:
phi=P*Q/R-x*P-y*Q+x*y*R is invariant under
(P,Q,R,x,y)->(lambda*P,mu*Q,lambda*mu*R,x/lambda,y/mu).
The physical height argument P*Q/R is also invariant. Therefore logarithmic
physical scaling fields may transfer Mellin derivatives without N loss.
Their repeated application hits the same cutoff derivatives, so this
identity by itself does not supply the conjectured three-factor decay.
Equivalent invariant coordinates w=P*Q/R,u=x*P,v=y*Q give
phi=(w-u)*(w-v)/w. A rigorous oscillatory/Mellin interchange would expose
a universal kernel and the full three-cutoff height convolution. Absolute
interchange over positive x,y is NOT available from the present formulas.

Next work: finish U4 audit; prove or refute actual height-averaged weak
regularity/tails via the exact multiplier or invariant coordinates. Any
needed arithmetic envelope must match this physical function class;
changing a numerical exponent without enabling that transfer is not a
frontier advance. No physical cancellation, norm saving or RH claim.

Further paper mechanism01aw (UNVERIFIED; explicit obligations retained):
Choose a monotone smooth edge family eta_N with edge N^1/4. On P in[1,2],
F_N,tau(P)=eta_N(NP)*smoothAFECutoff(P)*L/log(NP)*exp(-i*tau*logP).
Its first variation is uniformly polynomial in |tau|; kth derivative L1
is O_tau(delta^(1-k)), delta=N^(-3/4). Such a family must be constructed,
not inferred for every cutoff satisfying only support and range bounds.

Scaling the exact transverse multiplier suggests the ordinary two-variable
Fourier formula for normalized cone profile H_N:
  Hhat_N(a,b)=integral_tau,R c(tau)*conj(F_N,0(R))*R^(i*tau-2)
    *exp(-2pi*i*a*b/(N*R))*Fhat_N,tau(b/R)*Fhat_N,tau(a/R).
Constants/signs/interchanges still require exact proof from corpus Fourier
conventions. The Mellin window factors N^(2i*tau) cancel the two slice
factors N^(-i*tau); no original height window is discarded.

For |a|,|b|>=1, write each Fhat via its derivative measure mu_N,tau.
Then two integrations by parts cancel R^-2 and expose phase
  (a*v+b*u+a*b/N)/R,  u,v in[1,2],
with prefactor 1/(a*b). R integration, using first variation of F_N,0,
is bounded by C_tau/(1+|a*v+b*u+a*b/N|). In low frequencies
max(|a|,|b|)<=N/4, derivative of that phase numerator in b is
u+a/N>=3/4. Near its zero, |a| and |b| are comparable. The weighted L2
kernel integral is therefore controlled by integral_1^infty k^(2s-4)dk,
finite for s<3/2. Frequency strips with one coordinate <=1 use only the
other Fourier derivative and R derivative. High frequencies >=N/4 use
higher derivative bounds of the actual smoothed edges. If one coordinate
is high, a crude weighted L2 estimate costs N^(2s-k/2-1/2); k large pays
this without a stationary approximation. Thus a UNIFORM H^s bound for
1<s<3/2 appears accessible. It is not proved until the kernel integration,
Minkowski/Plancherel, tau budgets and exact Fourier identity are supplied.

Compact-frequency convergence follows from F_N->F in L1 and the exact
multiplier tending to1. Uniform H^s' tails, s<s'<3/2, would upgrade this
to strong H^s convergence. To transfer through the positive log map, also
prove weighted H2-smallness outside a fixed box inside the positive
quadrant. There the p or q stationary equation is separated from zero;
repeated integration by parts gains N^-k delta^(1-k), enough to pay fixed
position derivatives and weights. This step is still unproved.

Why this regularity would close actual test transfer: source envelope of
arbitrarily small positive polynomial order plus a constant bulk term,
combined with H^s convergence after log pullback, would give weighted L1
convergence of Mellin profiles. Their first frequency derivatives correspond
to multiplying the compact log-space profile by a coordinate. Vector-valued
1D Sobolev control then gives uniform weighted L1 tails along every vertical
or horizontal frequency line. The nearest-axis rescaling proof uses exactly
these line-tail bounds, uniform convergence on compact frequency sets, and
the integrable x-profile. The constant bulk term costs O(1/L). No assumption
of uniform high Schwartz seminorms is needed. All these transfers must be
proved for the ACTUAL selected cutoff family before any physical conclusion.

Corpus search44654: nonpartial66005files,coverage1248490/current1248491,
noerrors,refreshincomplete; all20candidate+20source inspected. Actual
ZetaVerticalLineBound.norm_riemannZeta_le_log_add and ZetaLogDerivBound
.norm_inv_riemannZeta_le plus Euler-region inverse bound support a global
polylog bound for zeta and reciprocal on 1<sigma<=2 away from t=0. Outside
the narrow strip use 1/(sigma-1)<=log^9|t|/A. Small heights use the filled
residue bounds. With U1/U3a and saturated pole size min(1,epsilon+|t|),
this gives the prospective source class T^epsilon*(1+two axes kernels).
Its purpose is a change of admissible physical test class, not numerical
constant/exponent optimization. This source-class upgrade remains unproved.

01aw kernel refinement: no distributional BV framework is needed at finiteN.
F_N,tau is smooth compactly supported, so use ordinary derivative densities
F'_N,tau(u)du with uniform L1 norm. Its Fourier derivative identity gives
the same u,v integral and first-variation height bound. The central scalar
energy obligation is uniform integrability, for 1<s<3/2, of
 (1+a²+b²)^s / ((1+|a|)^2*(1+|b|)^2*
   (1+|a*v+b*u+a*b/N|)^2),
on |a|,|b|<=N/4, uniformly u,v in[1,2]. Put c=a*v+b*(u+a/N).
The coefficient u+a/N belongs[3/4,9/4]; hence the slice change b->c has
uniform Jacobian. Among a,b,c, two largest magnitudes are comparable.
Partition by the smallest: the integrand is controlled by a finite sum
of separable products with powers -2 and 2s-4. The latter is <-1 exactly
when s<3/2. This provides a direct proof target for the low-frequency
energy, not a numerical experiment. High-frequency tail uses higher
ordinary cutoff derivatives. Exact constants and all measure interchanges
remain proof obligations; no H^s theorem or physical transfer marked closed.

01ax U4 fixed-test signed transfer CLOSED (P3 bag-signed-source-sector-transfer).
Central curved scalar energy also CLOSED (P3 bag-curved-frequency-energy):
all0<=s<3/2, entirestrip |lambda*a|<=1/4, allrealcurvatureincludingzero.
Actual profile H^s still open. Next selected cutoffs use corpus blockWindow
with endpoints1+delta,2-delta. Existing global derivative bound loses delta;
positive derivatives vanish in the plateau, so their support has length2delta.
Localizing derivative L1 mass to the two transition strips gives uniform
first variation and kth derivative O(delta^(1-k)), exactly the missing
physical-family budget. P1 bag-controlled-physical-cutoffs.

01ax exact reciprocal-phase target (new derivation, NOT Lean audited):
Let f_N(p)=bagCubicMellinSliceValue N eta_N 0 p, and H_N(x,y) be L³/N
times the original physical three-coordinate Fourier amplitude restricted
to(x,y,-xy). A second ordinary Fourier transform in(x,y) should equal
 (2pi L³/N)*integral_p,q,r f_N(p)f_N(q)conj(f_N(r))*W(pq/(rN))/r²
                 *exp(-2pi*i*(p*b+q*a+a*b)/r).
After p=NP,q=NQ,r=NR, put F_N(P)=L*f_N(NP). This becomes EXACTLY
 2pi*integral_P,Q,R F_N(P)F_N(Q)conj(F_N(R))*W(PQ/R)/R²
                 *exp(-2pi*i*(P*b+Q*a+a*b/N)/R).
All physical factors and the full W remain; no window Mellin phase is
needed in this final representation. Fixed-r derivation: Fourier inversion
in y sets q=r*x-b; change x=(q+b)/r then combines the original pq/r phase
with -(p+a)(q+b)/r, yielding -(pb+qa+ab)/r. This can be proved by ordinary
one-dimensional Fourier inversion on Schwartz slices, without a formal
delta function or unproved oscillatory interchange. Compact r interchange
still needs uniform fixed-N slice integrability and must be supplied.

Two P,Q integrations by parts then cancel R^-2. Differentiating W(PQ/R)
only creates bounded coefficients on[1,2]^3. R first variation exposes
D=P*b+Q*a+a*b/N, the exact phase in the new audited strip energy theorem.
The derivative densities (|F_N|+|F'_N|)(P)(|F_N|+|F'_N|)(Q) have uniform
mass once selected-amplitude budgets are proved. Thus the direct formula
also removes auxiliary tau-uniformity/interchange work from the regularity
argument, while preserving the original window. This is a paper mechanism,
not yet a formal identity or physical H^s theorem.

Search48168: nonpartial but inventory incomplete66653files/170pending;
coverage1249451/current1249497, noerrors, refreshincomplete. All20candidate
and20source statements inspected. Relevant corpus: partial Fourier inverse
ChiPrimeGaussianCubicPartialPoisson, physical rows in CubicTransverse,
exact kernel/transition in ChiHyperbolicFourierTransition. No exact direct
cone-Fourier identity retrieved. No broad novelty claim.

01ax reciprocal identity CLOSED: ChiCubicReciprocalFourier, production13249
emptyPASS/axiom77734standard3. Full physical-height interchange and actual
selected-amplitude specialization are proved, with all windows/log slices.
P3 bag-cone-reciprocal-fourier. Normalized scaling and amplitude derivative
budgets remain; next P1 bag-actual-amplitude-derivative-budgets.

01ax actual amplitude derivative budgets CLOSED: core compact-parameter
regularity, global smooth support, all-order L1 budgets, exact original
physical-slice attachment. P3 bag-actual-amplitude-derivative-budgets;
production70720emptyPASS/axiom83857all5standard3. Exact normalized Fourier
scaling scratch49555 running. Next actual coupled kernel energy uses
regularizedP/Q/R IBP, weighted Cauchy-Schwarz and the audited strip energy;
P1 bag-actual-reciprocal-kernel-energy contains the full paper mechanism.

Exact normalization CLOSED01ax: ChiCubicNormalizedFourier78lines/API1,
bagCubicControlledCone_normalized_fourier. For everyN>1 and admissibleH,
(logN)^3/N times the ACTUAL cone Fourier transform is exactly
 2pi integral_RQP F(P)F(Q)conj(F(R))*W(PQ/R)/R²
                *exp(-2pi*i*(Pb+Qa+ab/N)/R),
F=bagCubicNormalizedSlice(H/N,1/logN). Three explicit positive-dilation
changes of variable supplyN³; exact slice identities and total-field
algebra, includingR=0, pay all normalization/Jacobian factors.
Scratch49555PASS (two redundanttactics removed); production15138emptyPASS;
axiom95238standard3; index35848PASS/API1/importonce. Lint28068terminal1:
two unrelated unreachable(KuznetsovKernelIntegral,KuznetsovPoincareRows),
362warnings,noownederror. Diff checkPASS. No full/umbrella build.
The actual coupled energy estimate remains open; normalized identity
supplies its literal target. Scratch /tmp/bag-reciprocal-ibp-01ax.lean
now tests exact height resolvent and norm control; no further claim yet.

01ax actual reciprocal height decay CLOSED: production9533emptyPASS,
axiom44627all3standard3,index96838PASS/API3/importonce. Lint89133fiveunrelated
unreachable362warnings,noownederror. P2/P3 bag-actual-reciprocal-height-decay
record exact uniform all-jet actual theorem and proof. Tangential attachment,
full kernelenergy and RH remain open. Current single Lean scratch68100:
/tmp/bag-tangential-resolvent-01ax.lean, native single-fibre linear resolvent.

01ax actual coupled kernel decay CLOSED: ChiCubicCoupledKernelDecay723lines/API3.
One uniformC bounds the full actual reciprocalkernel by the integral of
w(P)w(Q)/((1+|a|)(1+|b|)(1+|Pb+Qa+c|)), allδ,hstructural and ALLreala,b,c.
Exact1+partialP/Q resolvents generate three heightjets; compact fullcube
admission pays allFubini swaps, includingR=0 bysupport. Actual heightdecay
plus coefficient bounds pays the coupledmajorant. Exact originalFourier
attachment retains2pi and nativecurvature1/(2piN), not1/N in nativevariables.
Production44357emptyPASS; axiom97812all3standard3; index18086PASS/API3/importonce.
Lint78177sixunrelatedunreachable362warnings,noownederror; scoped diffcheckPASS.
P2/P3 bag-actual-coupled-kernel-decay. Uniformactual stripenergy now in
scratch13277 /tmp/bag-coupled-strip-energy-01ax.lean, using existingreal
weightedCS and U5. Fullglobalenergy/Mellintails/movingtransfer and RH remainopen.

01ax ACTUAL uniform coupled stripenergy CLOSED:
ChiCubicCoupledStripEnergy284lines/API1,
bagCubicReciprocalKernel_uniform_strip_energy. All0<=s<3/2, ALLrealλ,
allstructuralδ,h; fullactual reciprocal Fourierkernel weightedL2strip
integral admitted anduniformlybounded. Kernelmeasurability fromliteral
integrand, actualcompactdensitymass, existingrealweightedCS andjoint
admission/Fubini via U5 close this. No assumedenergy/variation bound.
Production64537emptyPASS; axiom74320standard3; index55017PASS/API1/importonce;
lint69952eightunrelatedunreachable362warnings,noownederror; diffcheckPASS.
P2/P3 bag-actual-coupled-strip-energy. CurrentoneownedLean92740 tests
/tmp/bag-high-frequency-decay-01ax.lean: actualwindow-attachedallorder
L1budgets andnativephase decay. Highfrequency/globalenergy, log/Mellintails,
movingarithmetictransfer, fullsharpaction/growingmoments/commonheight
remainhardopen. RH remainsopen.

01ax actual ALLORDER kernel frequencydecay CLOSED:
ChiCubicKernelFrequencyDecay315lines/API1,
bagCubicReciprocalKernel_frequency_decay. Everypositivenaturaln has oneCn
uniformallδ,hstructural andALLrealabc:
max(|a|,|b|)^n*normK<=Cn/δ^(n-1). ActualF*W(kx) allorderL1budget,
nativecorpusrepeatedIBP, remainingQ/Ractualmass andexactP/Qsymmetry closeit.
Production55738PASS (oneinformationalring suggestion, noerrors/warnings),
axiom14295standard3,index91438PASS/API1/importonce;lint6955twelveunrelated
unreachable362warnings,noownederror;scoped diffcheckPASS.
P2/P3 bag-actual-kernel-all-order-decay. CurrentoneownedLean93859:
/tmp/bag-kernel-tail-energy-01ax.lean, completecandidate actualtailenergy
integral<=Cs/δ^22*R^(2s-20) onmaxfreq>=R>=1. GlobalactualN-energy,
compactconvergence/log/Mellintails/movingsignedtransfer remainhardopen.

01ax selected GLOBAL actual energy: complete scratch73079emptyPASS;
production13417emptyPASS, ChiCubicSelectedKernelEnergy248lines/API2.
Every0<=s<3/2 andfixedtau>0: literal K_(N^-3/4,1/logN)(a,b,tau*ab/N)
has eventually admitted uniformlybounded full-planeweightedenergy.
Actualtail bound Cs/delta^22*R^(2s-20), exact selectedscale identity and
closed-strip/complement decomposition pay allfrequencies. Index36595PASS,
umbrellaonce; scoped diffcheckPASS. Lint64836terminal1:14 unrelated
unreachable modules, no ownedleaf finding. Axiomprint currently42001.
Active next /tmp/bag-selected-kernel-limit-01ax.lean (same42001): actual
slice norm<=1 and pointwise limit; literal fixedcube dominant and Fubini;
full selectedkernel -> explicit sharp-band zero-curvature kernel.
P1 bag-selected-kernel-convergence records corpus search and paper proof.
Strong lower-order energy convergence, physical log/Mellintails, arithmetic
lowergrowth envelope/movingtransfer, fullsharpaction bridge and commonheight
recurrence remain hard open. RH remains open.

01ax GLOBAL actual energy closure: both axiomprints in42001 standard3;
42001 exited1 only for subsequent convergence candidate elaboration errors.
P2/P3 bag-selected-global-kernel-energy and BAG frontier row now record
production/index/wiring/lint evidence. Global lint has14 unrelated reachability
errors/362warnings, no ownedleaf finding. Finished energy scratch/templates
removed; logs retained. Convergence retry63299 handles exact positivity,
reciprocal limit API, explicit denominator coercions and cube admission.

01ax STRONG actual selected-kernel convergence CLOSED:
ChiCubicSelectedKernelConvergence479lines/API5. Literal family -> explicit
sharp-band reciprocal kernel globally in weightedL2, every0<=s<3/2.
Actual slice/cube domination/Fubini/DCT, intermediate-order Fatou admission,
and R^(2s-2t) tails pay full convergence without assumed regularity.
Scratch23076PASS; production6711emptyPASS; five axiomprints93079standard3
(combined next physical scratch has separate errors). Index88424PASS/API5,
umbrellaonce,diffcheckPASS. Lint94988terminal1: UnitClassInverseLBounds
unreachable outside this work,362warnings,no owned finding. P2/P3 and BAG
frontier updated. Finished convergence scratch/templates removed; logs retained.
Next single owned Lean89579: /tmp/bag-normalized-physical-kernel-01ax.lean,
exact normalized physical phase with prefactorN and reciprocal1/R. First
candidate93079 exposed vector-coordinate reduction, a star/conjugation simp
loop, and real-to-complex product coercion. Corrected without resource hacks.
P1 bag-physical-nonstationary-log-tails records all hard next obligations.
Uncompiled template /tmp/bag-physical-tail-budgets-01ax.txt gives the actual
polynomial-window attached derivative-budget candidate. RH remains open.

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

2026-10-06 01ax actual selected local Mellin energy CLOSED.
ChiCubicSelectedLocalMellinEnergy227/API7: scratch99827/log03PASS/all7standard3;
production78981emptyPASS; imported all7axioms79187standard3; index14164PASS,
RHTower importonce23584/scoped diffcheckPASS. Lint44890terminal1:362warnings,
10 unrelated unreachable, exactnames P2/P3 bag-selected-local-mellin-energy;
noownedfinding/globalnotclean. Literal N^(1/4) family has uniform global
physical H^s energy0<=s<3/2 and actual compact Mellin H^(1+theta) energy
0<theta<1/2, uniformly allsigma in[1,2]^2. Exact2*pi scaling/curvaturetau=1/(2*pi)
and double Jacobian cancellation are proved. Actual physical identity retained.
Next P1 bag-exterior-logarithmic-energy: pure physical jet -> weighted log
mass/second derivatives -> full exterior H^2 energy. RH/endgame remain open.

2026-10-06 01ax actual GLOBAL Mellin energy CLOSED.
ChiCubicExteriorMellinEnergy947/API5: exact actual local+exterior, complete
exterior H^2 energy C/N^(2k) for everyk; full selected H^(1+theta) uniformly
sigma[1,2]^2 for0<theta<1/2. Both log Jacobians, axis endpoints, Euler/cutoff
terms and literal selected family retained. Production99895emptyPASS,all5
importedaxioms37031standard3,index85730PASS,importonce,scopeddiffPASS.
Lint41249terminal1:362warnings/17unrelatedunreachable,noownedfinding;global
notclean. Exact errors P2/P3 bag-exterior-logarithmic-energy. Next arithmetic
source uses saturated pole geometry and actual logarithmic zeta/reciprocal
bounds; transverse trace/tail control still required for movingtests.
See P1 bag-source-saturated-pole-transfer. RH/endgame remain unproved.

2026-10-06 01ax complete SOURCE SUBPOWER ENVELOPE CLOSED.
ChiRamanujanSubpowerSourceEnvelope561/API1: actual original Z_N <=Cepsilon
T^epsilon*(1+both shrinking axis kernels), EVERYepsilon>0. Filled pole and
actual logarithmic zeta/reciprocal control, original signed-shift finiteEuler
comparison and allsixfactor assembly preserve both cofactors/exclusions.
Background1 retained. Production14933emptyPASS,importedaxioms81346standard3,
index87818PASS,importonce23586,scopeddiffPASS. Lint49703global18unrelated
errors/noownedfinding; exact P2/P3 bag-source-saturated-pole-transfer.
Next P1 bag-moving-mellin-trace-transfer: common compact log support gives
Fourier reproduction and weighted pointwise trace from Hs. Exterior can
absorb logarithmic concentration through arbitrary N-saving. Moving signed
transfer/full original sharpaction/RH remain unproved.

2026-10-06 01ax actual Mellin TRACE CLOSED. ChiCubicMellinTrace306/API2:
actualselected weightedpointwise trace foralltheta0,.5,sigma[1,2]^2; exact
difference trace throughs2, including differentparameters, paid byactual
differenceenergy. Commonlogsupport ->fixedcutoff ->Fourierreproduction
->weightedCauchy with allL2admission. Production76357emptyPASS,bothaxioms
43613standard3,index26282PASS,importonce23596,scopeddiffPASS. Lint38906
362warnings14unrelatedfailures/noownedfinding; exact P2/P3bag-actual-mellin-trace.
Full source pairing, exteriorvanishing, actual Cauchy/fixedinputparameter
continuity and moving signed cancellation remain P1bag-moving-mellin-trace-transfer.
Native Mellin sourcefrequencies2*pi*xi retained. RH/endgameopen.

Complete source pairing and actual exterior vanishing CLOSED:
ChiCubicMellinArithmeticPairing674/API5, production93958emptyPASS,
allimportedaxioms43754standard3,index96945PASS,importonce,scopeddiffPASS.
Uniform local-difference operatorH5/4; complete sourceH2 dualcostsqrt(1+logN);
actual exteriorpairing<=C/N andzero for everyq_N. Native2*pi*xi retained.
Lint83875 362warnings19unrelatedunreachable,noownedfinding; exactP2/P3
bag-complete-mellin-pairing. PhysicalHs Cauchy proof now in scratchaudit01;
fixed-input movingparametercontinuity and signed movingtest cancellation open.

ActualphysicalHs Cauchy anduniformlocalinputtransfer CLOSED:
ChiCubicSelectedPhysicalConvergence225/API2, production97119emptyPASS,
bothimportedaxioms73599standard3,index68204PASS,importonce23599,scopeddiffPASS.
Lint93037 362warnings21unrelatedunreachable,noownedfinding; exactP2/P3
bag-actual-physical-cauchy-transfer. Fixed-input movingparametercontinuity
is in scratchaudit28031; signedmovingtest comparison/cancellation remainsopen.

Fixed-input PARAMETER CONTINUITY CLOSED: ChiCubicMellinParameterContinuity
362/API1, production81641emptyPASS, importedaxiom37195standard3,
index80052PASS, importonce23601, scopedcodecheckPASS. Lint30316:
367warnings23unrelatedunreachable,noownedfinding; exactP2/P3
bag-fixed-mellin-parameter-continuity. Common compact joint log jets and
filterDCT prove actual fixed-input Hs parametercontinuity for0<=s<=2.
Complete movingcancellation candidate now325lines in
/tmp/bag-moving-mellin-cancellation-01ax.lean; firstaudit19396 running.
It retains exact2*pi source transport and both Jacobians, eventual literal
critical parameters, fixed-late-test approximation, complete admitted
pairing and actual exterior. No moving cancellation closure claimed yet.

ACTUAL MOVING MELLIN CANCELLATION CLOSED. Production96709emptyPASS,
all3importedaxioms10540standard3,index19630PASS/API3,importonce23615,
scopeddiffPASS. LeafChiCubicMovingMellinCancellation330lines. Lint14752:
367warnings24unrelatedunreachable,noownedfinding; exactP2/P3
bag-moving-mellin-cancellation. Actualcriticalparameters, fixedlatetest
comparison andsignedfixedlaw withBOTH2pi Jacobians pluscompleteexterior
prove fullmovingpair->0. Noanalyticpremises. This closes thisP1subtarget.
NextP1 bag-selected-rational-cone-cancellation andscratch01ay actualcone
normsaving auditstarted. Wholeoriginalsharpaction/globaldefects and RHopen.

SELECTED POSITIVE RATIONAL CONE CANCELLATION CLOSED. Production12330emptyPASS,
all5importedaxioms8568standard3,index21706PASS/API5,importonce23616,
scopedcode/generateddiffPASS. LeafChiCubicSelectedRationalConeCancellation
173lines. Lint70244:367warnings25unrelatedunreachable,noownedfinding;
exactP2/P3 bag-selected-rational-cone-cancellation. Actualadmission+exact
Mellin/scalar identity givesnormaction*log²N/N->0 forsourceP_N/physicalN.
Covered-band source2N/physicalN remainsP1bag-covered-source-mellin-transfer;
itscandidate/tmp/bag-covered-mellin-01ay.lean firstaudit50387running.
Wholeoriginalsharpaction/globaldefects and RHremainopen.

2026-10-06 continuation02ay: covered source2N/physicalN and literal positive
cone CLOSED, ChiCubicCoveredMellinCancellation API4. Production50975 and
imported axioms76729 PASS/allstandard3, index93313 PASS, umbrella once.
Lint76722 has no ownedfinding; global21unreachable+1sorry remain unrelated.
P2/P3bag-covered-source-mellin-transfer retain exact proof/audit. Remaining
hard action is P1bag-covered-global-defect-cancellation: complete signed
global residual, then growing moments/cofactors/commonheightreturn.
