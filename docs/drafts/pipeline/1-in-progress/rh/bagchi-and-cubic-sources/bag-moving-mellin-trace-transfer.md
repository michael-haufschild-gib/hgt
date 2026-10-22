# BAG actual moving Mellin trace transfer

2026-10-06,01ax. Hard target: signed cancellation against the literal selected
moving Mellin test; do not replace it by a stationary profile or a presumed
uniform Schwartz seminorm. Global actual H^(1+theta) energy is closed for
0<theta<1/2; exterior H2 has arbitrary N-saving (ExteriorMellinEnergy).
Complete arithmetic subpower envelope passed scratch22146/log04 standard3,
production14933 is running. Fixed Schwartz signed source transfer is closed.
Full sharp-action bridge, growing moments/cofactors/common-height and RH open.

New proof route: exploit compact log SUPPORT, not just energy. A fixed smooth
compact log cutoff b is one on the common support of every localized profile
F_N. Hence its Fourier test G_N satisfies the exact reproducing identity
G_N=(Fourier b)*G_N. The planar weight w(x)=1+|x0|+|x1| is submultiplicative.
Cauchy-Schwarz gives w(x)^s|G_N(x)| <= ||w^s Fourier b||2 ||w^s G_N||2.
The same estimate holds for differences of localized profiles, since the
common support is fixed. This gives actual uniform weighted POINTWISE
control with every1<s<3/2 from the proved Hs energy, including axis traces.
No claim that energy alone bounds unrestricted frequency traces.

For source/L, with L=logN, the two axes terms have bounded one-dimensional
transverse mass. Choosing0<epsilon<s-1, the weighted pointwise estimate
makes each remaining one-dimensional frequency tail integrable and uniformly
small; use a positive power of w to remove the region w>R. Background1/L
is handled separately by weighted L2 Cauchy-Schwarz in dimension2, since
s>1+epsilon. The exterior does NOT need a uniform trace estimate: weighted
L2 norm of source/L is O(sqrt L), and the actual exterior has arbitrary
N-power saving. This should make its full source pairing vanish directly.

The compact local family must be Cauchy in Hs along actual sigma_N->(1,1).
Existing selected reciprocal kernels converge strongly in weightedL2 for
s<3/2; exact frequency scaling and local bounded operator transfer handle
fixed sigma. Moving sigma can be controlled by the actual compact multiplier
exp((sigma-sigma0) dot u) on the common log support, with operator continuity
proved from joint compact smoothness/weighted convolution. Once Cauchy is
proved, compare the moving test with one fixed sufficiently late Schwartz
profile; apply actual fixed-test cancellation and the uniform pairing bound.
This avoids an unproved stationary limit identification or Schwartz-limit
claim. Every error must be admitted before the comparison.

Corpus search /tmp/bag-moving-mellin-trace-search-01ax.json: partial at
query decomposition deadline;66858/66858 indexed, noinventoryerrors,
index1257167,coverage1257161/current1257168,compilerpending/stale,
semanticunmeasured,backgroundrefreshincomplete. All20 candidate and source
statements and ingredient proposals inspected. No returned proposal proved
the needed trace theorem; old order76 seminorm bound is insufficient here.
Native source inspected: Mathlib.Analysis.Fourier.Convolution160,174 gives
Schwartz Fourier convolution and its actual integral; Schwartz Fourier
inversion; native Bochner/MeanInequalities Cauchy-Schwarz and Schwartz
polynomial-moment integrability. No generic helper is accepted as an actual
family budget without constructing the cutoff/support and applying it.

Next formalization: exact reproduction and weighted Cauchy estimate; actual
common log cutoff and selected localized trace. Then admitted full-source
pairing/tails, exterior decay, and actual moving-family Cauchy transfer.
No new trace/cancellation theorem is claimed yet.

2026-10-06 01ax source envelope now CLOSED: production14933emptyPASS,
public imported axiom81346standard3,index87818PASS/API1,importonce23586,
scopeddiffPASS. Lint49703:362warnings18unrelatedunreachable, noownedfinding;
exact P2/P3 bag-source-saturated-pole-transfer. Completed source scratch
and templates cleaned, all logs retained.

Current scratch /tmp/bag-compact-mellin-trace-01ax.lean. First audit4092/log01
terminal1: FourierPair needed explicit target type, fourierEquiv_apply before
rewrite, native absolute triangle name is abs_add_le. Fixed and appended
actual polynomial-weight square integrability/MemLp for Schwartz inputs.
Audit02 running. Weighted common-support reproduction, Cauchy pointwise
bound and attachment to the actual localized family still unproved.

Audit59509/log03 terminal1 only two positivity failures where the private
weight definition hid positivity. Exact Fourier reproduction and polynomial
weighted Schwartz L2 admission now print standard3. Cauchy/Tonelli/Haar
part elaborates aside from those two pointwise nonnegativity facts; supplied
explicit weight_pos/rpow_nonneg proofs. Appended actual common log cutoff,
physical support ->logBox, exact localized reproduction and PUBLIC actual
selected trace theorem. Audit04 running. Do not claim trace closure yet.

Paper refinement: a uniform complete-source pairing bound on differences
is enough; separate frequency-tail convergence need not be a standalone
assumption. Reproduction gives pointwise w^s decay; each normalized axes
kernel has bounded transverse mass and integrates w^(epsilon-s) along the
other variable whenepsilon<s-1. Background1/L pairs by weightedL2 in2D.
Thus|int Z_N G/L|<=C sqrt(E_s G) for every difference of compact local
profiles, uniformlyN, with all admission derived. Exterior uses the weighted
L2 dual source costO(sqrt(1+L)) and its actualN-power decay.

Avoid demanding operator-norm continuity in the moving Mellin parameter.
For a fixed late physical Schwartz input f_M, write
local(q_N,f_N)-local(q0,f_M)=local(q_N,f_N-f_M)
 +[local(q_N,f_M)-local(q0,f_M)]. The first term is small by the EXISTING
parameter-uniform local operator bound and actual physical Hs Cauchy law.
The second only needs continuity for the FIXED f_M. Its compact log support,
exact Euler derivatives and joint smooth compact coefficients permit DCT
for mass and both pure second log derivatives, hence H2 convergence and
lowerHs convergence. Constants may depend on that fixed M; noN-uniform
high Schwartz budget is used. Compare the full moving test with the one
fixed Schwartz test Fourier(local(q0,f_M)); actual fixed-test signed source
transfer pays it. This removes the need to identify a nonsmooth stationary
limit or construct a Schwartz limit. These are proof obligations, not yet
formalized cancellation claims.

Audit78938/log04 terminal0PASS: weighted reproducing Cauchy bound and PUBLIC
actual selected uniform local Mellin trace print standard3. Created candidate
production ChiCubicMellinTrace with this theorem plus the exact two-profile
difference trace (including different q,r). Production01 now running; no
umbrella import or production closure yet. Remaining actual transfer follows
the fixed-late-input decomposition above, not an assumed stationary limit.

Native normalization check: PositiveQuadrantMellinLines192 defines Mellin
profile literally as Fourier(logSchwartz); its line187 is sigma+2*pi*i*xi.
The full source pairing must therefore use Z_N at frequencies2*pi*xi,
not silently xi. Existing subpower envelope transfers since2*pi>=1:
w(2*pi*xi)<=2*pi*w(xi), and each shrinking-axis denominator only increases.
The fixed-test signed law on real frequency pairs needs BOTH 2*pi dilation
Jacobians and Euclidean/product coordinate transport. Retain these exactly.
Lexical pairing search01 returned one envelope hit, no coverage/freshness
metadata. SignedSourceTransfer74–145/416–425 inspected: actual source
measurability derives from finite labelled products and complete cofactor
series; pairing integrability is derived from its admitted scalar majorant.
No measurability or source/test admission premise is needed.

Actual TRACE SUBTARGET CLOSED: ChiCubicMellinTrace306/API2. Production76357
emptyPASS,bothimportedaxioms43613standard3,index26282PASS,importonce23596,
scopeddiffPASS. Lint38906:362warnings14unrelatedunreachable,noownedfinding.
Exact proof/audit P2/P3 bag-actual-mellin-trace. Overall moving-test transfer
remains ACTIVE. Next /tmp/bag-mellin-pairing-01ax.lean: full source operator
bound on differences and exterior vanishing; first scalar weight audit01
running. No pairing/cancellation closure yet.

Pairing loop 01–05: planar reciprocal weight p>2 proved in audit43726/log01,
standard3. Building exact scaled-axis mass, Euclidean/product transport,
background weighted Holder and full admitted envelope operator. AxisKernel
mass now checked; current errors are elaboration only (coordinate transport,
rpow direction, imported public name collision, add-order API). No failure
of the mathematical pairing conjecture observed. Source attachment will use
literal2*pi*xi and derive measurability from the complete cofactor series.
Lexical corpus search02 (integral/scale/axis/kernel/Mellin/pairing/Sobolev/trace,
Chi filter) returned20 old axis/scaling and unrelated hits; names/docs inspected,
no new uniform difference operator. No freshness/coverage metadata in lexical
output. Current scratch/tmp/bag-mellin-pairing-01ax.lean audit05 running.

Exterior paper refinement: write k_L(t)=L/(1+L|t|)^2. Then0<=k_L<=L,
k_L²<=L*k_L and(1+k0+k1)²<=3(1+k0²+k1²). Multiplying the source
subpower envelope by w^-2 yields squared weightw^-15/4. This is integrable
in2D and is bounded by(1+|otheraxis|)^-9/8 for each axis term. Exact scaled
kernel mass therefore gives squared H^-2 source cost<=C(1+L), retaining
background and both axes. Weighted Holder2 pairs every Schwartz exterior;
actual exteriorH2N-saving pays sqrt(1+logN). No exterior trace hypothesis.
Template /tmp/bag-mellin-pairing-dual-01ax.txt records the scalar proof candidate;
not yet Lean checked. Audit06 still owns the foreground pairing process.

Pairing audit73591/log09 terminal0: all FOUR public theorem proofs print
standard3, including uniform localized-difference pairing, complete sourceH2
operator cost, actual exteriorO(1/N) admission/decay and its explicit zero
limit for EVERY parameter sequence in[1,2]^2. No new analytic hypotheses.
Scratch warning was one unnecessary sequence-focus tactic; removed in new
production candidate ChiCubicMellinArithmeticPairing674lines/API5 (source
function plus4theorems). Production01 now running, no umbrella closure yet.
This pays the COMPLETE original source at native2*pi*xi, retaining cofactors,
exclusions/collision, background and both shrinking axes. Moving local signed
cancellation is still unproved and is the next direct mathematical target.

Next physical Cauchy refinement: use the proved actual reciprocal strong
weightedL2 limit only as a common center, without claiming a Schwartz limit.
Exact Fourier normalization is kappa=2*pi times reciprocal kernel at the
scaled frequency pair. The squared amplitude kappa² cancels BOTH dilation
Jacobians. Weight grows under kappa>=1. Pointwise squared difference of two
actual profiles is bounded by twice each error to the common sharp reciprocal
kernel. Existing admitted error integrals tend to zero. This gives actual
physicalHs Cauchy for every0<=s<3/2, then the existing parameter-uniform local
Mellin operator pays local(q_N,f_N-f_M). Fixed-input q_N->q0 continuity remains
separate; no uniformN high Schwartz seminorm will be assumed.

Search /tmp/bag-mellin-cauchy-research-01ax.json partial(decomposition worker
disconnected).66882/66882 indexed,noinventoryerrors,index1257571,
coverage1257561/current1257573; compilerpending/stale,semanticunmeasured,
backgroundrefreshincomplete. All20candidate/source statements and ingredient
proposal read. Mostly unrelated gauge/spectral statements; no paid moving
Mellin continuity. Exact actual reciprocal convergence401, physical Fourier44,
selection142/165 and uniform local operator607 source inspected.

Complete PAIRING/EXTERIOR SUBTARGET CLOSED. Production93958emptyPASS,
allfiveimportedaxioms43754standard3,index96945PASS/API5,importonce23598,
scopeddiffPASS. Lint83875:362warnings19unrelatedunreachable,noownedfinding;
exact P2/P3 bag-complete-mellin-pairing. Newleaf674lines. Completed scratch
sources/templates cleaned, logs/searchJSON retained. Current physical Cauchy
scratch/tmp/bag-physical-cauchy-01ax.lean firstaudit01 now running, before any
production physical convergence claim.

Fixed-input parameter continuity can avoid uniform operator-norm estimates
and explicit second Euler coefficient expansion. Define the literal JOINT
log profile F(q,u)=exp(-q0*u0-q1*u1)*chi(logNodeu)*f(logNodeu), for fixedf.
It is jointly smooth for unrestrictedq and has the SAME compact log support
for ALLq. Every pure log directional jet is a total joint directional jet
in direction(0,e_i); native tsupport_fderiv_apply_subset preserves that
support. Joint continuity bounds each jet on compact[1,2]^2 timeslogBox.
DCT for differences atq->q0 gives mass and both pure second jetL2 convergence.
Exact Fourier/Plancherel fourth-energy bound then givesH2 and lowerHs
continuity. NoN-uniform seminorm premise and no Schwartz-limit identity.
Native theorem names/source inspected, new Lean proof still required.
Lexical parameter search01 returned20 mostlyunrelated Schwartz functional
hits plus multiplication/translation exploration, no required slice continuity.
No freshness/coverage metadata. Native DCTfilter67, fderivsupport385,
actual logNode smooth proof and exterior fourth_energy_bound source inspected.

PhysicalCauchy scratch71682/log02 terminal0, bothpublics standard3. First
scratchfailure was ONLY higher-order inference of the curried dilation
integrand; explicitfunctionargument fixed it. Production97119emptyPASS:
ChiCubicSelectedPhysicalConvergence225/API2, public167/200, index68204PASS,
RHTimportonce23599,scopeddiffPASS. Importedaxiom73599 andlint93037 running.
ActualphysicalHs Cauchy anduniformlocalinputtransfer mathematically paid;
parametercontinuity andsignedmovingtest comparison stillopen.

Prepared /tmp/bag-mellin-parameter-continuity-01ax.lean341lines, NOT audited:
exactjointProfile, ContDiff, common logBox support, jointpurejets/support,
compactparameterL2filterDCT, exactidentification withSchwartzaxisJet,
allfixedinputjetL2continuity, imported-source FourierH2masscomparison,
publicbagLocalizedMellin_parameter_energy_tendsto for0<=s<=2. It derives
continuity fromactualfixedinput, without ananalyticpremise. Consumed template
/tmp/bag-mellin-parameter-energy-01ax.txt retaineduntilclosure. Firstaudit
mustwaitforownedphysicalaxiom73599terminal. No parameterproductionleaf.

Laterfixedsourcecoordinate transport: actual fixedtest signedlaw is onRxR
atfrequenciest. PullbacktestPhi(t)=G(toLp![t0/kappa,t1/kappa]) isSchwartz
usingPiLp.continuousLinearEquiv thenContinuousLinearEquiv.finTwoArrow and
unitscaling. Haar integral_comp_smul inreal dimension2 giveskappa^-2,
withkappa=2*pi, plusmeasurepreservingE/productcoords. Do notomit either
Jacobian. Lexicalsearches/tmp/bag-mellin-fixed-source-transport-search-01ax.json
and02ax.json returned0(ANDfinTwoArrow Schwartz/fullcamelname); nativeexact
APIsreadandmustbeauditedbeforeproduction. NoactualfixedlawEtransportproofyet.

Actual PHYSICAL/UNIFORM LOCAL CAUCHY SUBTARGET CLOSED. Both importedaxioms
73599standard3,index68204PASS/API2,importonce23599,scopeddiffPASS; production
97119emptyPASS. Lint93037:362warnings21unrelatedunreachable,noownedfinding;
exactP2/P3 bag-actual-physical-cauchy-transfer. Completedphysicalscratchsources
andtemplatescleaned,logs/searchJSONretained. Fixed-input parametercontinuity
firstaudit28031/log01 is nowrunning; source/tmp/bag-mellin-parameter-continuity-01ax.lean.
No parametercontinuity orsignedmovingtestclosure yet.

Parameteraudit28031/log01terminal1: joint smooth proof needed explicit
Complex.ofRealCLM composition; constant inpointwise DCTlimitneededtype;
slice fderivcompositionneededexplicitFunction.comp; firstinductionbranch
layoutneededblock; ENNRealofRealTendstorequiredcomp_apply/instancealignment;
ENNRealzerolowerboundusesbot_le. These are elaboration errors, no failure of
the continuity conjecture. Fixed; audit02 nowrunning. Compactdomination,
jet support andfourth-energy comparison otherwiseelaborated.
Prepared /tmp/bag-moving-mellin-cancellation-01ax.lean (~70lines) for the
EXACT fixed-sourceEtransport with bothJacobianfactors andadmission, NOTyet
audited. It imports onlyclosedPairing+PhysicalConvergence, andhasprivate
fixed_source_pairing_tendsto via literal signedfixedtestlaw. Noactualmoving
cancellationproofyet. Do notrunthis untilownedparameteraudit02terminal.

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

Movingcancellation audit19396/log01 terminal1: explicit coordsLinear.map_smul
needed to avoid rewriting outer Schwartz function; Tendsto composition
needed instance alignment/comp_apply; lintegral_ofReal_ne_top_iff_integrable
is in MeasureTheory, not ENNReal (section is not namespace). Remaining
candidate, including final signed comparison and exterior assembly, elaborated
modulo these errors. Corrected before second audit; no closure claim yet.

Movingcancellation audit7627/log02 terminal1: fixed_source_pairing_tendsto,
criticalMellinParameter_tendsto,movingEnergy_real_bound all standard3.
Only hp composed parameterlimit conversion failed. Audit44030/log03
reduced this to equality of a lambda and its explicit composition after
normalizing the exponent; added rfl. Audit35446/log04 nowrunning.
No mathematical obstruction found; no production closure claimed.

Nextsourceattachment cardP1 bag-selected-rational-cone-cancellation written.
Candidate/tmp/bag-selected-cone-cancellation-01ay.lean prepared (unaudited,
waits for movingcancellation production). Exact originalphysical amplitude,
admission/fullpositive rationalcone HasSum, literal Mellin normalization,
complex norm o(N/log²N). Corpus confirms rationalcone notthewhole original
sharp cubic action; additive labels/projectors/off-cone modes must be kept.
Search01ay partialdeadline,generation1257935,coveragepending; all20candidate
and20source statements inspected. Lexicalaxessearch01ay238matches,
20+5names/docs inspected, nofreshnessmetadata. Actualsource definitions
and scope read. No fullsharpaction or RH claim.

Movingcancellation scratch35446/log04 TERMINAL0. Final fullselectedmoving
Mellinpair cancellation and allfour audited private supports use only
propext, Classical.choice, Quot.sound. No warnings. Filterconversion
remaininglambda/compositiongoal closed by rfl after exponentnormalization.
Productionleaf ChiCubicMovingMellinCancellation created from that exact
scratchbody (prints removed, moduleheader added). Productionaudit next.
This is actual movingprofile cancellation, not fullsharpaction/RH.

Production96709/log01 terminal0emptyPASS. Newleaf330lines/API3public92/121/292.
RHTimportonce23615; index19630terminal0/API3; scopedcode/generateddiffPASS.
Importedaxiom10540 stillrunning. Lint14752terminal1; full errors in
/tmp/bag-moving-mellin-lint-01ay.log, all unrelated unreachable. Noowned
finding; global lint NOT clean. P2/P3 finalrecords awaitimportedaxiom.
Nextliteralcone candidate is161lines and hasnotyetbeenaudited.

ACTUAL MOVING MELLIN CANCELLATION CLOSED. Production96709emptyPASS,
all3importedaxioms10540standard3,index19630PASS/API3,importonce23615,
scopeddiffPASS. LeafChiCubicMovingMellinCancellation330lines. Lint14752:
367warnings24unrelatedunreachable,noownedfinding; exactP2/P3
bag-moving-mellin-cancellation. Actualcriticalparameters, fixedlatetest
comparison andsignedfixedlaw withBOTH2pi Jacobians pluscompleteexterior
prove fullmovingpair->0. Noanalyticpremises. This closes thisP1subtarget.
NextP1 bag-selected-rational-cone-cancellation andscratch01ay actualcone
normsaving auditstarted. Wholeoriginalsharpaction/globaldefects and RHopen.
