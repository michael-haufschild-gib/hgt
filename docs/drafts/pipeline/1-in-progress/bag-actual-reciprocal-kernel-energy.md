# BAG actual reciprocal kernel energy

01ax. HARD OPEN. This follows the audited exact reciprocal Fourier identity,
curved-strip scalar energy and selected cutoff budgets. Actual Gaussian/log
amplitude all-order L1 budgets are in scratch audit7804, not yet production.

Corpus search /tmp/bag-reciprocal-ibp-search-01ax.json5396: nonpartial,
66676files allindexed, generation1250608=current, noerrors; background
refresh incomplete. All20 candidate+20 source statements inspected.
Relevant existing mechanisms: Real.fourier_deriv (used by
ChenGuptaLiHtFourierDerivative), FiniteRegularityFourierDecay, compact
Fourier support conversion. No exact coupled reciprocal kernel estimate
appeared. Direct source read also found full-line integration by parts in
Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts.

Target: actual normalized reciprocal Fourier kernel
 K(a,b)=2pi integral_RQP F(P)F(Q)conj(F(R))*W(PQ/R)/R²
                         *exp(-2pi*i*(Pb+Qa+lambda*ab)/R),
lambda=1/N, delta=N^-3/4. All full physical factors retained.
Prove uniform weighted L2 energy for every1<s<3/2. No scalar energy
estimate alone closes this actual amplitude theorem.

New paper mechanism: replace separate small-frequency cases by the exact
operators1+partial_P and1+partial_Q. Their denominators are
1+2pi*i*b/R and1+2pi*i*a/R. They cancel the originalR^-2 to give
1/((R+2pi*i*b)*(R+2pi*i*a)). These are nonzero forR in[1,2], including
a=0 or b=0, and their firstR derivatives have the same product decay
C/((1+|a|)*(1+|b|)). The differentiated physical amplitude contains only
(|F|+|F'|)(P)*(|F|+|F'|)(Q), bounded window mixed derivatives, andF(R).

PutD=Pb+Qa+lambda*ab. Since d_R exp(-2pi*i*D/R)=
(2pi*i*D/R²)*exp(-2pi*i*D/R), integration by parts gives
 integral [B-(R²B)']*phase=(1+2pi*i*D)*integral B*phase.
No boundary terms: actual compact smooth amplitude has zero endpoint jets.
The proved uniformR first variation should therefore give
 |K(a,b)| <= C integral_PQ w(P)w(Q)/
       ((1+|a|)*(1+|b|)*(1+|Pb+Qa+lambda*ab|)),
w=|F|+|F'|, uniformly bounded mass and support[1,2].
Weighted Cauchy-Schwarz againstw(P)w(Q), followed by Tonelli and the audited
curved-strip energy, pays the low strip |lambda*a|<=1/4. This avoids needing
an abstract vector-valued Minkowski theorem.

High strip forlambda=1/N: apply tenQ derivatives and twoP derivatives,
withoutR oscillatory gain. Actual amplitude budgets give
 |K| <= C delta^-10 (1+|a|)^-10 (1+|b|)^-2.
Squaring costsdelta^-20=N^15. For|a|>=N/4, weighted integration costs
N^(2s-19) in the a-weight term andN^-19 in the b-weight term. Thus costs
N^(2s-4) andN^-4, bounded and tendingzero for s<3/2. Window derivatives
are bounded on the fixed cube. This deliberately uses a fixed sufficiently
high order; no numerical experiment or sharp-constant optimization.

Formal obligations: exact normalization from the raw audited identity,
full physicalP/Q/R IBP with all admissions and derivatives, positive
majorant/Cauchy-Schwarz/Fubini, high-frequency tail assembly. Then compact
frequency convergence, strong lower-orderH^s convergence, log-coordinate
tails/Mellin line tails, weaker-growth arithmetic envelope and moving signed
transfer. Entire sharp-action bridge, growing moments and common-height
self-return remain open. RH remains open.

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

Height-resolvent checkpoint01ax: mathlib-only scratch96186 passed exact
(1+iD)*I=int phase*(f-deriv(r²f)) and its first norm bound; scratch89947
emptyPASS additionally proves (1+|D|)*|I|<=10*(L1f+L1f') for smooth support
[1,2], and the complex multiplier K_ab(r)=1/((r+ia)(r+ib)) has
(1+|a|)(1+|b|)*|K|<=4 and the corresponding derivative bound<=8 onr>=1.
These are PRIVATE helpers, not a new public premise-based frontier claim.
No resource limits increased. Current scratch85800 adds the actual height
window jets W_j(p,q,r)=W^(j)(pq/r)/r^j. Their joint smoothness near the fixed
cube and compactness should bound |W_j|+|partial_r W_j| uniformly for eachj.

Next actual unconditional target: for allj, oneC_j bounds
(1+|a|)(1+|b|)(1+|D|)*|int_r exp(-iD/r)*conj(F(r))*W_j(p,q,r)*K_ab(r)|
for ALLdelta,h,p,q in their structural domains, and all reala,b,D.
Use the alreadyproved actualF mass/firstvariation. If the window-jet bound
isC, weighted amplitude norms are <=4C|F| and weighted derivative norms
<=12C|F|+4C|F'|. Thus the resolvent bound and mass budgets give a uniform
constant. Global smoothness at r=0 follows from the actual cutoff vanishing
on a neighborhood; no singularity or endpoint premise. Afterward, attach
P/Q resolvents to the exact normalized kernel, weightedCS andU5stripenergy.

Window-jet reduction01ax (paper): letU=F+F'. Exact(1+partialP)(1+partialQ)
applied toF(P)F(Q)W(PQ/R) is
 C0(P,Q)*W_0(P,Q,R)+C1(P,Q)*W_1(P,Q,R)+C2(P,Q)*W_2(P,Q,R),
C0=U(P)U(Q), C1=P*U(P)F(Q)+Q*F(P)U(Q)+F(P)F(Q),
C2=P*Q*F(P)F(Q), W_j=W^(j)(PQ/R)/R^j.
Thus only the three actual height-jet integralsj=0,1,2 are needed.
On[1,2]^2 their coefficient norms are <=w(P)w(Q),5w(P)w(Q),4w(P)w(Q),
respectively, w=|F|+|F'|. The height theorem uses frequencies2pi*a,2pi*b,
defect2pi*(Pb+Qa+lambdaab). Keep bothfactor2pi and positiveR Jacobians.
Prove the two tangential integration-by-parts identities by applying the
single-fibre linear resolvent, swapping admitted compact P/Q integrals,
then applying the other fibre resolvent; no derivative-under-integral
premise is needed. FullR/P/Q Fubini still needs actual compact admission.

Actual height theorem scratch88281 emptyPASS. New production leaf
ChiCubicReciprocalHeightDecay477lines (check actualcount), audit9533 running;
no production/axiom closure yet. Full originalF/W_j/action admitted and
uniform in allstructuralparams, frequencies anddefect. No hypothesis
supplies mass/variation/window/denominator bounds. Tangential/kernelenergy
still open.

Latest search49957 /tmp/bag-weighted-kernel-energy-search-01ax.json:
nonpartial66696files/allindexed,gen1251253=current,noerrors,refreshincomplete;
all20+20 statements inspected. Crucial exact corpus theorem already exists:
GaloisForLFunctions.HTGeometry.lintegral_weighted_sq_le in
HTGeometry/YoungConvolutionL2.lean:29, ANY measurable space and measure,
(∫K*G)^2<=(∫K)*(∫K*G²) inENNReal, no integrability hypotheses. Fullproof
read. Its weightedCS plus Tonelli proof mechanism is directly applicable
to w(P)w(Q) and the curved denominator. Reuse it; do NOT reprove an auxiliary
realvariance/weightedCS theorem. U5 supplies finite fibre energies and the
actualF mass/variation supplies finite densitymass. Original Fourier
Schwartz continuity supplies measurability of the actual normalized profile.

01ax actual reciprocal height decay CLOSED: production9533emptyPASS,
axiom44627all3standard3,index96838PASS/API3/importonce. Lint89133fiveunrelated
unreachable362warnings,noownederror. P2/P3 bag-actual-reciprocal-height-decay
record exact uniform all-jet actual theorem and proof. Tangential attachment,
full kernelenergy and RH remain open. Current single Lean scratch68100:
/tmp/bag-tangential-resolvent-01ax.lean, native single-fibre linear resolvent.

Tangential checkpoint01ax: scratch68300emptyPASS establishes both exact fibre
resolvents and compactP/Q firststage swap; scratch6432emptyPASS establishes
the combined double resolvent (R+ia)(R+ib)*J=R²*T with allthree exact
windowjet coefficients. Scratch8744emptyPASS admits arbitrary continuous
compactphysical coefficient times the ACTUAL heightjet on the fullR/P/Q
product, and proves its full Fubini swap. Admission uses continuity on
[1,2]^3 and literal zero support offcube, with explicit nonzero complex
denominators; no interchange or derivative-under-integral premise.
Current scratch tests actual coefficient admissions and complete fixedheight
attachment. No productiontangential/kernelenergy closure yet.

Energy normalization checkpoint01ax: the native kernel uses A=2pi*a,
B=2pi*b and c=2pi*a*b/N = lambda*A*B with lambda=1/(2pi*N).
Thus the native curved strip |lambda*A|<=1/4 is exactly |a/N|<=1/4;
no curvature factor may be dropped. Native U5 uses u=P,v=Q.
For every structuraldelta,h, densityrho(P,Q)=w(P)w(Q) has finite mass
at most(A0+A1)^2 by the audited actual derivative budgets. WeightedCS
inENNReal, followed by Tonelli on the frequency strip, gives native
weighted energy <= Ckernel^2*Cstrip*(integralrho)^2. Compact support
restrictsP,Q to[1,2]^2, precisely the U5 parameter domain. This is the
next actual energy theorem; it is not yet formalized. The full native
kernel's frequency measurability must be proved from its literal
parameter integrals. Current corpus search /tmp/bag-coupled-kernel-energy-search-01ax.json
seeks those integral-measurability/Tonelli ingredients.

Latest deepsearch1522 completed: /tmp/bag-coupled-kernel-energy-search-01ax.json,
nonpartial66706allindexed, indexgeneration1251916, coverage1251925=current,
noerrors; semanticcoverageunmeasured/reportingbudget, backgroundrefresh
incomplete. All20candidate+20source statements inspected (initial verbose
output truncated, then compact complete statement extraction). It found an
ADDITIONAL exact realweightedCS theorem: HTGeometry.sq_integral_weighted_le,
IntegralCauchySchwarz.lean:89. Fullproof read. For actualcompactdensity,
its weighted-square integrability premise is paid by continuity/support.
This provides a shorter nativeenergy proof than converting pointwise bounds
toENNReal: square actualkernel bound, then admit jointpositive densitytimes
U5kernel using integrable_prod_iff, U5fibreintegrability and uniformbound.
Fubini yields totalenergy; no generalvariance/CS theorem will be reproved.
Next realkernel measurability follows from literal measurable integrands
and three StronglyMeasurable.integral_prod_right applications.

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

Highfrequency paper refinement01ax, grounded in deepsearch12393:
/tmp/bag-high-frequency-derivative-search-01ax.json nonpartial66715allindexed,
indexgeneration1252164coverage1252176=current,noerrors; semanticcoverage
unmeasured/reportingbudget, backgroundrefreshincomplete. All20+20statements
inspected. Exact existing theorem HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv
in FourierIteratedDerivDecay.lean49 pays arbitraryfixed-order native linear
oscillation; entire96line source read. Existing mathlib iteratedDeriv_mul and
iteratedDeriv_comp_const_smul provide the actualwindow-product budget.

A simpler highfrequency mechanism than the earlier10Q/2P expansion:
for eachn, apply the native one-coordinate theorem toF(x)*W(k*x),
|k|<=2. Globalbounded derivatives of the fixedcomplexW plus actualF budgets
and Leibniz give L1 derivative<=C_n/delta^(n-1). Integrating the other
physicalcoordinate andheight uses only actualmass andR in[1,2]. Thus
|b|^n*|K(a,b,c)|<=C_n/delta^(n-1), ALLrealdefectc; atb=0 handle directly.
ExactP/Qsymmetry gives the samea bound, hence max-frequency decay.
Use fixedn=10. Withdelta=N^-3/4, squaredcostN^(27/2); the two-dimensional
weightedtail beyondfrequencycN costsN^(2s-18), leavingN^(2s-9/2), which
tendszero foralls<3/2. No mixedderivative expansion or parameterderivative
of an integral is needed. This is a proposed paper mechanism, not yet a
formal highfrequency theorem. Needactualwindow-attached L1budget,
completeone-coordinate normintegral bounds, exactsymmetry andtailadmission.

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

Highfrequency checkpoint01ax: scratch92740emptyPASS establishes every
actualF(x)*W(kx) derivativeL1<=Cn/δ^(n-1), uniformly|k|<=2, and attaches
the corpus native repeatedIBP theorem. Scratch86421reachedfullsingle-axis
kerneldecay with only scalarpositivity/zero-goal repairs; current86421
has terminated and its replacements are in the nextaudit. ExactP/Q
symmetry and arbitrarypositive-order maxfrequency theorem are now included.

Tailintegration paper variant: no radialchangeofvariables is required.
Use fixedorder12 from the allorderdecay. For M=max(|a|,|b|)>=R>=1,
(1+|a|+|b|)^(2s)*|K|² is bounded by
 C_s*δ^-22*R^(2s-20)/((1+|a|)^2*(1+|b|)^2), 0<=s<3/2.
Indeed(1+|a|+|b|)<=3M and(1+|a|)^2(1+|b|)^2<=16M^4;
M^(2s-20)<=R^(2s-20). The displayed separatedmajorant is integrable on
allR². Atδ=N^-3/4,R=cN its coefficient is a constanttimesN^(2s-7/2),
which tendszero. This sacrifices unuseddecay to reuse a simple global
integrablemajorant; no exact radialtailconstant is needed. Needformal
pointwisecomparison, measurability, admittedtailintegral, selectedN
substitution and then union with the CLOSEDstripenergy theorem.

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

Actualtail scratch49479emptyPASS. The FULLkernelenergy integral over
maxfrequency>=R>=1 is admitted and<=Cs/δ^22*R^(2s-20), allδ,hstructural,
ALLrealλ,0<=s<3/2. Taildensity is the globalintegrable product
1/(1+|a|)^2 *1/(1+|b|)^2. No productiontailleafyet: keep this result
with the immediatelyfollowing selectedscale/globalenergy theorem.
Current combinedscratch adds exactscaleidentity
 δ=N^-3/4,R=N/(4tau): δ^-22*R^(2s-20)
 =(4tau)^(20-2s)*N^(2s-7/2).
For eachfixedpositiveτ,δ/h/Rareeventuallyadmissible. The closedstrip
|τ*a/N|<=1/4 and thetailmaxfreq>=N/(4τ) coverthefrequencyplane.
The lastNpower<=1 eventually, so globalweightedenergy is admitted and
uniformlybounded. Actualnativecurvature correspondsτ=1/(2pi).
Globalassembly is now in scratchaudit, notyetclaimedformal.

Newscale search36988 /tmp/bag-selected-scale-energy-search-01ax.json:
nonpartial66730allindexed,index1252662coverage1252683=current,noerrors,
semanticcoverageunmeasured,backgroundrefreshincomplete; all20+20statements
inspected but mostlyirrelevant. Followed with exactlexicalsearch
/tmp/bag-selected-scale-power-search-01ax.json (12namehits, nofreshness
metadata exposed). Directcurrentcorpus evidence ChiPrimeGaussianCubicSharpEdges
edge_quarter_small uses root tendsto_rpow_neg_atTop andrpow_sub_one;
ChiCubicPhysicalAmplitudeBudgets actualslice theorem constructs h=1/logN
fromN>=exp1 usinglog_le_log. These actualtools supplyselectedadmission.

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
