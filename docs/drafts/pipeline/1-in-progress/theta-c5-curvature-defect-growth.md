# TH: C5 growth from the completed curvature defect

Status: new source conjecture; not a C5 or RH proof.
Working log: route-th-source-sign-working-log.md.

## Checked starting point

`ThetaCuspCurvatureDefectSource` proves H=L5-4L3>0 on x>0.
`ThetaCuspCurvatureProjectiveGlobal` proves b=c''-4c>0 on x>=0,
b'=-H<0, c'c''-cc'''>0, and negative completed C5 center numerator
on 0<t<=u. Here c=-L2 and Lj=(log theta source)^(j).
All final leaf audits pass with only standard Lean axioms.
The nonlocal completed compensation sign remains open.

## New conjecture

Let q=pi exp(2x)-3/2, A=q+3/2, and S(q) be the exact complete
cumulant cooling functional in ThetaCuspCurvatureDefectCumulants.
Conjecture on the actual source half-line:

    T(q)=(q+9) S(q)-A q S'(q) >= 0.

This is a coupled seventh-order source sign, not separate absolute
bounds on source jets. Search of the current corpus located the exact
seventh/eighth cumulant derivative chain and the C5 seam orientation
receiver, but no producer for T. Search generation1181122 was partial;
all proposed applications still require Lean verification.

## Why this sign attacks C5

The checked source identity is H(x)=F(q(x)) (1-R(x)), where

    F(q)=864 A^2(q+3)/q^5,
    R'(x)=-P(q) S(q), P(q)=2 A q^4/[27(q+3)^2].

With f1=F_x'/F=4+2A/(q+3)-10A/q, direct differentiation gives

    R''+2 f1 R'=(2P/q) T.

Thus T>=0 would imply H''<=(F_x''/F) H. Also H'>f1 H
already follows from R'<0 and F>0. These comparisons preserve the
modular cancellation H(0)=0.

The exact C5 seam polynomial in c and its derivatives becomes

    Omega = c'*(72c^3+36c^2 b+12c b+4b^2)
          + H*(18c^3+4c^2+2c b) +3c c' H' -c^2 H''.

Consequently T and a positive source lower reserve
18c+4+2b/c+3(c'/c)f1-F_x''/F would force Omega>0.
This reserve is NOT proved. One possible structural input is c'/c<2;
that comparison also remains unproved here and must not be assumed.
Even Omega>0 supplies only a source-dependent neighborhood of t=0
via eventually_c5CompletedCompensationMargin_pos_of_exactSeamOrientation.
A full displacement argument and arbitrary-packet positivity remain needed.

## First proof experiment

The ordinary-moment T functional has coefficients
D_j=(q+9)C_j-A q C_j'+A q C_(j-1), j=2,...,7,
where C_j are the existing cooling coefficients. Literal point-and-ray
integration gives a finite denominator-cleared polynomial.
Scratch /tmp/th_defect_growth_kernel.lean contains that exact polynomial.
First ring_nf exceeded default recursion depth; no mathematical failure
was established. Retrying raw normalization with no raised limits.
No source T sign or nonlinear absorption is claimed.

## Kernel progress and nonlinear seam obstruction

The ordinary point-and-ray polynomial sign now passes Lean with default
resources. Initial failures came from unreduced coefficient cases during
normalization. Full numeral reduction before ring normalization closes
positivity directly. New GrowthKernel leaf is written and wired; its final
leaf audit is pending. No computation or external algebra engine supplied
the certificate.

A necessary seam constraint emerged from the proposed comparison:
H(0)=H''(0)=0 by the corpus's odd-jet vanishing. Therefore the exact
identity R''+2f1 R'=(2P/q)T forces T(kappa)(q(0))=0.
This deduction still needs its own Lean derivative bridge, but rules out
any proposed strictly positive uniform cumulant absorption at the center.
The ordinary kernel alone cannot supply that missing sign.

Equivalent next producer: V(q)=A^5 S(kappa)/q^6 has
V'(q)=-A^4 T(kappa)/q^7. Prove V strictly decreases to the right of its
modular stationary value. A candidate finite-grade strategy writes
T(kappa)=T(e)-N, normalizes N by the positive ordinary contribution,
uses the exact seam value N/T(e)=1, and proves that ratio decreases via
coupled additive spectral gaps. The signs and monotonicity of this
normalized nonlinear correction are conjectures, not checked results.

GrowthKernel final leaf audit passed with exit0 and empty log. The new
ordinary full-measure transport is prepared in
/tmp/th_defect_growth_transport.lean and currently under audit.
Implementation note: existing likelihoodCumulant is deliberately truncated
after order6. Do NOT use it unchanged in growthFunctional: the new source
T requires the actual seventh cumulant. Add a separate seven-jet readout
using thetaCuspLikelihoodSeventhCumulant and its checked derivative chain;
do not accidentally prove a truncated false target.

Complete ordinary transport now checks: full_growthFunctional_pos holds
for every q>=3/2, via literal moment identity and HasSum over all theta
components. Scratch audit exits0; axiom audit reports only the standard3.
GrowthMoments is saved/wired; final leaf audit pending. The actual source
bridge through L7-4L5 is prepared in /tmp/th_defect_growth_seam.lean;
it explicitly uses the seventh cumulant, and remains untested.

The actual seventh-jet identity and exact modular-center cancellation now
PASS Lean in the combined scratch audit. source_growth_eq identifies
J-beta*H=-128*A^3/[q^2(q+3)]*sourceGrowth(q), J=L7-4L5.
sourceGrowth_coordinate_zero proves sourceGrowth(q(0))=0 by continuity
and odd-jet vanishing. Both axiom audits report only the standard3.
GrowthSource is saved/wired; final leaf audit pending.
GrowthMoments final leaf audit also passed (exit0, empty log).
The exact ordinary positive producer and exact nonlinear seam cancellation
are now available together; the positive-half-line cumulant sign is open.

## Next conjecture stated without an assumed correction sign

Let P=1+M0, To=T(M)/P (>0 by the checked full ordinary theorem),
Tk=sourceGrowth, and N=To-Tk. Prove strict decrease of N/To on the
actual coordinate ray q>=q(0). The checked seam Tk(q(0))=0 gives
N/To=1 there, so strict decrease would force Tk>0 for x>0.
This candidate does not assume N>=0 or any conjectural cumulant sign.
Its derivative must be proved from the literal theta moment/cumulant
chain, retaining the order8 term. A finite-grade expansion and coupled
additive spectral gaps are the proposed mechanism; support positivity
alone does not upper-bound the ordinary logarithmic decay rate.
Recent deep search generation1181331 completed but returned no applicable
global normalized-correction producer. Existing regime-I cumulant bounds
require scale>=6 and do not discharge the compact source interval.

2026-10-02 final audit: GrowthSource leaf exits0 with empty log.
All three Growth leaves are finally audited and wired. Ordinary positivity,
exact seventh-jet source identity, and modular-center cancellation are
formalized; the normalized nonlinear-correction monotonicity and Tk>0
for x>0 remain conjectural. No C5 compensation or RH proof is asserted.

Formal scope: GrowthSource checks the identity with the explicitly defined
rational factorCurvature. The interpretations T=(q+9)S-AqS' and
factorCurvature=F_x''/F above are paper differentiations; separate Lean
HasDerivAt bridges for those interpretations have not yet been published.
The checked source identity and seam zero do not depend on assuming them.

2026-10-02 continuation: current source files revalidated; search1181415
partial finds the new growth definitions but no normalized nonlinear sign.
First new sign experiment targets the literal binary grade against the
n=2 ordinary contribution. For unnormalized atom moment sequences m,n and
anchor a (gap3), put B=T(binaryMoment(m,n)); let dots denote their literal
q-derivatives, retaining moments through8. Test

    B*dot(T(a))-dot(B)*T(a)-B*T(a)>0

for every pair of point-and-ray gaps d,e>=3 and q>=3/2. If true, this is
a strict one-unit relative cooling reserve for the binary numerator against
the dominant literal component. Full denominator-tail correction and higher
cumulant grades remain mandatory. The test is a symbolic Lean polynomial
proof attempt in /tmp/th_growth_binary_anchor.lean, not a numerical sample.
The new coefficient derivative formula is derived from the explicit C_j;
its separate derivative bridge will be audited before source transport.

Binary-anchor experiment update: the first direct expansion exposed a Lean
sum-binder scope error, then hit the default heartbeat limit during repeated
rational denominator clearing. Correcting binder scope and using homogeneous
polynomial moment numerators removed the denominator bottleneck; the unsplit
Wronskian expansion still exceeded the default limit. These are proof-engineering
failures, not counterexamples. No resource limits were raised.

The denominator-free certificate uses
U_j(q,d)=q^(j+1) bareMoment(q,d,j), B_9=q^9 binaryGrowth,
Bdot_10=q^10 binaryGrowthSlope, A_8=q^8 growth(anchor), and
Adot_9=q^9 growthSlope(anchor). The exact candidate numerator is
B_9 Adot_9-Bdot_10 A_8-q B_9 A_8. The next proof splits these four
polynomials before attempting their Wronskian. Source transport is still pending.

Proposed complete-source differential continuation (not yet a theorem): let a
be the positive exact n=2 ordinary growth contribution and set
Gamma=a'/a-1/2. Prove Tk'-Gamma Tk>0 on the actual coordinate ray. For the
negative binary grade, the proposed one-unit anchor reserve would leave a
positive margin after the normalization derivative 2*mean is included.
The linear n>=3 remainder and differentiated grades3..7 must be controlled
from the literal theta weights. The exact Tk(q(0))=0 would then propagate
strict positivity without presupposing its sign. Existing StrictCooling gives
an exact modular bound for the mean; EighthFockSector and
EighthStablePairCompensation supply literal dominant/tail mechanisms, but
none of those existing statements proves this new differential inequality.
Search1181531 was partial, with complete source inventory but extensive
pending/stale compiler metadata; candidates were checked against source.

Further paper simplification: every growth coefficient D_j has the common
factor q+3. After dividing it out, with A=q+3/2, coefficients j2..7 are
540; 180(q^2-6A); 150A(3A-2q^2); 45A^2(3q^2-A);
-21q^2 A^3; q^2 A^4. This exact factorization was derived algebraically;
a separate Lean identity is pending. It suggests testing the stronger
point-spectrum binary Wronskian before integrating the full rays:
B(q,d,e)=sum D_j((d+e)^j-d^j-e^j), J=sum D_j' times the same cross powers.
For the literal n=2 anchor a(q), test
B*a' + (d+e-1)*B*a - J*a > 0 (d,e>=3).
Here a' includes its exp(-3q) factor, while B and J omit the two-point
exponential. This is precisely the same one-unit relative cooling target.
If true pointwise, it would integrate against the full spectral measure and
avoid a separate giant ray-by-ray certificate. This stronger conjecture is
prepared in /tmp/th_growth_anchor_point.lean, not yet run.

The exact self-pair numerator proof is currently being repaired at tactic
level: norm_num rewrites 0<X-Y into Y<X, so final positivity needs
`apply sub_pos.mp` before ring normalization. The prior 'not a positivity
goal' message was not a negative polynomial certificate or a counterexample.

MATHEMATICAL FAILURE FOUND in the strengthened one-unit target on q>=3/2:
the Lean-normalized exact self-pair numerator, at q=3/2+y, begins with
-6479264583807358963727295/524288
- (227143192854317004658861497/2097152)y
- (213366667935019863092309667/1048576)y^2,
followed by positive coefficients from degree3 onward. Thus the proposed
strictly positive polynomial cannot hold at y=0. This is an exact symbolic
obstruction, not a numerical sample. A closed Lean negative theorem remains
to be extracted from the checked ring normalization. It only refutes the
stronger q>=3/2 criterion; no failure on the actual q>=pi-3/2 ray has yet
been proved, and no source-growth or RH falsification follows.

Positive survivor / next producer: remove the arbitrary fixed one-unit rate
and prove B*a'-B'*a>0, first for the exact dominant self-pair. This is strict
cooling of its ratio to the literal dominant ordinary growth contribution.
Scratch /tmp/th_growth_anchor_self_cooling.lean is auditing that polynomial.
For the full-source proof use Gamma=a'/a, and absorb the higher one-particle
components by the positive binary derivative: the literal next gap is8 while
the dominant binary gap is6. Differentiated higher Bell grades begin atgap9.
This preserves the source-specific arithmetic separation, rather than trying
to force a uniform one-unit comparison throughout an enlarged domain.
The previous Gamma=a'/a-1/2 sufficient-criterion plan is superseded.

POSITIVE SURVIVOR CHECKED: anchorCoolingNumerator_self_pos proves the
exact dominant self-pair relative-cooling numerator positive for all q>=3/2.
The same new BinaryGrowthKernel leaf proves
anchorUnitReserve_threeHalves_neg, closing the negative certificate for the
failed enlarged-domain one-unit target. Final leaf audit exits0 with empty
log; leaf is wired without an umbrella build. No resource limits were raised.
Axiom audit and transport into the actual moment expression are next.
The scalar coefficient factorization passes its algebraic checks. Its
HasDerivAt bridge has only tactic simplification repairs pending, now included
in /tmp/th_growth_binary_cooling.lean together with exact polynomial/ordinary
moment denominator transport. No complete-source Tk sign is asserted.

Actual-moment transport now PASSES in scratch, together with the exact
coefficient HasDerivAt bridge. source_dominant_selfGrowthCooling_pos gives
strict positivity for the literal second theta component at every x>=0.
Kernel negative and positive certificates, actual-moment endpoint, and
coefficient derivative axiom audits show only propext, Classical.choice,
Quot.sound. BinaryGrowthCooling is saved; its final leaf audit is running.

Next hard conjecture: let a be the n=2 ordinary growth contribution and
R(q,t)=sum D_j(q)t^j. The differential comparison kernel is
K(q,t)=a'(q)R(q,t)+t*a(q)R(q,t)-a(q)*partial_q R(q,t).
Its a-normalized integral is the negative derivative of a spectral growth
ratio. Test K>0 for t>=6, q>=3/2, with a kept as the literal atom-and-ray
anchor. The t>=6 domain covers every spectral convolution of order>=2.
An exact denominator-cleared test, with separately checked anchor polynomial
identities, is prepared in /tmp/th_growth_fock_transfer_kernel.lean.
If this holds, the complete logarithmic expansion has positive even-sector
contributions and negative odd-sector losses; the hard comparison is the
gap6 dominant binary term against gap8 single-tail and gap9 higher sectors.
No all-sector expansion or absorption for this new kernel is yet proved.
Search1181879 was partial and did not provide this new growth-kernel producer.

The stronger pointwise t>=6 target fails at q=3/2,t=6: after reducing the
rawCast constants before ring normalization, the exact shifted polynomial
has constant -3098715321673852875/512. Its polynomial identities check;
a closed negative theorem is now being audited. This enlarged-domain
failure does not falsify the source-growth target. The positive survivor
already proved is the integrated literal n=2 self-pair expression.

Next pointwise conjecture starts at t>=8, the exact n=3 spectral gap.
The dominant n=2 self-pair is kept coupled; all other binary theta pairs
start atgap11 and every order>=3 convolution starts atgap9. Therefore t>=8
covers every remaining sector required by the proposed full-source
comparison. This uses the discrete theta gap structure. The same scratch
now tests that exact complementary-domain claim; its sign is not assumed.

NEW STABLE KERNEL SIGN PASSES: growthTransferKernel_pos proves the exact
cleared comparison polynomial positive for every q>=3/2 and t>=8. Lean's
216 positive normalized monomials are grouped into7 bounded proof blocks;
no heartbeat/recursion limit was raised. The closed theorem
growthTransferKernel_threeHalves_six_neg proves the t6 counterexample.
Both endpoint axiom audits report only propext/Classical.choice/Quot.sound.
GrowthTransferKernel leaf is saved; its final leaf audit is running.

Positive survivor now has two complementary pieces: the literal dominant
self-pair moment expression is positive, and the stable pointwise transfer
kernel is positive from the actual next spectral gap8. These are new checked
sign ingredients. The full signed-sector comparison remains a hard open
mathematical problem. In particular, neither a full Fock expansion for this
operator nor domination of the gap8 single tail and higher odd sectors by
the gap6 binary contribution has been proved. Existing eighth Bell/Fock
modules are source ingredients; their old bounds are not new-operator gates.

The canonical full-pair identity now passes Lean:
fullPairGrowthCooling=selfGrowthCooling+2*m1*T^2.
Its actual n=2 source specialization is strictly positive, and its axiom
audit has only the standard3. The initial unfold-order failure is repaired;
no failed declaration was published. These declarations are appended to
BinaryGrowthCooling and that updated leaf is being re-audited.

Next analytic transport /tmp/th_growth_flow.lean is prepared from the corpus
full spectral-moment differentiation proof. A single atom is dominated by
the full positive spectral measure, so its tilted moments also differentiate
to minus their successors. The intended endpoint is strict decrease of the
literal full-pair growth / dominant single-growth ratio on q>=3/2. This
will formalize the analytic interpretation of the checked moment-chain
inequality, not assume it as a source premise. No flow audit has run yet.

## Finite convolution decomposition conjecture

Corpus search1182187 (partial; complete source inventory, compiler coverage
mostly pending/stale) returned no applicable finite inversion producer.
The existing explicit cumulants through8 and momentConvolution motivate
the following exact replacement for infinite Fock resummation.

Let F be the exponential moment series of the normalized positive tail,
p=F(0), and N=8. The degree<=8 nonconstant jet of log(1+F-p) equals
sum(l=1..8) (-1)^(l-1) w_l(p) F^l, where
w_l(p)=sum(k=l..8) choose(k,l)*p^(k-l)/k.
Paper proof: expand sum(k=1..8) (-1)^(k-1)(F-p)^k/k by the
binomial theorem. Terms k>8 have vanishing jets through8 because F-p
has zero constant term. The collected sign is (-1)^(l-1), since
(-1)^(k-1)(-1)^(k-l)=(-1)^(l-1). The l=0 term is constant and
is annihilated by the transfer functional (orders2..8).

All w_l are nonnegative for p>=0. Applied to the new transfer kernel,
even sectors4,6,8 can be dropped from a lower bound; the coupled dominant
sector2 must dominate stable sector1 and odd sectors3,5,7. This exact
finite decomposition is NOT YET FORMALIZED. It avoids assuming an
infinite logarithmic expansion and retains the actual zero-mass terms.
The remaining hard issue is still the signed sector comparison, not
the formal expansion alone.

BinaryGrowthFlow final audit now exits0; its literal ratio is strictly
antitone on q>=3/2, with standard3 axioms only.

Finite-log scratch proves the rebase identity, positive weights, and the
coefficient-level alternating decomposition. Identification with source
cumulants2..8 is in progress. An automatic nested-sum simplification
exhausted default simp steps; the proof now expands one finite power at
a time and normalizes the concrete coefficient indices before continuing.
No resource limit is raised.

Next operator-specific conjecture, based on the explicit transfer kernel
and the corpus eighth-moment transports:
K(q,t) <= q*D7(q)*growthNumerator(q,3)*t^8 for q>=3/2,t>=8.
This compares the entire new operator to its exact highest monomial. It
would make existing convolution eighth-moment estimates applicable to
the remaining negative sectors; it is not yet proved. Search1182247 was
partial with pending coverage and returned the current K sign and old
moment transports, no applicable new-operator envelope. The direct
symbolic polynomial test is prepared in /tmp/th_growth_transfer_envelope.lean.

Exact signed comparison exposed by the finite decomposition (paper target):
write nu for the unnormalized tail measure, M=nu(R), P=1+M, r=1/P,
and J_k=integral K against nu^{*k}. The dominant single contribution to
J_1 is exactly zero by anchor calibration. The dominant self-pair
contribution J_2,dom is positive; other pairs and every k>=3 sector are
supported in K's positive domain. The finite-weight remainder identities
give w_k(p)*r^k <= 840/k, p=1-r, and w_2(p)*r^2 >= 420*r^2.
Consequently the sufficient comparison is
  (r^2/2)*J_2,dom > J_1,stable + J_3/3 + J_5/5 + J_7/7.
This keeps the actual dominant cancellation and leaves no infinite sector
tail. If the proposed exact monomial envelope holds, the corpus moment
product inequality gives J_k <= C(q)*k^8*M^(k-1)*m8 for odd k>=3.
The envelope and this complete signed comparison remain UNPROVED. No
positive-source theorem follows merely from the finite identity.

FINITE DECOMPOSITION FINAL LEAF AUDIT PASSES: new
ThetaCuspCurvatureDefectFiniteLogConvolution.lean identifies every actual
cumulant2..8 with the finite logarithmic jet, proves the full-power moment
convolution recurrence, and gives the exact eight-sector decomposition of
growthTransferFunctional. The positive weight and normalized-weight
remainder identities also pass. Saved and wired; final command
`lake --old env lean -o ...FiniteLogConvolution.olean ...FiniteLogConvolution.lean`
exits0 with empty log. No heartbeat or recursion limits were raised.
The final source axiom audit is in the next scratch together with the
actual sourceRelativeGrowth derivative identity and the operator envelope
conjecture. The complete signed comparison remains open.

The exact monomial envelope scratch theorem now passes on q>=3/2,t>=8:
K(q,t)<=q*D7(q)*growthNumerator(q,3)*t^8. Its shifted polynomial has a
direct positivity proof at default resources. A combined scratch also
audits the actual source ratio derivative; two local proof errors in
that derivative bridge are being repaired. The envelope is independent
of those failed declarations; its explicit axiom audit is pending.
The finite source decomposition endpoint already prints standard3 only.

Next coupled comparison is against the explicit dominant-pair numerator
P2(q)=anchorCoolingNumerator(q,3,3)+2*polynomialMoment(q,3,1)*N(q)^2,
where N(q)=growthNumerator(q,3). The canonical pair integral of K is
P2(q)/q^9 before multiplying by the square of its actual atom scale.
This follows from the checked full-pair cooling decomposition; the
remaining convolution successor identity and exact K transport must be
audited. The mass-times-eighth-moment comparison is a candidate way to
pay the finite odd-sector losses; no such absorption is yet proved.

GrowthTransferEnvelope and GrowthTransferFlow now both pass their final
leaf commands with empty logs and are wired. The core derivative,
finite source decomposition, and shifted kernel-envelope axioms are
standard3 only. Public envelope includes positivity of its exact leading
coefficient. Latest index exits0. Latest lint exits1 for12 unrelated
unreachable umbrella modules, with no finding in these TH leaves.

NEXT ACTUAL-SECTOR TRANSPORT: /tmp/th_growth_convolution_transport.lean is
under first audit. It proves all-power integrability under finite measure
convolution, the binomial moment formula, and additive lower support.
Then define nu_k recursively by nu_0=dirac0,
nu_(k+1)=thetaCuspHigherLikelihoodTiltedMeasure(q)*nu_k. Inductively prove
finite mass, all moments integrable, support>=3k, and for j<=8 the exact
identity integral(t^j)dnu_k=spectralPowerMoment(actualMoments,k,j).
The kernel is a finite polynomial, so its integral equals
growthTransferFunctional(q,spectralPowerMoment(actualMoments,k)).
For k>=3, the checked pointwise sign/envelope then yield
0<=J_k<=C(q)*spectralPowerMoment(actualMoments,k,8).
This closes the even-sector sign and odd-sector transport; the separate
dominant-pair-versus-loss comparison must still be proved.

Actual measure ingredients: SpectralMeasure.lean450/454 defines the tilt
and proves every power integrable; CassiniMarkovBoundaryTransport.lean362
proves finite mass and402 gives support>=3. Mathlib Group/Convolution
provides finite convolution and bilinearity; Group/IntegralConvolution
provides integral_conv. Search1184834 was partial, compiler metadata mostly
pending/stale. Names in the scratch are checked with @Name probes.

### Complete transfer absorption continuation (2026-10-02)

The actual k-fold source convolution has support >=3k. The current scratch
`/tmp/th_growth_convolution_transport.lean` transports its moments through
order8, K integrability, and K bounds to the finite source decomposition.
Generic integral transport passed except two elaboration/association repairs;
current retry includes them. No failed endpoint is accepted.

Corpus-grounded next conjecture: the full dominant pair polynomial
P2=anchorCoolingNumerator(q,3,3)+2*polynomialMoment(q,3,1)*N(q)^2
has a reserve against D7(q)*N(q)*P0(q)*P8(q) sufficient to absorb the
finite odd losses. Test the explicit factor16 on q>=3/2 as a sufficient
statement, not an optimized constant. This is motivated by the exact
convolution estimate Jk<=C*k^8*M0^(k-1)*M8 and existing actual activity
399*M0<1. A failure of polynomial positivity alone does not falsify it.
The exact coordinate-dependent P2 remains the primary comparison if the
uniform reserve fails. Stable single-tail absorption is still separate.
No complete transfer sign, sourceGrowth sign, C5 compensation, or RH claimed.

New structural conjecture from the exact source supports (not a numerical
fit): write P2 for the full dominant pair polynomial and
Q=q^10*D7(q)*N(q). Then its K/C ratio is
`dominantAtomScale(q)^2*P2(q)/Q(q)`.
If `(P2'+2*P2)*Q-P2*Q'>0` on the actual source ray, this ratio cools
strictly slower than rate8. The stable D8 satisfies D8'+8D8<=0 by support8;
M0^(k-1)*M8 cools at least rate3k by support3. Division of the pair by P^2
helps since P'<0. Thus the precise residual
`dominantPairK/(2*P^2*C)-D8-(3^7*M0^2+5^7*M0^4+7^7*M0^6)*M8`
would inherit global positivity from a center comparison. Both the pair
rational derivative sign and the center residual comparison are open.
This is a mechanism to prove the required full sign, not an assumed bound
or a claim that finite-degree positivity gives RH.

### Pair rate-eight polynomial certificate

The cached shifted forms satisfy
`(P'(y)+2P(y))*Q(y)-P(y)*Q'(y)>0` for every `y>=0`.
The scratch endpoint's axiom audit is standard3. The actual shifted
identities P(y)=P2(3/2+y) and Q(y)=(3/2+y)^10 D7 N also audit standard3.
Two redundant trailing ring commands caused file errors and are removed.
The current retry adds the actual source transport:
`(dominantPairTransfer/C)' + 8*(dominantPairTransfer/C)>0` and strict
increase after multiplication by exp(8q). Accept that endpoint only after
its own successful audit. No center residual positivity follows yet.
The optimization uses cached exact coefficient identities and a generic
finite-polynomial derivative lemma, with unchanged default limits.

### Pair comparison closed; center-residual obstruction test

Saved and wired `ThetaCuspCurvatureDefectGrowthPairRelativeCooling`.
Required final leaf audit exits0, empty log at
`/tmp/th-growth-pair-relative-cooling-final.log`. The source ratio
`dominantPairTransfer/C` satisfies `R'+8R>0` on q>=3/2, hence exp(8q)R
strictly increases. Scratch axiom endpoints were standard3; a saved-import
recheck is included in the next residual-monotonicity audit.

The next exact theorem combines this pair comparison with support-gap
cooling and decreasing partition: exp(8q)*transferAbsorptionResidual/C
strictly increases. Current scratch `/tmp/th_growth_residual_monotonicity.lean`.
This alone does not give the center sign. The source-based obstruction test
retains only the literal second atom in the cubic loss at q=5/3. If even
that loss exceeds the pair reserve, monotonicity transports a strict
negative residual to the actual center q0=pi-3/2<5/3. This would falsify
only the coarse eighth-moment absorption strategy, not sourceGrowth, C5,
or RH. The test uses exact rational polynomial identities and analytic
exponential inequalities, no numerical evaluation. It is not accepted
until Lean checks both the algebraic sign and actual source transport.
Fresh searches1185507/1185585 were partial with pending/stale compiler
metadata; actual source formulas inspected. Modular eighth center jets
remain another exact diagnostic for the genuine growth sign.

### Actual-center coarse-residual no-go (2026-10-02)

All three new leaves are saved, wired, and final-audited with exit0 and
empty logs: GrowthPairRelativeCooling, GrowthResidualMonotonicity,
GrowthResidualCenterObstruction. The last proves
`transferAbsorptionResidual (thetaCuspLikelihoodCoordinate 0)<0`.
The pair inequality and weighted residual monotonicity are positive
survivors; see 5-failed/theta-growth-coarse-eighth-absorption.md for the
exact obstruction and dependency-closed paper proof. This falsifies only
the coarse eighth-moment sufficient comparison, not sourceGrowth or RH.

Next attack restores the literal cubic kernel cancellation: three copies
of the point-and-ray measure have an exact finite gamma-mixture moment
numerator. Test the degree-eight pair comparison on that numerator, then
transport it to the actual source and bound only mixed deep-tail errors.
Scratch /tmp/th_growth_exact_cubic.lean; no new sign accepted before audit.
Corpus1185664 complete search supplied current convolution/source formulas;
compiler metadata still requires individual Lean audits.

### Exact dominant cubic repaired (2026-10-02)

`ThetaCuspCurvatureDefectGrowthDominantCubic` saved/wired; required final
leaf audit exit0, empty `/tmp/th-growth-dominant-cubic-final.log`.
`dominantCubic_transfer_le_pair` proves actual J3<=2^8*a0*J2 for q>=3/2.
`dominantCubic_weighted_lt_quarter_pair` proves w3*J3<J2/4 at every actual
source x>=0 using 399*M0<1. Exact finite gamma-mixture moments through8,
source rational transfer, and positive shifted-polynomial reserve all
have standard3 scratch axiom audits. The saved center obstruction was
also re-audited through its compiled import: standard3.

The first combined cubic sign attempt hit default200000 heartbeat at
ring_nf. Splitting out the already established pair polynomial identity
fixed it without increasing limits. Two redundant rings and one unfolded
convolution identity were the only remaining source-transport repairs.
No mathematical failure of the exact cubic comparison occurred.

Next exact decomposition: full k-fold tilted source equals its dominant
power plus a positive mixed remainder E_k, recursively
E_(k+1)=(A+D)*E_k+D*A^k. Its support is at least 3k+5. Hence
0<=Jk(full)-Jk(dom)<=C*(M8(full^k)-M8(dom^k)). For k=3 the support gap is14;
only this mixed difference will receive a monomial bound. Current scratch
/tmp/th_growth_mixed_convolution.lean. This is unverified until exit0.
Deep single-tail absorption and sectors5,7 still open; sourceGrowth,C5,RH
not proved. Index passed; latest lint has10 unrelated unreachable modules,
none ours, recorded /tmp/th-growth-pair-residual-lint-final.log.

### Exact mixed-tail isolation and repaired residual (2026-10-02)

`ThetaCuspCurvatureDefectGrowthCubicTailIsolation` saved/wired; final leaf
`lake --old env lean -o ... <leaf.lean>` audit exit0, empty log
`/tmp/th-growth-cubic-tail-isolation-final.log`.
For every k>=1, full k-fold transfer minus dominant k-fold transfer lies
between zero and C times the difference of their eighth moments. The
positive remainder measure has support>=3k+5. The repaired residual is

`R3=[1/(2P^2)-(256/3)a0]*J2-C*[D8+E3_8/3+(5^7M0^4+7^7M0^6)M8]`.

The complete source transfer is <=-R3; the bracket is strictly positive
on every actual x>=0. Its full sign remains OPEN. Generic/source mixed
transfer and repaired-residual scratch axioms are standard3; saved-import
axiom audit (including the newly added bracket positivity theorem) is
included in the next scratch run. Source assembly needed normalization
of inverse products in the pair denominator, not a mathematical repair.

Next conjecture attacks the remaining mixed cubic loss directly:
`E3_8 <=384*[D8*M0^2+256*D0*M0*M8]`. Every term keeps a deep factor and
cools at least at rate14. Paper mechanism: E3<=three copies of
D*(full*full) as positive measures; integrate the even-power two-summand
inequality twice. No numerical evaluation or all-moment sign premise.
Scratch /tmp/th_growth_mixed_eighth_budget.lean is auditing this exact
inequality, together with saved-import axioms. Center and complete R3
positivity, genuine sourceGrowth sign, C5 compensation and RH remain open.

### Mixed eighth budget proved; next stable-kernel conjecture

Scratch generic and actual-source endpoints now pass with standard3:
`mixedPowerMoment_three_eight_budget` proves
E3_8<=384*(D8*M0^2+256*D0*M0*M8). Saved as
ThetaCuspCurvatureDefectGrowthMixedEighthBudget, wired in RHTower.
Final leaf audit is running, sole owned Lean session83782, log
/tmp/th-growth-mixed-eighth-budget-final.log. No source sign is accepted
from the budget alone. Earlier CubicTailIsolation saved-import residual
and positive pair coefficient axioms are standard3.

Next corpus-grounded conjecture: K(q,t)<=C(q)*t^7*(t-3) on q>=3/2,t>=8.
It retains the literal dominant spectral edge3 instead of replacing the
kernel by its leading monomial. Existing exact dominant transfer=0 and
pointwise kernel polynomial motivate this structural cancellation. If
proved, the deep loss becomes D8-3D7, retaining rate8 through the support
identity t^7*(t-3)*(t-8)>=0. This is not yet proved. Scratch
/tmp/th_growth_root_three_envelope.lean prepared but NOT run. Corpus
search1186003 partial, source formulas verified; no numerical fitting.
The repaired complete residual's center and global signs remain hard
open problems, followed by C5 compensation and arbitrary-packet positivity.

GrowthMixedEighthBudget final leaf audit exits0, empty log. All six new
leaves are now saved/wired/final-audited. Root-three envelope scratch is
now the sole owned Lean audit, /tmp/th-growth-root-three-envelope-audit.log;
it also rechecks the mixed eighth-budget axiom endpoint from its saved import.
No root-three sign accepted before its result. Mixed budget and positive
pair coefficient do not by themselves establish complete residual positivity.

### Root-three envelope complete (2026-10-02)

GrowthRootThreeEnvelope final leaf audit passed; saved-import axioms for
pointwise envelope, literal deep bound and weighted antitonicity are
[propext, Classical.choice, Quot.sound]. The stable loss is D8-3D7, with
8(D8-3D7)<=D9-3D8 from a single nonnegative integrand retaining both
spectral edges. Complete residual sign remains open. Latest formal lint
reports10 unrelated unreachable modules, none of this route's new leaves;
/tmp/th-growth-root-three-lint-final.log records them.

Direct center attack now tests the exact even modular mass jets through10
from PolynomialODEJetOddRankThreeClosure. Their source/Bell transform
would give d-(4+beta)c*f0+4beta*b*f0^2, the normalized numerator of the
required negative log-jet combination. No sign or actual-source transport
is accepted from the symbolic polynomial scratch until Lean verifies it.
Working scratch /tmp/th_growth_center_modular_sign.lean.

### Actual modular-center growth sign (2026-10-02)

GrowthCenterModularPolynomial, GrowthCenterJetElimination and
GrowthCenterModularJets saved/wired; all three final leaf audits exit0,
empty logs. Scratch endpoints standard3. Exact source/Bell transport gives
-L8(0)+(4+beta)L6(0)-4beta L4(0)>0 for beta=factorCurvature(q0).
Proof uses exact even ODE jets through10, X>=191/10 and beta>=200.
The positive polynomial retains the coupled sixth-jet correction; the
separate eighth-minus-sixth term was not used as a positivity premise.
This is a direct literal-source center theorem, not a sufficient residual
estimate. Derivative identification and near-center sourceGrowth
positivity are being checked in /tmp/th_growth_center_source_transfer.lean.
Global sourceGrowth, C5 compensation and RH remain open.

GrowthCenterSourceTransfer final leaf audit0, empty log. Its endpoints
sourceCenter_growthSlope_pos, sourceCenter_growthTransfer_neg and
sourceGrowth_coordinate_eventually_pos have standard3 dependencies.
The actual source-growth center gap is closed. Next hard alternatives:
exclude a downward zero crossing using the exact cumulant-chain boundary
inequality, or prove stable-kernel/pair Wronskian comparison with signed
sector control. Neither global condition is assumed or proved yet.

### Exact third-atom relative cooling (2026-10-02)

GrowthAtomPairCooling saved/wired; final leaf lake --old env lean -o
audit0, empty /tmp/th-growth-atom-pair-cooling-final.log. The exact
literal n=3 transfer divided by dominantPairTransfer is strictly
decreasing on q>=3/2, standard3 dependencies. This preserves the whole
point-and-ray atom. GrowthTransferKernelDerivative and the P' extension
to GrowthPairRelativeCooling also final-audited. Index0; lint1 with10
unrelated unreachable modules, no new TH leaf violations.

Continuing all-gap attack: A(q,8+v)=sum A_k(q)v^k, k=0..9. The exact
coefficient expansion and intermediate polynomial normal forms are
being checked in /tmp/th_growth_atom_gap_coefficients.lean. The stronger
coefficientwise ratio cooling is still a conjecture. Full signed-sector
assembly, global sourceGrowth, C5 and RH remain open.

### All deep atoms and complete infinite tail closed (2026-10-02)

PROGRESS: GrowthAtomGapPolynomial and GrowthAtomGapCooling saved/wired;
both final leaf lake --old env lean -o audits exit0, empty logs. Exact
U(q,d)>0 for every q>=3/2,d>=8 yields atomTransfer_relative_strictAntiOn
for all literal n>=3. hasSum_atomTransfer_deep and strict sum comparison
give deepTransfer_relative_strictAntiOn for the complete infinite deep
tail, retaining exact transfers. Scratch endpoints standard3 only.
No source-global sign, C5, arbitrary-packet result or RH proof claimed.

Final index0 /tmp/th-growth-atom-gap-index-final.log. Lint1 reports12
unrelated unreachable modules, none these new leaves; details in
/tmp/th-growth-atom-gap-lint-final.log. No active proof holes, new axioms,
unsafe/native_decide, or raised resource options in owned modules.
All owned Lean/search/index/lint handles terminal. Completed coefficient
probes, text generator, coefficient JSON and source transport scratches
removed; audit logs/corpus snapshots retained. No commits or umbrella
builds. Goal remains active.

Next hard producer: positivity of complete polynomial Psi transfer after
normalizing original complete transfer by its dominant self-pair.
Dominant single and self-pair cancel; deep single and pure dominant cubic
are the prospective reserve against adverse even sectors. Exact finite
weight differentiation appears to contribute the favorable term
8!*C*mean^9. These new source-sign/cancellation statements still require
Lean proofs and signed-sector absorption; see working-log paper algebra
and memory rh/route-th-pair-normalized-transfer-frontier-2026-10-02.

### Exact normalization derivative cancellation (2026-10-02)

GrowthWeightDerivative saved/wired, final leaf lake --old env lean -o
exit0 (empty log), scratch endpoint axioms standard3 only. The entire
alternating sum of finite sector-weight derivatives times raw transfers
is exactly -40320*C(q)*mean(q)^9, strictly negative on q>=3/2. The proof
retains all eight weights and uses the eighth centered moment series:
all lower moments vanish, so only its leading transfer coefficient survives.
This closes the normalization-derivative sign in the next transfer.
Complete signed Psi positivity and global source-growth propagation are
still open. Testing positivity of Psi above the cubic threshold9 before
assembling mixed-pair and higher-even-sector absorption. Global lint1 has
11 unrelated umbrella omissions, none this leaf.

### Positive next kernel on every higher-sector support (2026-10-02)

GrowthNextKernelPolynomial and GrowthNextKernel saved/wired, final leaf
lake --old env lean -o audits both0; endpoint axioms standard3. Exact
Psi=((q*(t-6)-9)K-q*Kq)P+q*K*P' is strictly positive for all q>=3/2,t>=9.
Nine source coefficient identities and derivative uniqueness connect all
ten strictly positive shifted coefficients to the actual transfer kernel.
No full cumulant sign follows yet. Next source transport/flow scratch is
being checked; hard remaining producer is mixed pair and higher even-sector
absorption against exact deep/cubic positive terms. Working log records
the coupled literal mixed-pair conjecture q*V<=256*polynomialMoment(q,3,0)*U.

### Exact complete pair-relative source flow (2026-10-02)

GrowthNextConvolution and GrowthNextSourceFlow saved/wired and final
lake --old env lean -o audits0, empty logs; endpoints standard3. Actual
source convolution sectors k>=3 are nonnegative for the next functional.
The complete original transfer divided by its literal dominant pair obeys
(T/J2)'=-E/(q*P*J2), E=alternating eight normalized weights times next
source sectors +40320*q*P*C*mean^9. All factors in the denominator are
positive on q>=3/2. Exact E>0 remains open; this is now the precise source
propagation target. Mixed pair and even4,6,8 terms require absorption.
Working log records a concrete retention plan using existing399*M0<1
and D0(19/20)<=1/1000000, with explicit component comparisons still to
prove. New all-order bare normalized moment ordering passed scratch;
its actual deep/source product transport is being audited, not yet claimed.

### All-order actual deep/source moment dominance (2026-10-02)

GrowthDeepMomentOrdering saved/wired; final direct leaf audit0, empty log,
with reduced GrowthStableComponents import. All endpoints standard3 in
scratch. Normalized literal atom moments increase with spectral gap for
every moment order, by an exact positive-tail decomposition and mass-gap
identity. Countable source transport plus deep positive-measure Chebyshev
gives D_i*M_j<=M0*D_(i+j) for all i,j and q>0. This removes the separate
D0*M_j loss from future mixed-sector convolution budgets. Global E>0,
sourceGrowth, C5 compensation and arbitrary-packet positivity remain open.
Next: formalize the marked-deep convolution budget and test exact mixed-pair,
pure-quartic, deep/cubic reserve and leading-monomial comparisons recorded
in the working log. No bound is assumed. Pending mixed-pair probe remains
/tmp/th_growth_next_mixed_pair_probe.lean, not run yet.

Final checkpoint: all six new leaves pass final direct lake --old env lean
-o audits; all endpoints standard3. Index0 refreshed generated formal
indexes. Final lint1 reports13 unrelated unreachable modules, none owned
(/tmp/th-growth-next-transfer-lint-final.log). All owned handles terminal;
no live Lean/search jobs. Completed scratches/generators removed, pending
mixed-pair probe retained and marked unrun. This turn PROGRESS: exact next
source flow and stable kernel signs, plus all-order D_i*M_j<=M0*D_(i+j).
Hard signed absorption/global growth/C5/all-degree gaps remain; RH goal
active and unachieved. Next exact proof plan stored in working log and
Serena rh/route-th-pair-relative-absorption-plan-2026-10-02.
