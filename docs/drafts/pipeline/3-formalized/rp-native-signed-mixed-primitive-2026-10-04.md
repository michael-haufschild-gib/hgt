# RP69–RP71: signed complete mixed primitive

- **Stage:** 3-formalized
- **Type:** THEOREM, cofinal subcritical exponential escape
- **Route:** RP
- **Source:** RP68 exact mixed-admission classification;
  CriticalPrimeTailSource; CriticalLogProfilePrimitive;
  RoutePSourcePoleResidue and ShiftedAnalyticRigidity.

## Resolution at RP71

For every0<epsilon<1/2, b<1/2-epsilon, and real C,A, there is a physical
clock t>A with |Q(t)|>C*exp(b*t). This stronger positive survivor is
formalized by NativeMixedLaplace.nativeMixedPrimitive_exponential_escape
in RoutePNativeMixedGrowthBarrier. Its final foreground audit55535
exited0. Four new native leaves are wired; all removal jumps, the finite
source head, initial boundary, and actual decaying correction are retained.
The argument discharges the proposed growth bound by the source Hardy
barrier for every negative abscissa. The earlier conjecture and mechanism
entries below are a chronological record, superseded by this resolution.

The bounded separate signed-payment mechanism fails; its failure and
positive survivor are recorded in
../5-failed/rp-separate-signed-mixed-payment-2026-10-04.md.
Positive-damping native energy, signed high-LCM payment and both physical
history debts remain open. RH is neither proved nor falsified.
Separate axiom audit78542 exited0: all14 audited public theorems
(13 new and the retained fixed-width specialization) use only propext,
Classical.choice and Quot.sound. Global lint44744 reports12 unrelated
unreachable modules and no error in the four new leaves.

## Hard target and conjecture

The final open obligations remain absolute native energy at every positive
damping, signed high-LCM payment, and both physical history debts.
RP68 tests separate absolute mixed-work payment. This follow-up tests
whether retaining only the sign of that mixed work is enough.

For 0<epsilon<1/2 set delta=1/2-epsilon, h=native critical profile,
J=complete late-prime increment, and

    D(t)=exp(delta*t)*h(t)*J(t),
    Q(T)=integral_0^T D(t) dt.

Conjecture: Q is not bounded on any late ray. This is stronger than
absolute nonintegrability; RP68 alone does not prove it. No claim of
one-sided escape or two-sided sign oscillation is made yet.

## Proposed arithmetic variation mechanism

The exact finite sum is

    J(t)=sum_p 1_(log p<=t<2 log p)*a(t-log p)/p.

At t=log p the new atom is zero because a(0)=0. At t=2 log p the atom
is removed, producing jump -a(log p)/p. Between these removal clocks its
derivative is the corresponding sum of v(t-log p)/p. Thus for every
eta>0 and nonnegative integer k the exponentially weighted total
variation should be finite:

    integral exp(-eta*t)*(1+t^k) d|dJ|(t) < infinity.

For the absolutely continuous contribution, interchange the nonnegative
finite-prime terms and use sum_p p^(-1-eta)*(1+(log p)^k)<infinity and
integrability of v against a bounded polynomial-exponential weight.
For jumps, use bounded a and sum_p p^(-1-2eta)*(1+(log p)^k)<infinity.
All prime atoms and the removal boundary are retained.

The established second-order asymptotic t^2*J(t)->-D0/3, D0>0, makes J
bounded away from zero by a multiple of t^-2 on a late ray. Hence the
same exponentially weighted variation admission holds for 1/J (with
four extra polynomial powers). This needs a literal BV chain/product
proof, including jumps and one-sided limits.

## Proposed residue contradiction from a bounded primitive

Assume Q bounded and choose a late T where J is nonzero. For Re z>-delta,

    w_z(t)=exp(-(z+delta)*t)/J(t)

decays to zero and has finite total variation. Integration by parts
against dQ=D(t)dt gives a continued transform of h as a compact head,
a boundary term, and -integral Q dw_z. Fixing b=-delta/2 rewrites

    dw_z=exp(-(z-b)*t) dw_b
         -(z-b)*exp(-(z-b)*t)*w_b(t)dt.

Both resulting measures have finite variation if Q is bounded. Their
Laplace transforms are analytic for Re z>b. Far to the right this agrees
with the literal native transform. The exponentially decaying native/
Route-P correction transfers the continuation to the source. Analytic
rigidity and the existing Hardy-zero nonzero residue then contradict
holomorphy at the critical boundary.

This is a proof plan, not a completed paper proof or Lean theorem.
Outstanding: actual BV construction and weighted variation, reciprocal
chain rule across jumps, Stieltjes integration by parts and analytic
continuation identification. General receiver hypotheses must all be
discharged for the native carrier before any no-go claim. No numerical
experiments or new axioms.

## Corpus and dependency audit so far

The deep signed-primitive/Laplace/variation search completed without
partial stages or errors, inventory65168 with zero pending files,
generation=current1222219. Relevant hits were source-only. Candidate,
source, idea and ingredient fields were read; none supplied the native
conclusion. BurnolFirstWallSourceDecay supplies a concrete bounded
periodic primitive and finite-window integration by parts. It also
illustrates why absolute nonintegrability alone is insufficient.
Mathlib supplies Stieltjes measures for monotone right-continuous
functions and BV decomposition; the needed native signed measure and
integration-by-parts weld have not yet been built.

An alternative implementation may use the exact half-open integer-cell
identity criticalMovingPrimeHead_cell. It retains the prime-square
jumps, and on each cell the normalized J is a linear combination of
exp(-t) and exp(-3t/2). This permits finite-cell integration by parts and
an explicit jump sum rather than assuming smoothness across removals.

Positive survivor to seek with the obstruction: an exact transform
representation retaining the jump measure. The paper mechanism also
suggests that an eventual bound |Q(t)|<=C*exp(b*t), b<delta, is impossible.
That stronger growth statement is a new conjecture, not yet proved.

## Literal velocity and jump measure: implementation target

Use velocity atoms

    v_p(s)=1_(log p<s<=2 log p)*v(s-log p)/p,
    V(s)=sum_(p<=exp s) v_p(s).

The endpoint convention is an a.e. derivative representative, not the
right derivative at removal points. The jump measure is kept separately.
For every t>=0 the exact identity to formalize is

    J(t)=integral_0^t V(s)ds
         -sum_(p<=exp(t/2)) a(log p)/p.

Paper proof: freeze primes at exp t; each velocity atom integrates to
a(min(t-log p,log p))/p. Split these primes according to t/2<log p.
The uncapped terms give J and the capped terms give the displayed jump
sum. The physical cutoff and each removal are retained.

For every eta>0, the integral of exp(-eta*s)*|v_p(s)| is at most
p^(-1-eta)*integral_0^infinity |v(u)|du, by u=s-log p. Summing finite
families and using the admitted inverse-power series gives global
weighted velocity admission. The removed masses have weighted absolute
sum bounded by sup|a| times sum_p p^(-1-2eta). Polynomial weights are
absorbed by a smaller positive exponential rate. These measure-admission
claims have complete paper proofs; native reciprocal/primitive closure
still awaits construction. No derivative at an omitted jump is assumed.

## RP69 formalization checkpoint

`RoutePLatePrimeIncrementJumps.lean` passed its foreground leaf audit with
`lake --old env lean ... -o ...` (session86235, exit0). It proves the exact
velocity-minus-removals identity, measurable velocity and finite-window
admission. Its umbrella import is wired; no umbrella build was run.
Axiom audit is recorded below with the variation leaf.

The weighted-variation deep search completed: partial=false, errors=[],
unfinished=[], inventory65184 with zero pending files, generation1222559,
current1222560; refresh was running in background. Relevant hits were
source-only. Candidate/source/idea/ingredient fields were inspected.
The generated prime-power weighting recipe concerns another carrier and
does not discharge the actual removal jumps. The existing native velocity
primitive and uniform profile bound supply the required inputs.

## Dependency audit of the reciprocal and primitive argument

The subsequent BV/reciprocal search completed with partial=false,
errors=[], unfinished=[], inventory65186, zero pending files,
generation1222593/current1222594 and background refresh. Candidate,
source, idea and ingredient fields were inspected. Native inverse-jump
calculus was absent from the useful hits; generated reciprocal-Jacobian
ingredients concern another problem. Mathlib's AC primitive theorem,
BV Stieltjes vector measure and Lipschitz composition are applicable
infrastructure. No assumed receiver closes the native target.

The remaining argument can be specified without any smoothness assumption
at a removal. Write c_p=a(log p)/p and tau_p=2 log p. The audited
decomposition makes J locally absolutely continuous off the locally finite
set of tau_p, right-continuous everywhere, and

    J(tau_p-)=J(tau_p)+c_p.

The asymptotic t^2 J(t)->-D0/3 gives T>=1 and c>0 such that
J(t)<=-c/t^2 for t>=T. Passing to the left limit at tau_p>T yields the
same bound for J(tau_p-). Thus neither reciprocal denominator vanishes.
For every T<=A<=B, subdivide at the finitely many removal clocks in (A,B].
On each open piece J is an AC integral plus a constant and is separated
from zero on its closure using the appropriate one-sided endpoint values.
The AC reciprocal chain rule applies on that piece. Adding the endpoint
changes gives exactly

    1/J(B)-1/J(A)
      = -integral_A^B V(t)/J(t)^2 dt
        +sum_(A<tau_p<=B) c_p/[J(tau_p)*(J(tau_p)+c_p)].

This is the next Lean target. It does not follow by differentiating J
and ignoring its atoms. Its continuous integrand is bounded in absolute
value by c^-2*t^4*|V(t)|; each jump is bounded by
c^-2*tau_p^4*|c_p|. The polynomial-weight admission theorems under audit
therefore supply every positive exponential damping of both parts.

For real lambda>0, the ordinary product rule on the same pieces gives
the derivative measure of w_lambda(t)=exp(-lambda*t)/J(t): continuous
density -exp(-lambda*t)*(lambda/J(t)+V(t)/J(t)^2), and jump
exp(-lambda*tau_p)*c_p/[J(tau_p)*(J(tau_p)+c_p)]. Both absolute masses
are finite, and w_lambda tends to zero. Their integrals over (A,B]
equal w_lambda(B)-w_lambda(A) by the preceding finite partition argument.
This constructs the finite signed Stieltjes measure directly.

Stronger primitive conjecture: for every real b<delta, no eventual bound
|Q(t)|<=C*exp(b*t) exists. It suffices to handle 0<=b<delta, since b<0
implies the already included b=0 bound. Suppose such a bound holds and
put c=(b-delta)/2<0 and lambda=delta+c>b. The two signed measures

    mu=Q*dw_lambda on (T,infinity),
    nu=Q*w_lambda dt on (T,infinity)

have finite absolute mass by the positive margin lambda-b. For Re z>c,
let A(z), B(z) be their Laplace transforms with kernel exp(-(z-c)t).
They are analytic: on a compact sub-half-plane both this kernel and its
complex derivative are bounded by a constant with respect to each finite
absolute measure; differentiation under the integral applies. The
candidate native transform is

    integral_0^T exp(-z*t)*h(t)dt
      -exp(-(z+delta)*T)*Q(T)/J(T) - A(z)+(z-c)*B(z).

On the far right it equals the actual native transform. To verify this,
apply integration by parts to continuous AC Q and w_(z+delta) on each
finite piece, include every jump, then let the endpoint tend to infinity.
The terminal product vanishes by Re(z)+delta>b. Rewriting
dw_(z+delta)=exp(-(z-c)t)dw_lambda
             -(z-c)exp(-(z-c)t)w_lambda dt
gives the displayed expression with the stated signs.

Twice this native transform minus the actual native/source correction
continues the source across Re z=0. Here 0<epsilon<1/2 ensures
c>-1/2, within the correction's admitted analytic half-plane. The source
rigidity argument and its unconditional Hardy-zero nonzero residue would
then contradict analyticity at that boundary zero. This strengthens the
planned obstruction to sub-delta exponential growth of Q; it remains
unformalized. Missing Lean obligations are the one-sided-limit identities,
finite-partition reciprocal and product rules, signed-measure transform
analyticity, and the final native-source identification. The exact
transform representation is the positive survivor sought alongside the
growth obstruction. No claim of RH closure or signed primitive theorem.

## Verified admission checkpoint

`RoutePLatePrimeIncrementVariation.lean` passed the foreground final
`lake --old env lean ... -o ...` audit (session50941, exit0). Its four
public conclusions admit the continuous velocity and the absolute
removal series for every positive exponential damping, both without and
with an arbitrary natural polynomial power. The proof freezes only a
finite terminal clock, then uses the inverse-power series for a uniform
window bound. Both new leaves are wired into RHTower; no umbrella build,
new axiom, numerical experiment or heartbeat override was used.

The earlier two RP69 searches also completed without partial stages,
errors or unfinished stages: reciprocal/BV inventory65174 with
generation1222351/current1222352; prime-removal inventory65176 with
generation1222371/current1222372. Both had zero pending files and
background refresh; useful hits were source-only and were checked
against source and the installed Lean toolchain. The API scratch audits
passed, including the polynomial-exponential comparison lemma.

Immediate formal target: freeze removal mass on a finite terminal window
as a sum of indicators of [2 log p,infinity). Prove its right limit and
left limit by finite sums, then combine the AC velocity primitive with
this step function to identify J(tau_p-)=J(tau_p)+c_p. Use the established
asymptotic on both one-sided values to discharge every reciprocal
denominator. Only then prove the finite-window reciprocal identity above.

The separate /tmp axiom audit passed (session17075, exit0). All ten public
theorems of the two new leaves use only propext, Classical.choice and
Quot.sound. Global lint exited1 on16 unrelated unreachable modules; exact
names are recorded in the RP69 working log. No error concerns either
new leaf, and no global lint pass is claimed.

Guard for the final weld: the continued candidate is initially identified
with the literal Bochner transform only on the far-right half-plane.
Bounded Q does not establish absolute source admission for every Re z>0.
Consequently the existing helper whose function is fixed to causalTransform
cannot be applied there by fiat. Generalize its analytic-rigidity argument
to an arbitrary analytic candidate with proved far-right agreement, then
apply the nonzero-residue contradiction to that candidate.

Useful installed API for the next leaf:
`intervalIntegral.continuousOn_primitive_interval'` takes interval
integrability and membership of the base point in the unoriented closed
interval. It supplies continuity of the velocity primitive on the whole
window; choose a strictly larger terminal clock for local limits.
Source read in Mathlib/MeasureTheory/Integral/DominatedConvergence.lean;
verify the exact constant in a /tmp Lean scratch before use.

The one-sided-limit deep search ended partial=true with interrupted
text_retrieval and source_retrieval. Available candidate/source/idea/
ingredient fields were inspected. Inventory65195, zero pending files,
generation1222766/current1222770, background refresh; compiler evidence
was source-only. ContinuousWithinAt.rightLim_eq is a useful candidate.
The generated CCM finite-budget step is unrelated to the native step
function. Proceed from the available hits and the explicit finite sum;
the partial search is not a mathematical obstruction.

## RP70: physical one-sided limits and reciprocal jumps

Conjecture to discharge next: J is right-continuous on the positive ray,
and J(2 log p-)=J(2 log p)+a(log p)/p for every prime p. Paper proof:
freeze removal primes at a strictly later finite clock, take limits of
their indicator steps, and subtract this from the continuous velocity
primitive. Distinct prime removal clocks are distinct by injectivity of
log on positive reals. The negative inverse-square asymptotic then applies
to both one-sided denominator values on one common late ray. This is
needed for the signed-primitive transform argument, not an energy payment.

The current deep native limit search completed partial=false, errors=[],
unfinished=[], inventory65196 with zero pending files,
generation1222806/current1222807, background refresh and source-only
compiler evidence. Candidate/source/idea/ingredient fields were read.
The generated late-prime insertion recipe is a different carrier and does
not identify removal limits. Work proceeds from the audited native
velocity/removal decomposition and the installed one-sided-limit APIs.

The exact native one-sided-limit leaf passed its foreground final audit
(RoutePLatePrimeIncrementLimits, session99412, exit0) and is wired. It
proves the physical jump and right continuity, using the finite step sum.
Next discharge reciprocal denominators and admit their actual continuous
and atomic coefficients with the polynomial weights already proved.

The second RP70 search, for reciprocal FTC with jump corrections,
completed partial=false/errors=[]/unfinished=[], inventory65198 with zero
pending files, generation1222871/current1222872, background refresh and
source-only compiler evidence. Candidate/source/idea/ingredient fields
were inspected; its generated unrelated correction-factor recipe is not
applicable. The actual corpus supplies a stronger useful input:
criticalAbelLogProfile_hasDeriv_right holds even at arithmetic clocks.
An implementation can use the correct right-velocity representative with
channel support [log p,2 log p), subtract the cumulative reciprocal jumps,
prove the corrected inverse continuous, and apply
intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le. The existing
velocity on (log p,2 log p] differs only at countably many endpoints.
This avoids assuming an a.e. derivative alone implies the FTC; the
right derivative and continuity must both be proved.

The reciprocal coefficient leaf passed its foreground final audit
(RoutePLatePrimeReciprocalAdmission, session82030, exit0) and is wired.
It constructs one late ray with nonzero actual left and right values,
identifies the literal reciprocal jump using Function.leftLim, and admits
both V/J^2 and all absolute reciprocal jump masses under every positive
exponential damping. These are unconditional native facts; no denominator
or integrability receiver was left as a hypothesis. The finite-window
FTC is still not asserted.

The third RP70 search (native right velocity) completed with
partial=false/errors=[]/unfinished=[], inventory65201, zero pending files,
generation1222975/current1222981, background refresh and source-only
compiler evidence. Candidate/source/idea/ingredient fields were read.
The generic finite Abel-summation recipe does not supply the required
right derivative; use the inspected native right-derivative theorem.
The in-progress right-velocity leaf freezes the complete profile channels
through a finite terminal clock, proves their right derivatives using
[log p,2 log p), and identifies this velocity a.e. with the admitted one.

The right-velocity leaf passed its final foreground audit (session7677,
exit0) and is wired. The first audit found only local elaboration issues:
explicit implication introductions, dependent-if rewriting by simp,
shift-map membership and id reduction. The theorem holds at every clock,
including entry and removal, and its a.e. agreement transfers local
integrability from the admitted velocity.

The next leaf RoutePLatePrimeReciprocalFTC is under audit. Its paper proof
is now dependency-closed: for any finite removal weights, the cumulative
step sum is right-continuous, has right derivative zero everywhere, and
its left limit omits precisely the endpoint weight. For the actual
reciprocal weights r_p, K=1/J-sum_(tau_p<=t) r_p has matching left and
right limits at each late removal; elsewhere both terms are continuous.
The common nonzero late ray gives K'_right=-V_right/J^2 everywhere.
Positive exponential admission unweights on every finite window, giving
the derivative's interval integrability. Right-derivative FTC proves
1/J(b)-1/J(a)=-integral_a^b V/J^2+sum_(a<tau_p<=b) r_p, retaining literal
right endpoint values. This identity is not yet claimed Lean-verified.

Next transform implementation can use ordinary integrals and an atomic
series instead of introducing a general signed-measure library. For a
continuous primitive Q, the jumps of exp(-lambda*t)*Q(t)/J(t) are exactly
exp(-lambda*tau_p)*Q(tau_p)*r_p. Under a hypothetical Q=O(exp(b*t)),
lambda>b gives absolute admission of both this series and the continuous
integration-by-parts terms. The resulting analytic candidate still needs
far-right identification and analytic rigidity; absolute source admission
throughout Re z>0 must not be assumed.

The transform search completed partial=false/errors=[]/unfinished=[],
inventory65233, zero pending files, generation1223158/current1223159,
background refresh; compiler hits were source-only. All candidate and
source statements and the empty proof-idea list were inspected. The
generated signed-measure conversion recipe merely assumes an existing
finite measure; it does not prove admission or the native transform weld.

Direct corpus inspection found an existing arbitrary-candidate result:
no_routePSourceLaplace_analytic_extension_past_axis, in
SPEQuantileRieszRoutePSourceNoAnalyticExtension. It only requires agreement
for Re z>1/2 and analyticity for Re z>-1/8. Its proof uses the analytic ODE
identity and a Hardy zero. Thus no new fixed-causalTransform receiver is
needed. The fixed crossing width -1/8 suffices when delta-b>1/8; the full
claimed growth classification needs the same proof for every negative
crossing width, or the variable-width rigidity/residue argument described
above. Do not apply the fixed-width result when the continuation domain
is narrower. A focused corpus search for this interface is running.

The focused extension search completed partial=false/errors=[]/unfinished=[],
inventory65237, zero pending files, generation1223199/current1223200,
background refresh and source-only evidence. All candidate/source/idea/
ingredient fields were inspected. It also retrieved
not_bounded_ccmThirdGradeExponentialClockCumulative, whose source confirms
the same valid mechanism: construct a shifted analytic candidate from a
bounded primitive, identify only in a safe far-right region, then cross
a Hardy barrier. Its arithmetic source is different, so it is a proof
pattern, not a substitute for the native mixed-work transform identity.

The literal primitive leaf RoutePNativeSignedMixedPrimitive has been
written and awaits audit. It proves local admission from J=integral V-A,
then obtains Q's derivative at every positive clock from the actual
mixed work's right-continuity. This removes the need for a hypothetical
smooth primitive in the coming product identity. It asserts no growth
bound. The reciprocal FTC audit reached its final theorem with only
notation/definitional-equality repairs remaining.

### RP70 refinement: absorb atoms before taking the transform

The current native calculus exposes a simpler exact positive survivor.
On a fixed late ray T, define

    H_Q(t)=sum_(T<tau_p<=t) Q(tau_p)*r_p,
    P(t)=Q(t)/J(t)-H_Q(t),  D(t)=Q(t)*V(t)/J(t)^2.

Because Q is continuous, its product with 1/J jumps by precisely
Q(tau_p)*r_p. Thus P is continuous and has right derivative everywhere

    P'_right(t)=exp(delta*t)*h(t)-D_right(t).

The native mixed-work derivative, including the actual J factor, cancels
the denominator in Q'/J. This is a derived identity, not a postulated
smooth receiver. D_right=D a.e. Every finite window admits both terms,
so right-derivative FTC for exp(-(z+delta)*t)*P(t) gives

    integral_T^B exp(-z*t)*h(t)dt
      = exp(-(z+delta)*B)*P(B)-exp(-(z+delta)*T)*P(T)
        + integral_T^B exp(-(z+delta)*t)*((z+delta)*P(t)+D(t))dt.

This absorbs every physical atom before taking an infinite transform.
Only ordinary Bochner Laplace integrals of P and D are then needed; no
analytic atomic-series or general signed-measure library is required.

Under the contradiction hypothesis |Q(t)|<=C exp(b*t) for t>T, take
b>=0 (negative b implies the bounded case). For every eta>0, the admitted
series sum exp(-eta*tau_p)*|r_p| and positivity of b+eta give

    |H_Q(t)| <= C exp((b+eta)*t) * sum_(T<tau_p) exp(-eta*tau_p)*|r_p|.

This is a finite-sum comparison, not a uniform full-ray prime-core
replacement. Combined with |1/J(t)|<=C_J*t^2, it admits P against every
exp(-lambda*t), lambda>b. D is admitted for the same lambda by the
already-proved admission of V/J^2 with damping lambda-b. The terminal
product vanishes for Re(z)+delta>b after choosing eta strictly inside
that margin. The candidate native transform is therefore

    nativeHead_T(z)-exp(-(z+delta)*T)*P(T)
      +(z+delta)*LaplaceTail(P,T,z+delta)+LaplaceTail(D,T,z+delta).

Its analyticity and far-right agreement would contradict the source's
Hardy barrier after the actual correction is subtracted. This sharper
implementation plan is paper-checked but not Lean-proved. Next formal
target: the literal Q/J corrected derivative and finite-window product
identity, then the two ordinary Laplace admissions under the contradiction
hypothesis. Signed primitive growth and every final RH debt remain open.

The exact reciprocal FTC is now Lean-verified. Final foreground audit
RoutePLatePrimeReciprocalFTC (session81271) exited0; leaf wired into
RHTower without an umbrella build. It proves the corrected reciprocal
continuous with an everywhere right derivative on a native late ray,
then the exact finite-window inverse formula with the complete cumulative
jump difference. Repairs were finite-step predicate equivalence and
explicit function extensional/definitional expansion; the FTC itself
needed no additional mathematical premise. The expanded /tmp API audit
also passed (session80497). Axiom auditing remains pending.

The reciprocal FTC leaf is now being extended with the actual Q product,
reusing its finite step-sum machinery. Define P=Q/J-sum_(tau_p<=t)Q(tau_p)r_p
with the full early constant retained. This differs from the truncated
late-ray P above only by a fixed constant, so the exact derivative and
window formula agree. The new public targets are an unconditional late
ray on which P is continuous with right derivative exp(delta*t)*h-D_right,
and P(b)-P(a)=integral_a^b exp(delta*t)*h-integral_a^b D. These additions
await audit; the previously audited inverse-only theorems remain separate.
The literal Q audit found only measure inference, pointwise function
notation, empty-interval orientation and unfolding issues; repairs are
under re-audit. The further /tmp calculus API audit passed (session8853).

RoutePNativeSignedMixedPrimitive passed its final foreground audit
(session5919, exit0), and is explicitly wired into RHTower. Its six public
theorems establish local admission of J and the literal mixed work,
measurability and right continuity of the mixed work, and continuity plus
the everywhere right derivative of Q. No signed bound is assumed. The
expanded reciprocal FTC leaf, including the exact native Q/J product
calculus and finite-window identity, is now under audit.

The expanded RoutePLatePrimeReciprocalFTC passed its final foreground
audit (session61643, exit0) on its first product-extension audit. Both
exists_routePNativeMixedCorrectedPrimitiveCalculus and
exists_routePNativeMixedCorrectedPrimitiveFTC are now Lean-verified.
The same late ray works for every real epsilon. Every physical Q/J jump
is retained and absorbed before the exact native-profile identity is
integrated. This closes the finite-window product-calculus obligation;
the infinite-ray Laplace admission and Hardy-barrier weld remain open.

Final RP70 axiom audit34722 exited0: all25 public theorems in the five
new leaves use only propext, Classical.choice and Quot.sound. All five
leaves are wired; no full or umbrella build. Global lint50493 exited1
on14 unrelated unreachable modules, listed in the RP70 working log; no
new leaf has a lint error. All owned processes terminated and ten /tmp
artifacts were cleaned after evidence was persisted. RH and the signed
primitive growth obstruction remain unproved. The next proof obligation
is the ordinary Laplace admission of the now-formal native P and D under
the growth contradiction hypothesis, followed by far-right identification.

## RP71: infinite-ray admission from the growth contradiction

Previous turn classified as progress: five native leaves and25 public
theorems passed final Lean/axiom audits. Current source revalidation
confirms the exact corrected primitive and both FTC identities. This
turn stays on the same signed-growth conjecture; no numerical experiment
or new RH premise. Primary obligations: convert the actual weighted
reciprocal-jump summability into a bound for cumulative Q-weighted jumps,
retain the finite early constant, admit P and D against exp(-lambda*t)
for lambda>b under the contradiction hypothesis |Q|<=C exp(b*t), then
construct the ordinary Laplace candidate and identify it on the far right.
Positive-damping energy payment, high-LCM cancellation and both physical
history debts remain open. A deep cumulative-admission search is running.

The cumulative-admission search returned partial=true with interrupted
text_retrieval; errors and unfinished stages report that interruption.
Available candidate/source/idea/ingredient fields were inspected.
Inventory65253, zero pending files, generation1223465/current1223467,
background refresh, source-only compiler evidence. Useful hits confirm
the existing native weighted removal admission and exact removalSum.
The generated Poisson jump-rate recipe addresses a different carrier.
Proceed from the available native facts and finite sum/subtype comparison.
The first new leaf is under audit: exact early/late product-jump split,
finite prime sum domination by the admitted series, and transfer of a
hypothetical Q envelope to P with any strictly larger exponent. These
are intermediate implications for the contradiction, not a claim that
Q has such an envelope. Installed API scratch39263 passed.

The transform-admission deep search83261 exited0 with partial=true:
semantic_retrieval exceeded its local runtime deadline. Inventory65256,
zero pending files, generation/current1223494, background refresh,
source-only evidence. Candidate/source/idea/ingredient fields inspected:
generic Bochner agreement is useful; the generated Hawking transfer
recipe does not establish native admission. The expanded API audit87065
passed after renaming a reserved lambda token. Admission leaf audit7625
reached a single absolute-value rewrite error; repaired and re-auditing.

The variable-barrier search34158 exited0, partial=false, no errors or
unfinished stages. Inventory65260, pending0, generation/current1223564,
query index1223554; background refresh, source-only candidates. The
existing fixed-width source obstruction was retrieved; other Hardy and
Suzuki carrier recipes do not prove the needed native assertion. Source
search confirms the only use of that public receiver is quantitative
source oscillation. Generalize its proved analytic-ODE argument from
width1/8 to every negative abscissa, preserving the old theorem as a
specialization. This is necessary for an arbitrarily small signed-growth
gap; no improvement of a numerical constant is being claimed.

Admission audit65960 exited0. It verifies the complete early/late jump
split, exponential envelope transfer, both real Laplace admissions, and
terminal decay under the proposed Q bound. Removed an unused private
binder and queued final clean audit. Transform API20600 passed, including
real-to-complex admission and the real-time derivative of the exponential
kernel. A new leaf constructs the ordinary indicator-supported tail
transform, its open-half-plane holomorphy, and complex terminal decay;
its actual native P/D specialization is written and awaits audit.

Remaining weld is explicit: integrate the product exp(-w*t)*P(t) with
the verified everywhere right derivative, replace V_right by V a.e.,
and take the terminal limit only where h's transform is absolutely
admitted. This identifies the candidate on Re(z)>1/2. Neither formal
Bochner values outside that convergence half-plane nor a.e. derivatives
alone are accepted as substitutes for this argument.

Clean admission audit18751 exited0; its leaf is wired. The generalized
source obstruction audit16201 exited0: every negative abscissa is now
excluded, with agreement required only for Re(z)>1/2; the original
fixed-width theorem remains a proved specialization. The native weighted
FTC and its infinite-tail identity have been written and await audit.
The latter uses the existing global L1 theorem for the Abel log profile
to justify native admission only on Re(z)>1/2. No improved source
convergence assumption enters the identity.

Paper completion of the signed-growth contradiction, still awaiting
the final Lean weld: fix0<epsilon<1/2, delta=1/2-epsilon, 0<=b<delta,
and the proposed eventual Q envelope. Move a beyond all native thresholds.
Set c=(b-delta)/2. Then -1/2<c<0 and Re(z)>c implies
Re(z+delta)>b. Let R=2*h-source be the literal decaying correction,
0<R(t)<=20/3*exp(-t/2) on the positive ray. Its tail transform is
holomorphic for Re(z)>-1/2. The finite source head is entire. Therefore

    L(z)=sourceHead_a(z)
      +2*(-exp(-(z+delta)*a)*P(a)
           +tail_D(z+delta)+(z+delta)*tail_P(z+delta))
      -tail_R(z)

is holomorphic on Re(z)>c. For Re(z)>1/2 the native tail identity,
the exact relation source=2*h-R, and admitted head/tail splitting identify
L with routePSourceLaplaceContinuation. The now-verified variable-width
Hardy obstruction contradicts this. The expected unconditional survivor
is cofinal escape of |Q(t)| above every C*exp(b*t), for every b<delta;
negative b reduces to b=0 on a positive late ray. This is neither a
two-sided sign-oscillation theorem nor a positive-damping square bound.
The open RH energy/history obligations remain unchanged. Useful installed
head/tail splitting API found by source: intervalIntegral.integral_interval_add_Ioi;
it still requires its /tmp API check before use in the final weld.

Expanded transform API71799 exited0. Transform audit53737 found only
set-membership unfolding and indicator-measure inference issues; these
were repaired explicitly. Final transform audit11514 exited0 and the
leaf is wired. Weighted FTC audit3440 verified native far-right admission
and the limit passage, but exposed two pointwise-function representation
issues in the finite FTC: product-function equality during derivative
conversion and Pi multiplication at endpoints. Replaced conversion by
the exact product-function target plus congr_deriv, and expanded endpoints.
Re-audit pending. The final growth-barrier leaf is now written: entire
finite source head, actual correction admission, exact source head/tail
reconstruction, arbitrary-width analytic contradiction, and cofinal
subcritical exponential escape (including negative b by reduction to0).
This final survivor is not yet Lean-verified; no RH completion claim.

Growth API35302 passed. Weighted FTC audit21166 passed, exit0, and its
leaf is wired. Native far-right absolute admission, complex weighted
finite FTC and exact infinite-tail identity are now Lean-verified.
The actual primitive, all product jumps and the initial boundary remain
in the formula. The final source reconstruction and cofinal exponential
escape theorem are now under their first foreground audit.

Growth audit89112 found restricted-integrability unfolding and an
incorrectly inferred affine composition point; both were made explicit.
The escape theorem itself elaborated after its dependencies. Re-audit
running. The next-energy search86721 exited0, partial=false, no errors or
unfinished stages. Inventory65276, pending0, query index1223782,
generation/current1223791, background refresh, source-only evidence.
All candidate/source/idea/ingredient fields inspected. It reconfirms the
native joint balance and the admitted coprime Mellin source. The proposed
Burnol damping/colligation recipe already assumes square integrability;
it cannot supply the missing absolute native energy bound. The next
attack must retain the complete square and negative coprime work jointly
at the physical cutoff; a separate mixed primitive budget is exactly the
mechanism this card tests. No new joint-absorption theorem is claimed.
