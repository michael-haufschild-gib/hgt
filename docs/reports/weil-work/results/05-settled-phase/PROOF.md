# WP05 proof ledger

## Main problem

OPEN. No proof yet derives atomicity or phase settlement of the canonical measure from full positivity.

## Cycle 1: count control versus phase transport

**Verdict: REDISCOVERED / BRIDGE.** Smoothed or bounded counting discrepancies do not supply settlement. The corpus already warns of this; the elementary transport mechanism below is not claimed as new scientific knowledge. It is the positive range of the failed count-only shortcut, with exact normalization and strict cutoffs.

For real parameters a, d, q define l = 1 + |a|, r = l + |d|, and c = (1 + cos q)/2. Put positive atoms of mass c and 1-c at l and r. Both ordinates are at least one, both masses are nonnegative, and total mass is one. Its strict cumulative count is

    S(y) = c 1[l < y] + (1-c) 1[r < y].

The phase E(x) = exp(2 pi i x) equals 1 below l and above r; on (l,r] it equals E(c). This includes the degenerate case l=r. Therefore

    |E(S(y))-1| = |E(c)-1| 1[(l,r]](y),
    integral_R |E(S(y))-1| dy = |E(c)-1| |d|.

This exact formula shows why a bounded counting discrepancy is insufficient: the discrepancy from the unit atom at r is bounded by c independently of |d|, while integrated phase error grows exactly linearly in |d| whenever E(c) != 1. At q=pi/2 one has c=1/2 and error 2|d|. This is a statement about explicitly constructed spectra; no arithmetic Weil producer is asserted.

For a finite family, let S be the sum of these strict counts. The identity E(sum x_j)=product E(x_j), unit modulus, and telescoping give

    |E(S(y))-1| <= sum_j |E(c_j)-1| 1[(l_j,r_j]](y).

Integration gives the exact transport upper bound

    integral_R |E(S(y))-1| dy <= sum_j |E(c_j)-1| |d_j|.

No separation assumption is needed; overlapping intervals and repeated ordinates are retained. The right side is sharp for one packet. Its finite-block restriction gives the same upper bound on any measurable interval. Applying this to a locally finite infinite spectrum requires a separate infinite-sum/limit proof; it is not silently inferred here. The source-derived bound on these transport costs is also unpaid.

## Cycle 2: genuine open boundary

Candidate: replace the existing fixed power bound C(T)=O(T^alpha), alpha<1, by C(T)=o(T) in the monotone fractional-mass rigidity theorem.

Exact obstruction in the existing proof: the contour error is bounded by epsilon^(1-nu), for each fixed nu>0; layer cake costs a Laplace transform of dC. C=o(T) alone does not make epsilon^(1-nu) C(1/epsilon) tend to zero. Choosing nu depending on epsilon without controlling the corresponding constants is invalid. This kills that proof substitution, not the conjecture.

Potential source-specific improvement: fractional atoms occur at zeros of the actual producer, whereas the current strip supremum discards that relation. `[OPEN CORE]`: estimate horizontal top-edge integrals against fractional spectral mass using the Herglotz derivative identity, preserving the original producer and all integer masses. No usable bound has been proved yet.

## Cycle 2 positive source estimate: coefficient-free Littlewood bound

**Statement.** For every original `hW : WeilPositiveFull lam`, there exist C,T0 such that
`Re producerLogZeta(hW,sigma,t) <= C log|t| / log log|t|` whenever
`T0 <= |t|` and `1/2 < sigma <= 2`. No coefficient, atomicity, or phase hypothesis is added.

**Dependency-closed proof.** Set M2 = sum |lam(n)|/n^2, finite by full positivity. For L>0 and Re(s)>=0, the polynomial in the existing Soundararajan inequality satisfies

    |producerPoly(lam,L,s)|/L <= (M2/log 2) exp(2L).

Indeed only 2<=n<exp L contribute. For each term, n^Re(s)>=1,
max(L-log n,0)<=L, log n>=log 2, and n^2<=exp(2L). Bound its norm by
`(|lam(n)|/n^2) exp(2L) L/log 2` and sum using absolute summability at 2.

Put y=log|t|, ell=log y, L=ell/4, and T0=exp(exp 8), so L>=2. Take
sigma0=max(sigma,1/2+1/L). Then sigma<=sigma0<=2,
sigma0-sigma<=1/L, and exp(-(sigma0-1/2)L)<=(sigma0-1/2)L.
The Soundararajan inequality applies. Its polynomial term is at most
`(M2/log 2) sqrt(y)`; the two archimedean terms are each at most
`(y/2+3)/L`; the existing residual bound is at most M2+2 because exp L<=|t|.
Since sqrt(y)<=2y/ell<=2y/L and 1<=y/ell<=y/L, the existing elementary
assembly lemma with kappa=M2/(2 log 2) bounds the total by
`(2M2/log 2+M2+9)y/L`. Therefore C=4(2M2/log 2+M2+9) works.

All analytic inputs are existing source theorems in `WeilProducerSoundararajanInequality`
and `WeilProducerLittlewoodBound`; the new step is the summability-based polynomial
bound and the shorter cutoff. The old Littlewood cap theorem assumes its estimate
as input and does not remove the coefficient premise itself.

**Novelty/significance.** SURVIVES as an unconditional source estimate beyond the
corpus theorem's coefficient hypothesis. Classical Littlewood/Soundararajan method;
no broad scientific novelty claimed. This is an intermediate source growth bound,
not yet the requested cumulative-phase estimate or a new rigidity class.

## Cycle 3: source-derived phase-disorder dichotomy

**Exact claim.** Fix the original full-positive source and a boundary-continuous
normalized producer G satisfying its actual differential equation. For any bounded
measurable lock w with `G(1-lineS(t))=w(t)G(lineS(t))` below a fixed height, and
any nonzero constant c0, either lambda=Lambda and RH, or there exist a,K>0 such
that at arbitrarily large T,

    integral_(T,2T] |w(-t)-c0^(-1)| dt
      >= a T exp(-K log T/log log T).

There is no decay assumption in this statement. For exact positive atomic
representations, the corpus product supplies G and w(t)=exp(2 pi i S(-2t));
the statement then concerns the actual strict-cutoff phase at scale 2T.

**Dependency-closed proof.** The new Littlewood theorem has constants C>0,T0
independent of G. The corpus boundary comparison at sigma'=1/2+1/log(2T)
bounds `|phiG(t)|` by `exp(4) exp(Re producerLogZeta(sigma',2t))` for T<t<=2T.
The existing dyadic cap at base 2T and log(2T)<=2 log T give, for sufficiently
large T, `|phiG(t)| <= exp(4) exp(K log T/log log T)` with K=4C.
Thus the weighted block defect B(T) is at most this envelope times its unweighted
L1 defect D(T). All integrals exist: w is bounded measurable, and phiG is continuous
on the compact block.

Suppose rigidity fails. The existing `lock_rigidity_of_block_means` then rules out
`B(T)=o(T)` in its exact quantified block form. Negating that form gives eta>0
such that for every lower cutoff there is a larger T with B(T)>eta T. Combining
the two inequalities and multiplying by the positive reciprocal envelope yields
`D(T)>eta exp(-4) T exp(-K log T/log log T)`. Take a=eta exp(-4).
No assumption on the size of D is used. All remaining inputs are the original
source and the exact producer/lock structure. For the atomic specialization the
representation hypotheses are not claimed to follow from positivity.

For completeness, the atomic change of scale has no hidden asymptotic step.
With Y=2T, the actual phase integral on (Y,2Y] equals twice the lock integral
on (T,2T]. For T>=exp(2), log(2T)<=2 log T and
log log(2T)<=2 log log T. Hence

    log T/log log T <= 2 log(2T)/log log(2T).

Replacing K by 2K therefore preserves the lower bound after changing scale.
The constant phase is arbitrary; the proof never assumes that it is a limit.

**Assessment.** SURVIVES as a quantitative source-derived obstruction; the targeted
build, final source audit and axiom audit passed. This is not settlement of arbitrary hW. The contraposition
step is elementary; the improved source envelope is the mathematical input.
Do not claim a general scientific novelty result from corpus novelty alone.

**Next attack audit.** Existing Soundararajan mean-square bounds require both
`|lam(n)| <= kappa log n` and summability of `restWeight lam`. The new Littlewood
bound removes neither premise from the large-value/moment step: those premises
also control prime-polynomial variance and the non-prime remainder. Substituting
the new cutoff estimate in the old moment theorem is therefore not a valid way
to obtain a source-wide mean-square theorem. A collective estimate tied to the
actual spectral measure, or a new arithmetic coefficient law, is still needed.

## Next candidate: canonical measurable boundary trace

This is a proposed bridge, not a proved settlement theorem. Fresh corpus search
located `exists_zetaQuotient_primitive`, the horizontal potential identity, and
`tendsto_re_weilContinuation_interval`. The last theorem needs only non-atomic
endpoints, with a common full-Lebesgue-measure set supplied by its companion.

Candidate proof mechanism: choose a primitive P of the actual Weil continuation
on Re(s)>1/2, normalized at 2, and set G(s)=bigG(lam,2) exp(P(s)-P(2)). The
normalization is real and positive. Reality of the source gives conjugation
symmetry. Positivity of Re(Phi) makes |G(sigma+iy)| nondecreasing in sigma, so a
finite nonnegative limit rho(y) exists as sigma decreases to 1/2, bounded by
|G(2+iy)|. On a vertical segment, conjugation symmetry and the logarithmic
derivative identity give

    2 arg G(1/2+x+iy) = integral_(-y,y] Re Phi(1/2+x+it) dt,

where arg is the continuous primitive branch, not the principal argument.
For y>0 with non-atomic endpoints, the right side tends to pi*mu((-y,y]).
Thus the horizontal boundary trace should equal

    rho(y) exp(i*pi*mu((-y,y])/2).

Its conjugate reflection has multiplier exp(i*pi*mu((-y,y])). Symmetry rewrites
this as exp(2*pi*i*(mu((0,y))+mu({0})/2)). This retains central mass instead of
silently imposing a spectral gap. Local L1 trace convergence should then follow
by domination by the continuous right-edge modulus |G(2+iy)|. Continuity of the
boundary trace itself is neither asserted nor needed in this proposed step.

Remaining audit: precise primitive/reality APIs, normalization constants and
measure conventions; then formalize the trace theorem before attempting to
replace the closed-boundary-continuity premise in the contour argument. That
contour replacement remains an open proof obligation. The mechanism is classical
Herglotz boundary recovery; any value here is removing an unpaid corpus input,
not claiming a new boundary-inversion method.

## Cycle 4: dependency-closed trace statement

**Statement to formalize.** From hW alone construct the normalized completed
producer G on Re(s)>1/2 and an almost-everywhere strongly measurable boundary
function b. Prove its horizontal limit almost everywhere, local L1 convergence
on every compact interval, and for y>0 the reflection multiplier
`exp(i*pi*mu((-y,y]))`. The multiplier equals the strict cumulative-phase
expression with central half-mass at non-atomic endpoints. No atomicity,
support gap, phase-decay or boundary-continuity premise is added.

**Proof.** The right half-plane is an exact domain, so choose P with P(2)=0
and P'=Phi. Put G=bigG(lam,2)*exp(P). Uniqueness of primitives and reality of
Phi show P(conj(s))=conj(P(s)); bigG(lam,2) is real. Hence G is normalized,
satisfies G'=Phi*G, and respects conjugation. For each y, exp(Re P(1/2+x+iy))
is nondecreasing in x>0 because its logarithm has derivative Re Phi>=0.
Its infimum rho(y) is finite and nonnegative, and is its limit as x decreases
to zero. It is bounded above by its value at x=3/2.

For y>0 with mu({y})=mu({-y})=0, the fundamental theorem on the vertical
segment and conjugation of P give

    2 Im P(1/2+x+iy) = integral_(-y,y] Re Phi(1/2+x+it) dt.

The existing canonical interval-phase theorem makes the right side converge
to pi*mu((-y,y]). Define b(y) for y>=0 as
`bigG(lam,2)*rho(y)*exp(i*pi*mu((-y,y])/2)`, and define b(y) for y<0 by
conjugation of b(-y). The exponential's modulus/argument decomposition proves
the claimed horizontal limit at every non-atomic y; at y=0, reality of P gives
the limit directly. Atoms form a countable set, so this is an a.e. limit.
The reflection formula for y>0 follows directly from this explicit definition,
reality of bigG(lam,2), and multiplication of exponentials.

To obtain measurability, take the a.e. limit of the analytic horizontal slices
along x decreasing to zero. Horizontal monotonicity bounds those slices,
for 0<x<=3/2, by |G(2+iy)|. The same bound holds for b almost everywhere by
passing to the limit. The right-edge function is continuous on every compact
height interval; twice its modulus is therefore an integrable majorant for
|G(1/2+x+iy)-b(y)|. Dominated convergence proves local L1 convergence.

All dependencies are existing exactness, conjugation, positivity, canonical
Poisson recovery and elementary integration/limit facts. This closes the trace
statement on paper. It does not close the later contour replacement or supply
settlement. Verdict: BRIDGE; classical inversion mechanism, useful removal of
the atomic representation premise from the boundary-trace construction.

### Stronger trace statement exposed by the contour audit

The local L1 statement upgrades to global L1 without a new source premise.
The corpus theorem `FractionalMassRigidity.exists_bound_bigG_two`, whose only
input is absolute Dirichlet summability, bounds the actual right-edge modulus by
`C (|y|+4)^N exp(-pi |y|/4)`. Full positivity supplies that summability.
`exists_bound_pow_mul_exp_neg (N+2)` and `pow_mul_exp_neg_le_div` bound this by
`C K/(1+y^2)`, an integrable function on the whole real line. Thus the continuous
right-edge modulus is integrable. The trace is integrable by its almost-everywhere
right-edge bound; so is every slice with 0<x<=3/2. Dominated convergence with
majorant twice the right-edge modulus proves

    integral_R |G(1/2+x+iy)-b(y)| dy -> 0 as x decreases to 0.

This is a dependency-closed paper proof of the strengthened trace claim. It
uses no conjectural decay and does not assume boundary continuity. The inverse
Mellin contour receiver still needs its own extension; global trace convergence
supplies the infinite-height passage but does not by itself settle the phase.
Novelty verdict remains BRIDGE, now strong enough to control the contour tails.

### Next contour conjecture and kill test

The precise proposed receiver extension replaces closed-strip continuity of E
in `critical_line_inverse_mellin` by interior holomorphy, its existing uniform
C/(1+t^2) strip bound, and an a.e. horizontal boundary trace e. For fixed Mellin
parameter y>0, first shift to an interior line Re(w)=sigma>1/4 using the existing
rectangle theorem. Then send sigma to 1/4. The Mellin multiplier has modulus
y^(-sigma), uniformly bounded for sigma in [1/4,3/4]; dominated convergence
passes to e(2t). The right-line Mellin inversion is unchanged.

This receiver-level mechanism is classical and not a new hypothesis to impose
on hW. Before composing it for the actual producer, derive the corresponding
uniform decay and trace of `bigEG (sourceCompletion hW)` from hW. At s=1 the
polar subtraction is an interior removable singularity; near the critical line
the algebraic denominators are separated from zero. Global trace convergence
for G handles the boundary passage but must not be substituted for E's decay
without this argument. The subsequent even-theta and coefficient steps must
use a.e. boundary identities and measurability throughout. None of those receiver
extensions is yet asserted proved. The intended payoff is removing atomicity
from the canonical phase-disorder alternative, not manufacturing settlement.

The actual-source decay obligation has the following paper route. For
E=bigEG(G), use its existing algebraic identity away from 0 and 1. On
1/2<Re(s)<=3/4, the factors |s| and |s-1| are at least 1/2 and 1/4.
The uniform right-edge bound therefore controls G/(s(s-1)), while Gamma_R(s-1)
has no pole on this closed left substrip and is bounded on every bounded-height
rectangle. On 3/4<=Re(s)<=3/2, E is continuous on bounded-height rectangles
because the pole at 1 was removed inside the holomorphic domain. This gives a
uniform compact-height bound. For |Im(s)|>=4, the existing polynomial-Gamma
bounds and `exists_decay_Gammaℝ_sub_one` give C/(1+Im(s)^2). Combining the two
regions gives the desired strip bound without continuity at Re(s)=1/2.
The boundary value is b(y)/(s_y(s_y-1))-beta*Gamma_R(s_y-1), s_y=1/2+iy;
its a.e. limit and global L1 convergence follow by the same dominated convergence
argument, since neither denominator vanishes on that line. This closes the
analytic source-decay argument on paper, subject to checking the exact installed
Gamma/removable-singularity interfaces before formalization. No resulting Lean
receiver or phase-rate theorem is claimed.

## Cycle 5: actual-source Mellin trace and contour passage

The cycle-4 paper argument for E=bigEG(sourceCompletion hW) has now been checked
against the installed `differentiableAt_Gammaℝ_sub_one`,
`differentiableOn_bigEG`, `bigEG_eq` and `exists_decay_Gammaℝ_sub_one` interfaces.
These pay the removable-pole and Gamma conditions without boundary continuity.
The new source decay claim is C/(1+t^2) uniformly for 1/2<Re(s)<=3/2. Define
its trace e(t) from b(t) by the explicit polar subtraction. Its horizontal a.e.
limit, measurable representative, integrability and global L1 convergence follow
from that uniform bound and dominated convergence.

For each fixed r>0 set H(s)=r^(-s/2)E(s). On 1/2<=Re(s)<=3/2 the multiplier's
modulus depends only on Re(s), and its maximum M is finite by continuity on the
compact real interval. Hence |H(s)|<=MC/(1+Im(s)^2). For 0<x<=1 the entire
closed strip between 1/2+x and 3/2 lies inside E's holomorphic domain. The existing
`integral_vertical_line_shift_of_decay` applies there, giving equal line
integrals. Send x down to zero: H has a.e. trace r^(-(1/2+it)/2)e(t), and the same
integrable majorant gives dominated convergence. Thus

    integral_R r^(-(3/2+it)/2) E(3/2+it) dt
      = integral_R r^(-(1/2+it)/2) e(t) dt.

This closes the weighted contour claim on paper with only original hW and the
positive Mellin argument r as inputs. It is a classical bridge removing the
critical-edge continuity premise from the actual source's contour shift, not
yet a coefficient rigidity theorem or a phase settlement bound. The newly found
`WeilWorkQuantizationRadialBoundary` strengthens radial recovery to all heights;
we do not reprove that endpoint result in this cycle.

### Next source identity; avoid rebuilding inversion

The inspected `HTGeometry.HamburgerThetaDefect.inverse_mellin_shift` allows
sigma=3/4. Its strip then collapses to Re(s)=3/2, entirely inside the source's
holomorphic domain. Apply it to a=dirichletExp(lamLog lam), theta=coeffTheta(a),
E=sourceRemainder(hW), beta=betaG(sourceCompletion hW). The existing Dirichlet
exponential theorem and hW's absolute summability give the right-line identity.
Changing the height variable u=2t contributes a factor 1/2; composition with the
new weighted contour theorem should give

    theta(r) - beta*r^(-1/2)*exp(-pi*r)
      = (1/(4*pi)) integral_R r^(-(1/2+iu)/2) remainderTrace(u) du.

This has a dependency-closed paper proof from the inspected inversion theorem,
real scaling formula `Measure.integral_comp_mul_left`, and the new contour shift.
The remaining formal work is coefficient normalization, the right-line algebra,
and exact scaling; no new analytic theorem is needed for this identity. Then add
the known polar Gamma inversion to obtain the actual boundary defect-kernel
identity and its reflected theta relation. The coefficient rigidity transfer is
still not composed.

Crucial limit on the payoff: E's quadratic decay is for the Gamma-weighted
completion. The normalized phase defect divides by Gamma_R on the critical line;
its decay cancels that archimedean damping. Therefore neither this decay nor the
new global L1 theorem supplies Abel-sublinear normalized defect or unweighted
phase settlement. Claiming that substitution would be circular proof debt.

## Cycle 6 extension: polar subtraction and the normalized trace

Write s(t)=1/2+2it, B(t)=b(2t)/(s(t)(s(t)-1)), and
Phi(t)=B(t)/Gamma_R(s(t)). The denominator is nonzero: s has real part 1/2,
neither s nor s-1 vanishes, and Gamma_R has no zero there. Hence
Gamma_R(s(t))*Phi(t)=e(2t)+beta*Gamma_R(s(t)-1) exactly, including exceptional
heights where b was defined explicitly. The weighted e(2t) integral is integrable:
e is integrable, real scaling preserves integrability, and the weight has constant
modulus r^(-1/4) for each r>0.

Apply existing Mellin inversion to f0(r)=r^(-1/2)*(exp(-pi*r)-1) on Re(w)=1/4.
Its inspected HasMellin formula is Gamma_R(2w-1). The installed Gamma-line
integrability bound supplies the vertical integral. Thus its inverse integral
equals f0(r). Add beta times this identity to the already closed theta/e identity,
with the u=2t scaling checked in both directions. The exponential polar terms
cancel exactly, leaving theta(r)=beta*r^(-1/2)+defectKernel(Phi)(r).
This proof uses only hW and r>0. It pays the actual-source input of the existing
theta-defect calculus but makes no polynomial or phase-rate inference about Phi.

### Reflected theta relation on the same full trace

Define g(t)=(b(2t)-b(-2t))/(s(t)*(s(t)-1)*Gamma_R(s(t))). The quadratic
factor is invariant under t -> -t because s(-t)=1-s(t). Consequently
Gamma_R(s(t))*g(t)=Gamma_R(s(t))*Phi(t)-Gamma_R(s(-t))*Phi(-t).
Each weighted summand is integrable by the polar/remainder decomposition above.
For r>0, the identity
r^(-1/2)*(r^(-1))^(-(1/4-it))=r^(-(1/4+it))
follows from the inspected positive-real complex-power multiplication laws.
Change t to -t in the second integral. It gives
K_g(r)=K_Phi(r)-r^(-1/2)*K_Phi(1/r).
Substitute the theta/Phi identity at r and 1/r; the polar product is one. Thus

 theta(r)=r^(-1/2)*theta(1/r)-beta+beta*r^(-1/2)+K_g(r).

This reflected theta identity is dependency-closed on paper, without boundary
continuity or atomicity. It preserves the original b everywhere and uses only hW
and r>0. The current corpus search is checked before implementation; its coverage
warnings prohibit claiming absence of other proofs. Measurability/polynomial
bounds and the Abel defect-to-coefficient step remain separate obligations.

### Next normalization check, supported by source inspection

The two primitives are chosen from the same existential proposition: a primitive
of weilContinuation on Re(s)>1/2, zero at 2, obtained from
isExactOn_rightHalfPlane(...).with_val_at 2 0. Our version packages that proposition
behind exists_sourcePrimitive; quantizationLogPrimitive chooses it directly.
Lean proof irrelevance may make sourcePrimitive=quantizationLogPrimitive and the
two completions definitionally equal. Verify this in a scratch file before
using it; do not build a duplicate uniqueness proof unless necessary.

The existing radial-growth module supplies measurable_quantizationTraceF,
tendsto_quantizationTraceF, exists_bound_quantizationTraceF on compact intervals,
and exists_norm_quantizationProdF_le in the open strip. Passing the last bound
to the radial limit gives the same O((1+|y|)^(1/2)) bound for |y|>=2. Combining with
the compact [-2,2] bound gives a global polynomial bound. A.e. uniqueness of the
completed trace identifies our sourcePhi(t) with quantizationTraceF(2t), so the
new theta identities transfer to that everywhere measurable representative.
This supplies the next coefficient-transfer regularity without re-proving it
for the piecewise full-measure phase representative. This next transfer is not
claimed formally verified yet.

## Cycle 7: source Abel-lock dichotomy after refreshed corpus audit

The refreshed source now contains RadialTheta, including both arithmetic
Hamburger/Laplace identities and a common linear bound on the actual quotient
Phi(t)=quantizationTraceF(2t) and reflected quotient Psi(t). Reuse these results.
The same-choice primitive/completion identities passed an installed Lean scratch
check. Thus no new measurable-representative or theta construction is needed.

For a real theta put kappa=exp(2*pi*i*theta), a unit. Define
r(t)=1_{t<0}*(kappa^(-1)*Phi(t)-Psi(t)), and g=Phi-Psi. All three functions are
measurable and bounded by a common multiple of 1+|t|. The exact low-half-line
identity g=(1-kappa^(-1))*Phi+r holds for t<0 by algebra.

If delta*abelMass(r,delta) tends to zero, split both source Laplace identities
into t>0, t<0 and {0}. Eliminate the lower Phi term using the exact identity.
This gives L(tau)=kappa*S(tau)-(kappa*beta/pi)/tau+beta+K0(tau), where K0 contains
upper pieces, singleton pieces and the lower remainder. Existing checked kernel
lemmas make epsilon*K0(epsilon+im) tend to zero at each nonnegative integer m:
upper pieces by one-sided damping, singleton pieces by bounded-interval Abel
vanishing, and the lower piece by the supposed Abel limit. The exponential
series S is i-periodic. Existing radial-to-full residue comparison and Hamburger
coefficient receiver yield a(n+1)=2*kappa*beta for every n. Since a(1)=1, all
positive coefficients equal one. Dirichlet-series equality and logarithmic
derivatives then identify lam(n)=vonMangoldt(n) for n>=2; the existing full-cone
comparison theorem supplies RH from this coefficient equality.

Therefore the source alone gives a disjunction: coefficient/RH rigidity, or the
explicit lower reflected remainder fails Abel sublinearity. This is the exact
contrapositive of the proved mechanism, not an assumed phase bound. It removes
atomicity and continuous critical-edge extension from that obstruction. The
remaining work is to transfer the obstruction to the full canonical cumulative
phase with quantitative unweighted block lower bounds, and ultimately derive
an upper bound from the arithmetic source. No settlement conclusion is inferred.

### Positive quantitative form exposed by the Abel alternative

The explicit remainder is measurable, zero for t>=0, and has norm at most
|Phi(t)|+|Psi(t)|, hence a source-derived linear envelope. The inspected
`WeilSpectral.tendsto_mul_abelMass_of_blocks` therefore applies if its dyadic
reflected norms are o(T). Contraposition sharpens the source alternative to:
rigidity, or some eta>0 such that for every R there is T>=R with

 eta*T < integral_(T,2T] |lowerSourceRemainder(-t)| dt.

The threshold can be taken nonnegative by feeding max(R,0) into the negated
block condition. This is a weighted reflected-defect lower bound for the actual
full measure, not an unweighted cumulative-phase estimate. It follows from the
closed coefficient argument and the already checked generic Abel transfer;
no new asymptotic hypothesis is added to its source statement.

### Next full-phase extraction and its normalization

For y>0 let p(y)=exp(i*pi*mu.real(Ioc(-y,y))). The already proved
sourceTrace_reflection says b(y)=p(y)*b(-y), with the whole canonical measure.
A.e. equality of the canonical completed trace with b can be pulled back through
y=2t and y=-2t; nonzero real scaling preserves null sets. Consequently, for t>0,

 |lowerSourceRemainder(theta,-t)|
   = |kappa^(-1)-p(2t)|*|quantizationTraceF(-2t)|.

The quotient at -y is conjugate to the quotient at y: completed-trace conjugation
is in RadialTheta, and lineFactor_conj is in WeilConeSettledLockRigidity. Hence
replace the last factor by |quantizationTraceF(2t)|. These are a.e. identities,
which suffice for the block integrals; no atoms or diffuse mass are discarded.
The function y -> mu(Ioc(-y,y)) is monotone as an ENNReal-valued function by interval
inclusion. Compose its measurable map with ENNReal.toReal and the exponential to
get measurability of p without needing a separate local-finiteness argument.

For the unweighted bound, adapt the inspected proof of
norm_phiG_le_exp_producerLogZeta: replace its critical-edge continuity monotonicity
step by norm_quantizationCompletedTrace_le, which is already source-derived.
G_eq_lineFactor_mul_cexp uses only the interior differential equation and value
at two, so applies to quantizationCompletion. The same lineFactor estimate at
sigma=1/2+1/log(2T) yields the exp(4) transfer. Compose the already proved hW-only
Littlewood log estimate to obtain the same exp(4)*exp(K*log(T)/loglog(T)) envelope
on the actual measurable quotient. Divide the new weighted block lower bound by
this envelope, then substitute y=2t exactly. The expected survivor is the earlier
quantitative disorder alternative for the full canonical cumulative phase,
without atomicity or support-gap premises. Exact Lean API/application checks for
this next extraction remain outstanding; do not claim it formalized yet.

## Cycle 8 exact source statement and integral domination

The target capstone, for every original hW and every real theta, is the
disjunction of coefficient/RH rigidity with existence of a,K>0 such that for
every R there is Y>=R satisfying

 a*Y*exp(-K*log(Y)/loglog(Y))
   <= integral_(Y,2Y] |p(y)-exp(2*pi*i*theta)| dy.

Use the cycle-7 remainder with parameter -theta, so its inverse lock is exactly
the desired phase. After the a.e. factorization and Littlewood envelope, the
remainder norm is dominated on each sufficiently high block by the envelope
times the phase norm. The latter is measurable, bounded by two, and integrable
on the finite interval. Integral domination first proves integrability of the
remainder norm and then gives the inequality; no continuous-edge integrability
lemma is needed. Multiply eta*T<integral|r| by exp(-4-q), q=K*logT/loglogT,
to get a=eta*exp(-4). Substitute Y=2T. For T>=exp(2),
logT/loglogT <= 2*log(2T)/loglog(2T), so replacing K by 2K pays the exact rescaling.

Refreshed corpus still distinguishes this full-measure obstruction from the
earlier atomic theorem. It also now contains finite-residual rigidity with an
explicit finiteness premise; that does not discharge the present upper-bound
problem. External Hamburger/L-data sources remain parent mechanisms, not
producers of missing phase regularity. Classification: BRIDGE. The proof above
is closed on paper; no claim of new scientific novelty or phase settlement.

Endpoint convention: p uses the exact symmetric Ioc(-y,y) mass because that is
what the canonical reflection identity supplies. For a symmetric atomic
representation, at a nonatom y>0 this is twice the strict positive-ordinate
cumulative mass. At an atom the included positive endpoint contributes half of
the symmetric pair. The exceptional ordinates are countable, so the integral
version agrees with the strict-cutoff phase after a.e. transfer. Do not assert
pointwise equality at those atoms or alter the assigned phaseSum convention.

## Next hard conjecture: source circular variance decay

For the actual full-measure phase p, define

 V(Y)=integral_(Y,2Y] integral_(Y,2Y] |p(u)-p(v)|^2 du dv,  Y>0.

Conjecture: every original hW supplies epsilon>0,C,Y0 with
V(Y)<=C*Y^(2-epsilon) for all Y>=Y0. This concerns phase increments and is
unchanged by all mass below the block, which contributes a common phase. It
does not assume atomicity, finite residual mass or a chosen limiting phase.
Its first unproved step is exactly this source upper estimate: [OPEN CORE].

Preliminary attack: positivity and cumulative monotonicity alone do not imply
the estimate; a continuous positive density can give a steadily rotating phase
with variance of order Y^2. The finite-packet obstruction likewise prevents
deducing it from bounded counting discrepancy. These are model obstructions,
not counterexamples to an arithmetic hW. Current searches locate fixed-phase,
summable-tail, sublinear-variation and finite-residual receivers, whose added
inputs cannot be assumed here. No closing source estimate was located, subject
to the recorded coverage warnings. Provisional verdict for the source claim:
SURVIVES PRELIMINARY ATTACK, with open proof core; no Lean assertion yet.

The transfer from this variance estimate to a fixed phase is classical, hence
BRIDGE/REDISCOVERED rather than the new research claim. For a unit-valued phase,
put m_Y=Y^(-1)*integral_(Y,2Y] p. Fubini gives
V(Y)=2*Y^2*(1-|m_Y|^2). At large Y, normalize m_Y to a unit kappa_Y. Then
integral|p-kappa_Y|^2=2Y*(1-|m_Y|)<=V(Y)/Y, and Cauchy--Schwarz gives local L1
error at most sqrt(C)*Y^(1-epsilon/2). Blocks at Y and 3Y/2 overlap in length
Y/2, so their centers differ by O(Y^(-epsilon/2)). The geometric chain of such
overlaps converges to one unit kappa; comparison with intermediate overlapping
blocks gives the same tail rate for every Y. Triangle inequality supplies the
assigned fixed-phase power saving, without preselecting theta. The source
variance estimate, not this alignment calculation, must be proved next.

If the conjecture is false for an actual hW, the counterexample would refute
WP05's universal lambda-rigidity target, not by itself the weaker existence-to-RH
problem. The cycle-8 theorem constrains such a source to recurrent quantitative
phase disorder. Keep these scopes distinct.

## Cycle 9: quantitative passage to an explicit interior line

The fixed-line reciprocal mean-square theorem does not prove circular variance
decay. Its quantifiers are `forall sigma>1/2, limit as T tends to infinity`;
neither the limit nor its coefficient energy is uniform at sigma=1/2+eta(T).
The period-defect alternative also adds no estimate: the three-term identity
already holds for every translation-invariant input. Lewis--Zagier's period
correspondence requires analytic continuation and growth across the cut. These
are rejected proof steps, not counterexamples to full positivity.

There is, however, a closed quantitative boundary-passage lemma. Write
`W=integral (1+r^2)^(-1) dmu(r)`, finite and nonnegative for the original
canonical measure. Set

    p_eta(y)=exp(2i Im sourcePrimitive(1/2+eta+iy)),
    p(y)=exp(i*pi*mu((-y,y])).

For Y>=1, eta>0 and h>0, the following estimate holds:

    integral_(Y,2Y] |p_eta(y)-p(y)| dy
      <= W*((4*pi*h+2*eta*Y/h)*(1+16*Y^2)+32*eta*Y^2).       (R)

Proof with all mass retained. The already proved vertical primitive identity
and Poisson representation identify the interior angle with
`integral K_eta(-y,y;r) dmu(r)`, where K is the arctangent window. The boundary
angle is the integral of `pi*1_{(-y,y]}(r)`. The complex exponential restricted
to imaginary real arguments is 1-Lipschitz. Thus its error is bounded by the
integral of the absolute scalar window error, and Tonelli allows integration
in y first. This avoids division by a boundary trace and does not require its
nonvanishing. All scalar errors are nonnegative and measurable.

For fixed |r|<=4Y, window error is at most pi everywhere. Outside the two sets
`|y-r|<=h` and `|y+r|<=h`, the arctangent tail estimate
`pi/2-arctan(x/eta)<=eta/x` for x>0 bounds it by 2eta/h. Each exceptional set
has y-length at most 2h. Its y-integral is therefore at most
`4*pi*h+2*eta*Y/h`. The mass of [-4Y,4Y] is at most `(1+16Y^2)*W`.

For |r|>4Y and y in (Y,2Y], the sharp indicator is zero. For every
t in [-y,y], |r-t|>=|r|/2 and r^2>=1. Consequently
`eta/(eta^2+(r-t)^2)<=8eta/(1+r^2)`. Integrating over t gives
`K_eta(-y,y;r)<=16eta*y/(1+r^2)<=32eta*Y/(1+r^2)`.
Its y-integral is at most `32eta*Y^2/(1+r^2)`. Integrating over r proves (R).
These same majorants prove the required integrability; no divergent signed
integral or exchange of conditionally convergent integrals occurs.

Taking eta=Y^(-8), h=Y^(-3), and using Y>=1 gives the explicit corollary

    integral_(Y,2Y] |p_(Y^-8)(y)-p(y)| dy <= (68*pi+66)*W/Y.  (R8)

Indeed 1+16Y^2<=17Y^2, the first product is at most
`68*pi/Y+34/Y^2`, and the last term is 32/Y^6. Endpoints are retained
pointwise in the indicator estimate; they need not be excluded beforehand.

Verdict: BRIDGE. This is a classical Poisson/BV estimate specialized to the
actual source, not new scientific knowledge or phase concentration. It pays
an explicit moving-boundary error with no atomicity or regularity assumption.
It does not infer a uniform critical-line reciprocal moment from a fixed-line
one. The hard next conjecture is the same power-saving circular variance for
`p_(Y^-8)`; (R8) changes its double-integral variance by at most a source
constant, since both phases have norm one. That arithmetic estimate remains
the OPEN CORE. Formalizing a mean-oscillation receiver alone would not pay it.

### Next arithmetic attack, after paying boundary passage

Write `m_eta(Y)=integral_(Y,2Y] p_eta(y) dy`, with eta=Y^-8. The exact source
claim is equivalently

    |m_eta(Y)|^2 >= Y^2-C*Y^(2-epsilon), epsilon>0.             [OPEN CORE]

The identity behind this reformulation is
`V_eta(Y)=2Y^2-2|m_eta(Y)|^2`, since |p_eta|=1. The perturbation estimate is
explicit: for unit p,q, the difference of their squared two-point distances
is at most `4*(|p(u)-q(u)|+|p(v)-q(v)|)`; integrating gives
`|V_p(Y)-V_q(Y)|<=8Y*integral_(Y,2Y]|p-q|`. Thus (R8) pays at most 8C.

The existing `G_eq_lineFactor_mul_cexp` identifies the actual completion with
`s(s-1)Gamma_R(s)*exp(producerLogZeta(s))` away from real height zero.
Consequently this problem concerns the normalized reflection ratio of that
actual product. The inspected logarithmic and moment estimates control the
real part of producerLogZeta, whereas the normalized reflection ratio retains
its imaginary part together with the archimedean phase. Substituting a modulus
bound for this correlation would be invalid. The next proof attempt must use
integer Dirichlet frequencies and that archimedean phase together; proving
another abstract phase-transfer implication is not the missing arithmetic work.

## Cycle 10: cancellation away from the critical boundary

Let H(s)=weilContinuation hW s and P=sourcePrimitive hW. For the original
source hW alone, there is Y0>=4 such that, for every Y>=Y0 and 0<eta<=1,

    |integral_Y^(2Y) exp(2 i Im P(1/2+eta+i t)) dt|
       <= 18 Y/(eta^2 log Y).                                      (C10)

This is an actual-source upper bound, but in the cancellation direction. It
excludes using fixed-width phase averages as near-maximal approximations to a
settled boundary phase. Verdict BRIDGE: Harnack/Caratheodory and integration by
parts are classical parent theories; no significant novelty claim. The
moving-line near-maximal mean at eta=Y^-8 remains OPEN CORE.

Dependency-closed paper proof:
1. Put M=sum_n |lam(n)|/n^2, finite by full positivity. The exact right-line
identity and the verified digamma bound give, for t>=4,

    Re H(2+i t) >= (log t)/2 - C0,
    C0=(log 2+log pi)/2+1+M.

Indeed |Re psi(1+i t/2)-log(t/2)|<=8/(t/2)^2<=2; both polar
real parts are nonnegative and |producerA(2+i t)|<=M. Choose
Y0=max(4,exp(4C0)). Then Re H(2+i t)>=(log t)/4 for t>=Y0.
2. The exact positive Poisson representation, including all mass components,
gives for 0<eta<=1

    Re H(1/2+eta+i t) >= (2eta/3) Re H(2+i t),

by the pointwise kernel inequality
eta/(eta^2+(r-t)^2)>=(2eta/3)*(3/2)/(9/4+(r-t)^2).
All integrals are finite by the existing source Poisson theorem. Therefore on
[Y,2Y], u(t)=Re H(1/2+eta+i t)>=(eta/6)log Y.
3. On the disc of radius eta about s=1/2+eta+i t, H is holomorphic with
nonnegative real part. The corpus Caratheodory difference estimate implies
|H(w)-H(s)|<=4 u(t)|w-s|/eta for |w-s|<eta/2. Passing to the
derivative gives |H'(s)|<=4u(t)/eta. Consequently u is continuously
differentiable and |u'(t)|<=4u(t)/eta. This local estimate remains valid
when u(t)=0 and uses no extra source hypothesis.
4. Set phi(t)=2 Im P(s), v(t)=phi'(t)=2u(t), L=eta log Y/3>0.
Then v>=L, |v'|<=4v/eta. The function B(t)=1/(i v(t)) satisfies
B*i*phi'=1, |B|<=1/L, |B'|=|v'|/v^2<=4/(eta L).
All functions are continuously differentiable on the integration interval.
The existing nonmonotone oscillatory integration-by-parts theorem gives

    |integral exp(i phi)| <= 2/L + Y*4/(eta L)
                           =6/(eta log Y)+12Y/(eta^2 log Y)
                           <=18Y/(eta^2 log Y),

because eta<=1<=Y. This proves C10 with no added arithmetic, support,
atomicity, boundary-continuity or concentration assumption.

Positive survivor: uniformly for widths with eta(Y)^2 log Y tending to
infinity, the normalized phase mean tends to zero. A hypothetical settled
boundary phase cannot be transferred through that region with o(Y) L1 error:
triangle inequality would instead force its normalized mean to have modulus
tending to one. This does not refute settlement at eta=Y^-8; it identifies a
necessary singular dependence on width. We retain and formalize C10 itself,
not a false uniform-limit interchange.

## Cycle 11: arithmetic rational modes, exact conjecture and first attack

Given the audited internal/external frontier, the new structural conjecture is
that full source positivity forces additive equidistribution of the actual
forward coefficients, before any Euler product or functional equation is
available. Put a(n)=sourceCoeff(lam)(n), B=sourceCompletion(hW)(1), and
S(r,q,N)=sum_(1<=n<=N) a(n)*exp(2*pi*i*r*n/q). Conjecture C11:

    for every epsilon>0 there are A>=0 and C>=0 such that, for all
    integers q>=1, 0<=r<q, N>=1,
    |S(r,q,N)-[r=0]*B*N| <= C*q^A*N^(1/2+epsilon).

Here B=2*betaG(sourceCompletion hW); the corpus defines betaG(G)=G(1)/2,
so the theta subtraction coefficient must not be used as the Perron residue.
Quantifiers are source-only: hW is the original assigned input. No twist
continuation, periodicity, multiplicativity, or coefficient estimate is an
added premise. This is a falsifiable arithmetic law, not a restatement of a
phase upper bound. Its truth would control each rational saddle's forward
coefficient sum. Even C11 would not by itself pay the moving-line reciprocal
denominator tail; that remains an independent obligation.

Competing conjecture: some actual full-positive source retains a nonprincipal
rational mean. Such a source would obstruct this mechanism and WP05's proposed
rigidity. A generic sequence is not a counterexample to the source conjecture.

First attacks:
1. Critical forward energy O(log N) does not imply C11. The elementary sequence
   a(n)=1+c*(-1)^n for n>=2, a(1)=1, with fixed nonzero real c, has that energy order and a
   nonzero linear parity mean. It has not been shown to satisfy full positivity.
2. Even a square-root bound for the untwisted partial sum would not suffice.
   Abel summation against exp(2*pi*i*r*x/q) loses an integral of its derivative
   times the partial-sum error, of size O((r/q)*N^(3/2+epsilon)). Do not claim
   nonprincipal cancellation from the untwisted Perron contour.
3. The actual all-cutoff Toeplitz relaxation has a sharp sparse construction
   (WeilWorkSingularArithmeticToeplitzSharpness, capstone checked directly).
   Strengthening that extracted relaxation alone is not the missing mechanism.
4. Existing rational saddle blocks cancel constant weights; replacing those
   weights by the actual a(n) requires C11 or a different genuine source input.
5. The audited ratios formulas assume arithmetic correlations/GRH. Booker's
   degree-one classification assumes discrete, almost everywhere integral
   multiplicities. Neither proves C11 from the present source.

Verdict so far: SURVIVES PRELIMINARY ATTACK, not proved. [OPEN CORE]: obtain
nonprincipal rational cancellation from the original full-positive quadratic
form, retaining its archimedean and polar terms. The q=1 Perron consequence
also needs a complete contour/truncation proof before use. No cycle-11 Lean
code is authorized by a closed paper proof yet. The original eta=Y^-8
near-maximal phase mean remains the main open target.

A stronger attack removes a tempting fake source counterexample. Normalize
periodic coefficients by a_c(n)=(1+c*(-1)^n)/(1-c), c!=0, |c|<1, so a_c(1)=1.
Their right-line Dirichlet series is (1+d*2^(-s))*zeta(s), d=2c/(1-c).
Where the logarithm is absolutely convergent, its logarithmic derivative
changes Lambda only at powers of2. The existing full-source common-ratio
rigidity theorem then forces every such change to vanish, hence d=0, a
contradiction. For parameters violating right-line convergence/zero-freeness
there is already no admissible source. Thus this normalized periodic family
cannot refute C11. This uses the actual corpus obstruction, not an assumption
of RH or a numerical check. It does not exclude arbitrary nonperiodic sources
with a rational bias, so C11 remains OPEN CORE. No new Lean wrapper of the
existing common-ratio theorem is warranted.

## Cycle12: exact atom exponent retained by every polynomial reciprocal tail

Let b_n be the literal producerMobius coefficients (with lambda filtered below2),
G the reciprocal continuation supplied by the existing atom-order theorem, and
s_h=1/2+h+i*a. Write P_N(h)=sum_(1<=n<=N) b_n*n^(-s_h), E_N(h)=G(s_h)-P_N(h).
For every fixed real a, A>=0 and epsilon>0, there is h0>0 such that

    0<h<h0, N<=h^(-A) implies
    |log(1+|E_N(h)|)/log(1/h)-mu.real({a})|<epsilon.          (C12)

Only original hW is a source input. Every ordinate, including zero-mass ones,
is retained. Neither atom existence, positive atom mass, atomicity nor a growth
hypothesis on reciprocal coefficients is added. This is uniform over all
prefix lengths in the indicated range, but a and A are fixed before h0.

Paper proof, dependency closed:
1. For every delta>0 the literal reciprocal series converges at
   s_delta=1/2+delta+i*a (reciprocal_dirichletConvergesAt). Consequently its
   coefficient partial sums A_k at that point satisfy |A_k|<=K_delta uniformly.
   For 0<h<=delta the ratio of the summands at s_h and s_delta is the
   nonnegative increasing real weight n^(delta-h). Finite Abel summation gives
   |P_N(h)|<=(2*N^(delta-h)-1)*K_delta for N>=1; P_0=0.
   Thus |P_N(h)|<=2*K_delta*(N+1)^delta, uniformly in 0<h<=delta and all N.
   This argument is conditional convergence, not a termwise absolute estimate.
2. If h<1 and N<=h^(-A), then N+1<=2*h^(-A). Hence
   1+|P_N(h)|<=(1+2^(delta+1)*K_delta)*h^(-A*delta).
   Therefore 0<=log(1+|P_N(h)|)/log(1/h)
   <= log(1+2^(delta+1)*K_delta)/log(1/h)+A*delta.
   Given any tolerance choose delta smaller than tolerance/(2*(A+1)), then
   h small enough. The normalized log of every prefix tends uniformly to0.
3. Existing tendsto_log_norm_reciprocalZeta_div_log gives
   log|G(s_h)|/log(1/h)->m=mu.real({a})>=0. For every x>=0,
   max(0,log x)<=log(1+x)<=log2+max(0,log x), with x=0 checked separately.
   Thus log(1+|G(s_h)|)/log(1/h)->m. All logarithms are divided only for h<1.
4. Triangle inequalities in both directions imply
   1+|G|<=(1+|E_N|)*(1+|P_N|) and
   1+|E_N|<=(1+|G|)*(1+|P_N|). Taking logarithms gives

   |log(1+|E_N|)-log(1+|G|)|<=log(1+|P_N|).

   Steps2--3 prove C12 uniformly in N. This also handles m=0; no branch,
   integer multiplicity, pole order or division by G is needed.

Verdict: BRIDGE. Abel/Cahen partial summation and the already proved source
atom-order law supply the result. No significant scientific novelty claim.
The positive survivor is the exact exponent of the complete remaining tail,
not just failure of an approximation bound. In particular, at every positive
atom polynomial prefixes leave an error with the full positive blow-up exponent.
This does not rule out a phase argument which retains that tail. It also does
not prove a uniform obstruction on a growing height window a in[Y,2Y]; exchanging
these quantifiers would be unjustified. The C11 arithmetic correlation and the
eta=Y^-8 phase-concentration OPEN CORE remain unchanged.

Novelty attack: the corpus search returns the atom-order theorem and fixed-line
tail/mean-square bounds, but no inspected statement already asserts C12.
Coverage is not a novelty certificate. Classical Abel summation (Hardy--Riesz;
Knill's author notes, Lemma1 and Cahen proof) is an immediate parent mechanism.
Defant--Schoolmann's boundary Riesz results concern different summation means
and retain boundary hypotheses; they do not provide our moving-height source
phase conclusion. The result is being formalized only as the exact positive
survivor of the short-reciprocal-prefix shortcut, not as the main solution.

## Cycle13: first arithmetic parity test (OPEN CORE)

C12 does not settle phase or exclude phase-only approximations: it retains an
exact invariant of the complete reciprocal remainder. Returning to the
arithmetic source, isolate the weakest nonprincipal rational mode from C11.
Write a(n)=sourceCoeff lam n for the original forward coefficients. Conjecture:

    (1/N) * sum_(1<=n<=N) (-1)^n a(n) -> 0, as N->infinity,

from the original hW alone. No rate, periodicity, Euler product, multiplicative
coefficients, or comparison with von Mangoldt is a premise. This is a necessary
first test of C11, not a replacement for its quantitative target or WP05's
moving-line phase estimate. Together with the principal-mode mean asserted by
C11, it would equidistribute the forward mass between even and odd indices.
That ordinary untwisted mean has not been verified as a corpus theorem here;
the pole residue and a smoothed mean must not be confused with that conclusion.

Falsifier: an actual full-positive source for which these normalized alternating
sums fail to tend to zero. A generic biased sequence or an inadmissible periodic
toy is not a falsifier. Previously audited exact period-two deformations reduce
to geometric-support logarithmic deviations and are already excluded by
CommonRatioRigidity. That does not exclude a nonperiodic source with parity bias.

Attack and applicability audit: the new deep search is partial (runtime and
Qdrant deadlines). Available parity-energy hits concern reflection channels
and an RH-equivalent energy comparison, not arithmetic parity of a(n).
Minorant, majorant, regular-deviation, finite-support and summability rigidity
hits all retain additional premises. The prime-multiples laws concern lam,
with sign/size restrictions; no source-preserving projection from a(n)'s parity
mean has been obtained. The proposed ingredient set does not close this gap.
Saias--Weingartner's checked periodic classification retains exact periodicity.
No external classification is applied to mere mean bias.

Verdict: OPEN CORE, no novelty or proof claim; no Lean wrapper. Next attack the
exact passage from a nonzero parity mean to a full-cone conductor/polar defect,
or construct an actual admissible counterexample. Keep the full reciprocal
tail and all canonical measure components. This is a focused continuation of
C11, not a new solved route.

## Cycles13--14 audit: parity and variance remain open

The odd-index indicator is completely multiplicative. Hence filtering the
Dirichlet exponential to odd indices is exactly exponentiating the odd part
of its logarithmic coefficients. On Re(s)>1, write F=exp(L),
F_odd=exp(L_odd); then F_alt=F-2F_odd and F_alt/F=1-2exp(-L_even).
This identity supplies no full positivity for the filtered source. The checked
prime-multiples results require sign or local-mass inputs. In particular no
argument here forces the even logarithmic part to log2 at the pole.
C13 survives this attack; neither an admissible counterexample nor a proof
has been obtained.

A stronger possible C14 is the exact ordinary variance law
N^(-1) sum_(1<=n<=N)|a(n)-B|^2 -> 0, B=sourceCompletion hW 1.
Cauchy--Schwarz would imply C13, since the alternating sum of the constant B
is bounded. This is stronger than merely specifying a second-moment limit
without a verified first moment. Corpus search exposed WP03 cycle20's already
open logarithmic pole-mode variance conjecture. C14 is an ordinary-mean
strengthening of that existing question, not a new saturation mechanism.
The Toeplitz/Gronwall bound has an unspecified constant and does not prove it.
Verdict: SURVIVES PRELIMINARY ATTACK, [OPEN CORE] sharp saturation from hW.

Parent-theory audit: Perelli's extended Selberg class and Kaczorowski--Perelli's
2026 standard-twist framework retain global continuation and functional
equations. Lewis--Zagier period correspondence retains the relevant analytic
three-term relation and growth conditions. The canonical L1 trace alone does
not supply these inputs. No parent classification has been applied here.

## Cycle15: exact ordinary forward mean (BRIDGE, paper proof)

This repairs the unverified principal-mode assertion in C11. Put a=sourceCoeff
lam, G=sourceCompletion hW and B=G(1). The exact statement is: for each eps>0
there is C>=0 such that, for every natural N,

    |sum_(n=0..N) a(n) - B*N| <= C*(N+1)^(1/2+eps).

Only the original full-positive source is an input. In particular this neither
assumes nor proves B=1. a(0)=0. The centered coefficients a(n)-B consequently
have ordinarily convergent Dirichlet series on Re(s)>1/2, by finite Abel
summation and the strict exponent gap. No sign hypothesis is used.

Dependency-closed proof:
1. Define A(s)=G(s)/(s*Gamma_R(s)) on the open half-plane Re(s)>1/2.
   The denominator is nonzero there, G is holomorphic, and A(1)=B since
   Gamma_R(1)=1. The divided difference R(s)=dslope A 1 s is holomorphic
   on the same half-plane, including its removable value at1. Away from1,
   R(s)=F(s)-B/(s-1), where F(s)=G(s)/(s*(s-1)*Gamma_R(s)).
   Existing sourceCompletion_eq_bigG and sourceCoeff_LSeries identify F
   with the absolutely convergent forward series on Re(s)>1.
2. For every q>0 and exponent a>0, R has a bound
   |R(s)|<=K*(2+|Im(s)|)^a on 1/2+q<=Re(s)<=2. For |Im(s)|>=2 and
   Re(s)<=3/2, use exists_quantizationProdF_subpolynomial: the canonical
   completion there is definitionally G. For Re(s)>=3/2, absolute
   convergence at3/2 bounds F by the finite constant
   L=sum_n |LSeries.term a (3/2) n|, since each term norm decreases with
   real part. In both regions |B/(s-1)|<=|B|. On the remaining compact
   rectangle |Im(s)|<=2, continuity of R supplies a finite bound. Increasing
   K covers both ranges since (2+|Im(s)|)^a>=1. This uses the entire original
   source; no boundary extension, arithmetic projection or atom removal.
3. Choose q=min(eps/4,1/4), exponent a=q/2 and c=1/2+q. For N>=1 take
   the existing smoothWeight N (1/2), whose values on natural indices equal
   the sharp cutoff. Absolute convergence at2 gives the exact Mellin-Perron
   identity. Split F=B/(s-1)+R. The existing pole integral equals
   2*pi*J_N, J_N=integral_(1,infinity) smoothWeight N (1/2), with
   |J_N-N|<=2. Multiply this identity by B. Shift the R integral from2
   to c using its holomorphy and the step2 power bound.
4. The checked fractional Mellin estimate, with 0<a<q<=1, bounds the
   remaining integral by a fixed constant times
   (N+1/2)^c + (2N+1)^q*(N+1/2)^c. Since c+q<=1/2+eps and N+1>=1,
   this is O((N+1)^(1/2+eps)). The pole error is at most2|B|. N=0 is
   immediate. This proves the displayed statement with a nonnegative C.
5. For Re(s)>1/2 choose eps=(Re(s)-1/2)/2. The centered partial sums
   are bounded with exponent1/2+eps<Re(s); the existing finite-Abel
   convergence theorem applies. The same estimate with eps<1/2 gives
   the ordinary mean B. This last limit is a consequence, not a premise.

Attack verdict: BRIDGE, not significant scientific novelty. This is the
classical pole-plus-Perron mechanism already used by WP03 for the original
logarithmic source and its reciprocal. Ramaré, Modified truncated Perron
formulae (2016), introduction and Theorem1.1, confirms the parent inversion
framework and the need to control the cutoff boundary. Here the existing
half-width smooth cutoff handles that boundary exactly. New Lean content
will close a concrete missing link; C13/C14 and WP05 settlement remain open.

## Cycle16: prime-deletion residue law (OPEN CORE)

C15 identifies the principal forward density B. It leaves every nonprincipal
arithmetic projection unpaid. Given this exact frontier, the next conjecture
is a prime-deletion law at the pole, without assuming an Euler product:

    For every prime p and every original full-positive lam,
    lim_(sigma down to1) sum_(n>=2, p divides n)
      lam(n)/(log(n)*n^sigma) = -log(1-1/p).

Each series is absolutely convergent for sigma>1 by the actual source
summability. At p=2 the target is log2. The claim concerns the original signed
lam, with no local-mass, nonnegativity, prime-power-support or rigidity input.
A falsifier must be an actual hW source with a different or nonexistent limit.
Competing possibility: an admissible source preserves the principal pole but
has a different prime-deletion ratio. No such source has been constructed.

Why this is structurally meaningful: the indicator of p not dividing n is
completely multiplicative, so it commutes with Dirichlet convolution and its
exponential. If L_p is the series above, then exactly on Re(s)>1,

    F_coprime-p(s)/F(s) = exp(-L_p(s)).

Thus C16 would fix this ratio at1-1/p at the pole for every prime, even before
any coefficient multiplicativity or actual Euler factor is available. At p=2,
C13 plus C15 would imply C16 by ordinary Abelian summation: the odd forward
mean would be B/2, hence F_odd/F->1/2; real logarithms then give L_2->log2.
The converse is not asserted. A pole ratio alone does not give an ordinary
alternating mean without a further Tauberian argument.

Attack: residue search87179 and even-log search80428 completed, partial=false,
with unmeasured semantic coverage/background refresh still reported. Neither
checked result removes the local-mass/sign premises in the multiples law.
Harmonic-pinning uniqueness additionally requires notch-smallness and a pinned
constant (or further multiples summability). Suggested xi log-derivative and
residue-symbol chains do not discharge these. The index also returned our
then-pending C15 theorem as source_only; that self-hit was excluded as proof
of any new residue normalization.

Primary-parent audit: Booker's L-functions as distributions (arXiv:1308.3067v2,
2015), Definition1.3(A3), requires discrete spectral support and integrality
apart from finitely many masses. Those are not consequences established for
our full canonical measure, so its low-degree classification cannot simply
be imported. The Selberg and period-function parents audited above likewise
retain unpaid hypotheses. C16 asks for one consequence without paying for
that whole classification. Verdict: SURVIVES PRELIMINARY ATTACK; no novelty
claim or closed proof. [OPEN CORE]: obtain the exact prime-deletion constant
from the full signed source form, rather than a conditional boundedness law.
Next inspect the fibre test behind multiples-of-prime estimates and determine
whether logarithmic averaging pays its local-mass cost. If that shortcut fails,
retain its exact positive boundary; do not substitute generic biased sequences
for an admissible counterexample or add C16 as a Lean premise.

C16 fibre-cost audit: `exists_ramp_scale_bound_bounded_of` in
`WeilLittleOVonMangoldtRigidity.lean` charges absolute values in its defect
pairing and in all three notch bounds. In particular its harmonic and square-root
costs are bounds on sums of absolute deviation, not on signed partial sums.
The full-source `exists_twistFibre_level_bound` retains that NotchBounded input.
C15 therefore cannot discharge the input merely by Abel summation of its signed
forward remainder; the coefficients are also different from the logarithmic
deviation used in the fibre test. This identifies an unsupported shortcut,
not a counterexample or a no-go theorem for C16. A next attack must either
derive the required absolute cost from hW or replace the error estimate itself
with a justified signed pairing before applying the fibre argument.

Oliver, Notes on Low Degree L-Data (arXiv:1601.05009), Definition2.1 and
section4, does not remove this gap: discrete multiplicity and the finite
nonintegral exception remain inputs to its continuation/classification
framework. No claim of applicability to an arbitrary canonical boundary
measure is made.

## Cycle17: signed-cost and self-pairing attacks

The exact notch error, before absolute values, involves rational-twist
off-diagonal terms. The checked envelope in ZetaNotchRefinedEnvelope has a
near-dual contribution of size sqrt(L)*log(L) on n<=2*K0^3*L. No bound on its
signed sum follows from the principal forward mean alone. Moreover v in the
notch is (lam-Lambda)/sqrt(n), not the forward coefficient remainder.
WP03 supplies ordinary convergence of sum(lam-Lambda)/n, but not absolute
local mass or convergence of every divisibility subseries. No shortcut across
either distinction was accepted.

The proposed self-pairing with the forward coefficients is REDISCOVERED:
WeilSingularArithmetic.forwardCoeff_log_convolution and
exists_forwardCoeff_log_moment_le already insert the exact logarithmic
convolution into the Weil--Toeplitz form. Their resulting critical energy
O(log N) has an unspecified constant. It does not give centered variance zero.

A concrete attack on that latter inference uses a_c(n)=1+c*1_(2|n), n>=1,
0<c<1. Its mean is B_c=1+c/2 with O(1) summatory error, while its alternating
mean is c/2 and its centered square is identically c^2/4. Its critical energy
is (1+c+c^2/2)*log N+O(1), whereas B_c^2=1+c+c^2/4. Thus even bounded
summatory error plus logarithmic critical energy does not force saturation.
On Re(s)>1, F_c= zeta(s)*(1+c*2^(-s)); its logarithmic coefficient deviation
is (-1)^(k-1)*c^k*log2 at n=2^k and zero elsewhere. The prime-deletion
logarithmic limit is log2+log(1+c/2), not log2. This is NOT an hW
counterexample: the existing common-ratio rigidity theorem excludes precisely
this nonzero deviation. The positive survivor is the already-formalized
common-ratio rigidity, not a new theorem to duplicate. Verdict for the
mean-plus-energy shortcut: FALSE; C13/C16 themselves remain open.

## Cycle18: complex-power energy boundary

Given the exact internal and external frontier, the stronger conjecture to
attack is a phase-sensitive critical energy law for complex source powers.
For z in C define a_z=exp_*(z*logZetaCoeff(lam_0)), with lam_0 truncated below2.
This uses the literal Dirichlet exponential, so its branch is fixed by the
original absolutely convergent logarithmic series, not by a pointwise choice
of complex logarithm. Proposed sharp law:

    For every original hW, every z in C and eps>0,
    sum_(1<=n<=N)|a_z(n)|^2/n <= C_(hW,z,eps)*(1+log N)^(|z|^2+eps).

In particular imaginary z would control powers sensitive to argument, while
z=-1 would give critical reciprocal energy currently missing from the checked
source estimates. Neither implication to phase settlement nor the sharp law
is claimed proved. A falsifier must use an actual hW source; finite Euler
deformations excluded by hW are not falsifiers. [OPEN CORE]: obtain the
imaginary/negative-power estimate from the full source, beyond the one-sided
Toeplitz test. This does not replace the constant-phase WP05 target.

There is a closed weaker paper range, to be audited before new Lean. Put
r=2*Re(z)/|z|^2. For |z-1|<1, r>1, and the Toeplitz mechanism gives

    sum_(1<=n<=N)|a_z(n)|^2/n
      <= C_(hW,z)*(1+log N)^(1/(r-1)).

Dependency-closed argument for this weaker range:
1. Absolute convergence of lam on Re(s)>1 gives absolute convergence of
   z*logZetaCoeff(lam_0), hence of a_z and its Dirichlet series
   exp(z*L(s)). Differentiate there and use Dirichlet-series injectivity:
   lam_0*a_z=(log(n)/z)*a_z(n). z is nonzero in the stated disk.
2. Insert c(n)=1_(n<=N)*a_z(n)/sqrt(n) into the checked Weil--Toeplitz
   ceiling. Swap the finite divisor sums. Its inner expression is the real
   part of a_z(n)*conj((lam_0*a_z)(n))/n, equal to
   Re(1/z)*log(n)*|a_z(n)|^2/n, since lam is real. Thus r*S_N<=(log N+C)*E_N,
   where w_n=|a_z(n)|^2/n, E_N=sum w_n, S_N=sum log(n)*w_n, and C>=0.
3. Let H_N=log(N)*E_N-S_N>=0, c=C/(r-1), alpha=r/(r-1)>1. Then
   (log N-c)*E_N<=alpha*H_N and
   H_(N+1)=H_N+(log(N+1)-log N)*E_N. Choose N0 with log N0>c and
   K=H_N0/(log N0-c)^alpha. Induction, using convexity of x^alpha on x>0,
   gives H_N<=K*(log N-c)^alpha for N>=N0: the increment is at most
   alpha*K*(log N-c)^(alpha-1)*(log(N+1)-log N), which the corresponding
   power increment dominates. Consequently E_N<=alpha*K*(log N-c)^(alpha-1).
4. Here alpha-1=1/(r-1)=|z|^2/(2Re(z)-|z|^2). The finitely many smaller
   N are absorbed by E_N0, and c>=0 allows replacement by 1+log N.
   No spectral decomposition, coefficient sign or new source premise enters.

Verdict for this weaker range: BRIDGE, a parameter extension of the existing
Toeplitz/log-moment argument, not demonstrated scientific novelty. For z=it,
Re(1/z)=0, so the same test gives no energy control at all; merely retaining
the complex algebra does not solve the phase direction. The sharp all-z law
is still under corpus/primary-parent attack, with no Lean assertion added.

Further attack: even sharp logarithmic power energies would not alone identify
the arithmetic source. Finite Euler perturbations can preserve such growth
while altering the logarithmic prime-fibre constant; full positivity excludes
the checked common-ratio perturbation by a separate rigidity argument. Thus
the proposed sharp law is not itself a proved phase detector.

## Cycle19 entry: imaginary powers versus interior growth

Focus the sharp C18 conjecture at z=it, t real: for every eps>0 and original
hW, the critical coefficient energy should be O((1+log N)^(t^2+eps)). It is
exact and falsifiable by an actual hW source. Its competing failure is an
actual source with energy exceeding every such bound for some t and eps.
Neither candidate has a proof. [OPEN CORE]: a source-derived critical norm
bound beyond the zero real-part coefficient in the Toeplitz pairing.

Do not weaken this to subpower vertical growth of exp(it L). The existing
exists_logZeta_lindelof controls the norm of the continued logarithm itself by
C(log(|height|+3))^theta on each strict inner strip, theta<1. Multiplying by
any fixed complex z and exponentiating therefore already gives subpower
vertical growth of that branch. This is REDISCOVERED and does not give a
logarithmic critical coefficient-energy bound or moving-boundary uniformity.
The gap is the approach to the critical line, not fixed-parameter interior
holomorphy. No extra Lean lemma is added for this immediate parent consequence.

Alarcon Athens, arXiv:2101.07402v5, explicitly treats powers of zeta with
multiplicative coefficients constructed from prime factorizations. This is
an algebraic parent for the zeta case, not a producer of multiplicativity for
the arbitrary full-positive source. Roy's 2025 LSD framework likewise requires
analytic product structure not obtained here. No novelty follows from the
failure of these parents to discharge the exact missing source input.

## Cycle20 attack: logarithmic coefficient energy

The unrestricted candidate sum_(2<=n<=N) lam(n)^2/(n*log(n)^2)=O(log log N)
remains OPEN. Two working claims required correction. First, an assumed
square-sum ceiling would indeed provide this by Abel summation. Second, the
actual parent ceiling is only on primitive sets, not all integers. Its
prime-restricted consequence is REDISCOVERED, but the unrestricted one has
not thereby been proved. For an arbitrary nonnegative square-mass function,
the conditional Abel implication is exact: if
A(x)=sum_(2<=n<=x)lam(n)^2/n <= C(1+log x)^2, then

  sum_(2<=n<=N) lam(n)^2/(n*log(n)^2)
    = A(N)/log(N)^2 + integral_2^N 2*A(x)/(x*log(x)^3) dx,

with the standard step-function endpoint convention. The right side is
O(1+log log N). The verified original-source parent
WeilMeanSquare.exists_sum_sq_div_le_of_primitive only licenses this argument
after restricting A to primes (or a fixed primitive support). Its dyadic
law for all integers gives an O(log N) bound on the logarithmic energy by
block summation, not O(log log N). The all-integer square-mass law in
ToeplitzSharpness belongs to its particular prime-supported construction,
not to every hW. Both corrections were posted in chat; no new Lean assertion
depended on either erroneous source inference.

Relentless interrogation now asks for the sharp source constant instead:
for every original hW and eps>0, there exists N0 such that N>=N0 implies

  sum_(2<=n<=N) lam(n)^2/(n*log(n)^2) <= (1+eps)*log log N.

This is a provisional exact conjecture under corpus/parent attack, not a
closed theorem. It would constrain arithmetic variance at the zeta constant
without postulating prime support or multiplicativity. Its falsifier would
be an actual hW source with larger normalized limsup. No implication from
this second-order statement to imaginary exponential moments or WP05 phase
settlement is asserted. [OPEN CORE]: sharpen the source variance constant;
the verified prime-only ceiling neither fixes that sharp constant nor pays
the composite contribution. Parent source eligibility must precede any
further asymptotic inference.

## Cycle21 entry: source-derived exponential moments

Given the exact refreshed frontier, the structural conjecture is a Bohr
exponential-moment law, not a direct transplant of the circle inequality.
For N>=2 let P_N be primes<=N, use normalized Haar probability on the finite
torus T^(P_N), and write chi_n(omega)=product_(p|n)omega_p^(v_p(n)). Define

  L_N(omega)=sum_(2<=n<=N) lam(n)/(sqrt(n)*log(n))*chi_n(omega).

Conjecture: for every original hW, every fixed z in C, and eps>0, there is
C>=0 such that for all N>=2,

  integral exp(2*Re(z*L_N(omega))) dHaar(omega)
    <= C*(1+log N)^(|z|^2+eps).

Every composite coefficient is retained. The exact factorization of integer
frequencies defines the torus; no multiplicativity of lam is postulated.
If true, Parseval for exp(zL_N) bounds the original a_z coefficients through
N, since convolution products contributing to those indices use only
logarithmic coefficients throughN. Thus it would imply C18's sharp energy
law and C19's imaginary range. It does not yet imply WP05 settlement.

The competing falsifier is an actual full-positive source whose finite-torus
exponential moments violate this bound for fixed z,eps. Prime-only estimates,
signed means and fixed-strip logarithmic bounds do not pay this input.
[OPEN CORE]: derive the complete exponential-moment budget from the full
Weil test cone, controlling mixed composite correlations. Literature parents
require Euler structure or an already-controlled logarithmic Sobolev norm.
No such input is added as a premise. This conjecture is entering the exact
corpus/primary-parent attack; no proof or novelty verdict is claimed yet.

C21 preliminary verdict: SURVIVES PRELIMINARY ATTACK as an open conjecture,
not established novelty. The direct corpus producer
WeilConeSoundararajanMoments.exists_setIntegral_exp_mul_le additionally
assumes both summability of restWeight and |lam(n)|<=kappa*log(n). It gives
a height moment, not this complete finite-torus norm. SteinhausLogTailMoment
is an Euler prime-power model and cannot remove arbitrary mixed composites.
The deep search's generic exponential-type/log-coefficient recipe gives
neither the uniform cutoff budget nor its sharp exponent; rejected.

One proposed shortcut also fails to supply a source: arbitrary prime-phase
twists of lam are not known full-positive with the original fixed pole and
archimedean datum. Density of finite phase orbits alone gives no uniform
control of the accompanying height-dependent archimedean cost. Any use of
randomized tests must retain that cost and the original unmodified hW.
Phase5 remains incomplete at the source exponential-moment estimate; no
dependent Lean assertion has been introduced. Next attack the exact mixed
composite contribution and its required full-source payment.

## Cycle22: isolate the complete composite logarithm

The new exact candidate is uniform exponential integrability of the composite
part, without deleting any non-prime-power terms. With C21's characters put

  H_N = sum_(2<=n<=N, n not prime) lam(n)/(sqrt(n)*log(n))*chi_n.

C22 asserts: for every original hW and z in C there exists C_z such that
integral exp(2 Re(z H_N)) <= C_z for every N>=2. The competing possibility is
an actual full-positive source with an unbounded composite exponential moment
for some fixed z. Neither direction is proved. This is a structural source
conjecture, not a claim of novelty for the Euler-model case.

Even C22 would not by itself prove C21. If the additional *source theorem*
sum_(p<=N) lam(p)^2/(p log(p)^2) <= (1+o(1))*log log N were obtained, the
independent prime characters give the required prime exponential bound:
the circle integral of exp(2 Re(w X)) is
sum_(k>=0) |w|^(2k)/(k!)^2 <= exp(|w|^2). Holder with exponents r>1 and
r/(r-1) then combines the prime and composite bounds; choose r sufficiently
close to1 and absorb the small prime-variance slack into epsilon. This
conditional calculation identifies two missing producers; it adds neither
as a Lean premise nor presents them as consequences of hW.

Attack verdict: SURVIVES PRELIMINARY ATTACK, with [OPEN CORE] at the complete
composite exponential moment. SteinhausLogTailMoment bounds only the Euler
prime-power tail's second moment. Independence of distinct primes does not
make the general composite characters independent. The original-source
Soundararajan receiver still requires restWeight and a coefficient bound.
The full-cone log-square rigidity theorem has no 1/n in its deviation norm,
so this weaker critical norm cannot be fed to that theorem. The refreshed
deep search's coefficient-sign proposal was rejected after reading its full
premises. No dependency-closed source proof or new Lean theorem resulted.

## Cycle23: audit the Gamma energy observable

The exact existing source identity is, for y>0,

  2 O(y) = (U(y)-g(y)) A(-y),

where O=paperGammaOdd(remainderTrace hW), U=canonicalPhase hW,
g=paperGammaPhase, and A=paperUnsubtractedTrace hW. The multiplier g is the
quotient GammaR(-1/2+iy)/GammaR(-1/2-iy), chosen to fix the actual pole
profile. It is not the target constant lockConstant(theta).

Consequently, a proposed inference from recovery or zero Gamma-odd energy
to settled constant phase is not licensed. The deep search suggested exactly
this missing 'zero odd component' step; its identity does not prove it.
The correct constant-phase observable retains the counterterm:

  2 O(y) - (c-g(y)) A(-y) = (U(y)-c) A(-y),  c=lockConstant(theta).

This is a dependency-closed algebraic consequence of the existing
paperGammaOdd_phase_discrepancy, not a new scientific result. The strongest
positive survivor is the corrected identity, already contained in the parent
algebra; verdict REDISCOVERED. No redundant Lean leaf is added. No actual hW
counterexample to settlement, and no theorem asserting positive Gamma-odd
energy for every hW, has been established here.

There is a second missing transfer: the native energy is weighted by |A|^2.
Finite weighted energy and L1/L2 boundary recovery do not supply an unweighted
dyadic phase estimate without quantitative control of small |A|. The known
Littlewood bound is an upper amplitude bound, not the required lower bound.
Thus this detour has not improved the original canonical phase budget.

## Cycle24 entry: the first arithmetic resonance beyond variance

Return to the actual signed source. Put b_n=lam(n)/(sqrt(n)*log(n)) for n>=2.
The next falsifiable conjecture is the uniform signed cubic budget

  exists C>=0, forall N>=2,
  |sum_(a,b>=2, ab<=N)
      lam(a)*lam(b)*lam(ab)/(a*b*log(a)*log(b)*log(a*b))| <= C.

All ordered factorizations and all composite terms remain. No sign or Euler
support is assumed. Its falsifier is an actual original full-positive source
whose signed cubic sums are unbounded. For C21's finite logarithm L_N,
character orthogonality gives the sum exactly as integral L_N^2 conj(L_N).
For real t, the coefficient of t^3 in
log integral exp(2t Re L_N) is precisely this real sum: the pure holomorphic
moments vanish, and expanding (L_N+conj L_N)^3 contributes six times the
sum before division by3!. This identity is classical bookkeeping, not the
conjectured new source bound.

This exposes the first correlation omitted by a variance-only argument.
It is not asserted to imply C21 or WP05 by itself. [OPEN CORE]: use the full
Weil test cone to control this signed multiplicative correlation, beyond
primitive-set square mass and the existing two-prime completion. The new
source statement is entering the exact corpus/primary-parent attack.

C24 first attack: the principal signed mean and even a logarithmic pointwise
coefficient bound do not imply it. Define chi_3(n) as0,1,-1 according as n
mod3 is0,1,2, and set lambda_test(n)=1+chi_3(n)*log n for n>=2. The character
is completely multiplicative and its partial sums are bounded. Abel summation
therefore gives sum_(2<=n<=N) lambda_test(n)=N+O(log N), and
|lambda_test(n)|<=1+log n. These are paper identities, not a proposed hW.

Expanding the cubic sum, its term with three logarithmic factors is
sum_(a,b>=2,ab<=N,3 does not divide ab)1/(ab). Since
sum_(2<=n<=x,3 does not divide n)1/n=(2/3)log x+O(1), another Abel summation
gives (2/9)(log N)^2+O(log N) for this term. Each of the other seven terms
has at least one denominator log a, log b or log(ab); discard its bounded
character factors, bound any further inverse logarithms by powers of
1/log2, and use
sum_(a<=N)1/(a log a) * sum_(b<=N/a)1/b=O(log N log log N).
Thus the full signed cubic sum is
(2/9)(log N)^2+O(log N log log N), and is unbounded.

This kills only the mean-plus-size shortcut. No primitive-set law, full
Toeplitz ceiling, source interior-growth bound, or full positivity has been
proved for lambda_test. In particular it is not a counterexample to C24.
The full-source correlation law remains the exact open claim; its proof must
use source information beyond those two elementary estimates.

C24 preliminary verdict: SURVIVES PRELIMINARY ATTACK, not a novelty claim.
The complete source search returned no applicable cubic producer; its recipe
uses an unrelated short-packet kernel bound with an unprovided cost bound.
Harper's Euler Product Result1 in IMRN2023, section2.3, controls higher-order
errors by summing local prime expansions and multiplying independent Euler
factors. Those local factors are not available for arbitrary hW. The corpus's
divisor-square identity also permits exact signed compensation by the
composite entry, so a sign deletion in the cubic sum is not justified.
Next attack the original full-cone pairing with logarithmic convolution
tests, retaining the cubic term, full archimedean cost and both pole terms.
Phase5 remains open; no dependent Lean theorem has been added.

## Cycle25: what the direct cubic test actually pays

Retain C24's ordered sharp cutoff ab<=N. For n>=2 put
b_n=lambda(n)/(sqrt(n)*log n), and set

  V_N = sum_(2<=n<=N) b_n^2,
  A_N = sum_(2<=n<=N) log(n)*b_n^2,
  B_N = sum_(a,b>=2,ab<=N)
          lambda(a)*lambda(b)*lambda(ab)/(ab*log(a)*log(b)).

The full-source Toeplitz parent applies through
weilPositive_of_weilPositiveFull. Increase its constant C to be nonnegative;
then K_N=log N+C>0 for N>=2. Test the finite vector c(1)=t, c(n)=b_n for
2<=n<=N, zero elsewhere. Its squared norm is t^2+V_N. Its arithmetic pairing
is exactly 2t*A_N+B_N: the m=1 terms give 2t*A_N; in the remaining ordered
pairs, swapping a,b and using log(ab)=log a+log b gives B_N. Thus, for EVERY
real t,

  2t*A_N+B_N <= K_N*(t^2+V_N).

Taking t=A_N/K_N gives the exact paper consequence

  B_N <= K_N*V_N - A_N^2/K_N.

This is a Schur-complement consequence of the existing finite ceiling:
verdict BRIDGE, no scientific novelty claim. The parent legitimately uses
polar-free tests and charges their archimedean cost; neither pole was
silently deleted from an unrestricted test. The cubic B_N is log(ab) times
C24's summand. The inequality is one-sided and does not bound |B_N|.
Abel summation cannot turn it into C24's uniform absolute bound without a
new estimate. In particular multiplying the whole test by -1 leaves the
quadratic form unchanged and supplies no opposite inequality.

There is also an exact Hankel representation, with the cutoff retained:

  C24_sum(N) = sum_(a,b>=2) b_a*b_b*H_N(a,b),
  H_N(a,b) = 1_(ab<=N)*lambda(ab)/(sqrt(ab)*log(ab)).

The standard multiplicative Hilbert matrix has lambda(ab)=1, not this
signed source. Even a uniform bound for the actual H_N would initially give
only |C24_sum(N)|<=C*V_N, and boundedness of the untruncated operator does
not by itself establish a uniform bound for the sharp product cutoff.
Perfekt's September2026 Fejer--Riesz theorem (arXiv:2609.03855, Theorem1.1
and Corollary1.2) supplies a bounded symbol for the standard matrix. It
neither inserts lambda(ab) nor bounds V_N. Ma--Lu--Zu, arXiv:2608.22882v2,
section6, uses coefficient domination or a positive moment representation;
none has been produced for the signed source. No Hankel-transfer theorem
for hW has been assumed.

The new WP03 harmonic law says the ordinary sum of (lambda-Lambda)/n tends
to L<=0. It is linear in the deviation and gives neither this three-source
correlation nor the prime-deletion logarithmic limit. Its Gaussian source
coefficient is (lambda-Lambda)*1*1, not lambda^2 or lambda^3. The exact
Gaussian spectral identity retains a nonnegative |zeta|^2-weighted boundary
integral. Dropping that term proves only an upper bound, not its vanishing.

C24 remains SURVIVES PRELIMINARY ATTACK / OPEN CORE. No proof of C24 implies
WP05 has been obtained either. Therefore this moment detour is deprioritized,
not declared false or retired. Its exact source bound and the missing phase
transfer remain separate recorded obligations. No redundant Lean leaf added.

## Cycle26: return to the actual parity mode

Select the conductor-two case of C11 as the next exact source conjecture,
stronger than C13's unquantified mean and explicitly using C15's now-proved
principal mean. For a(n)=sourceCoeff lambda n and original hW alone:

  for every epsilon>0, exists C>=0, for all integers N>=1,
  |sum_(1<=n<=N) (-1)^n*a(n)| <= C*N^(1/2+epsilon).

This is not a new name for a proved bound. It would pay the first missing
nonprincipal arithmetic mode and imply C13, hence the p=2 instance of C16
using C15. It does not by itself settle WP05. A falsifier must be an actual
full-positive source, not a periodic surrogate. Competing possibility:
full positivity permits a nonperiodic source with a parity pole or a larger
alternating remainder.

The exact starting algebra is unchanged: on Re(s)>1,
F_alt=F-2F_odd=F*(1-2*exp(-L_even)). The odd-index mask commutes with
Dirichlet convolution; the alternating mask does not. No full positivity,
Euler factor, or half-plane continuation of the masked source follows from
that identity. C15 pays F's pole and untwisted remainder; it does not pay
F_odd's pole residue or its remainder.

[OPEN CORE]: derive the parity cancellation from the original source form,
retaining the signed arithmetic terms and the physical height dependence.
An analytic route would have to produce a pole-free continuation of F_alt
and adequate strict-half-plane growth before copying C15's contour argument.
Neither condition is added as a premise. Current corpus and primary twist
parents are being checked against this exact claim. Do not return to broad
Haar moments without first proving their transfer to the physical phase.

C26 first refreshed attack: the source search returns C15's principal sum,
forwardCoeff_LSeries, and the finite two-prime fibre identity. The complete
notchBochner_le statement still requires NotchSmall and convergence of every
gcd-harmonic fibre. Neither is supplied by the new single harmonic sign law.
The generated parity/pole recipe conflates additive coefficient parity with
a character-parity or reflected-kernel calculation; reject it. The exact
Kaczorowski--Perelli primary parent starts inside the Selberg class and
requires analytic twist properties, so it does not produce this source mode.
Verdict SURVIVES PRELIMINARY ATTACK, without a novelty claim. Phase5 remains
open at the actual source cancellation. Next inspect the signed two-fibre
pairing and try to replace its absolute notch error while retaining all
physical-height and polar terms; do not repeat the already-failed signed
summatory-to-absolute-cost substitution from C16.

## Cycle27: a finite even logarithm without an assumed parity pole

C26 remains the exact square-root forward parity conjecture. The proposed
paired-scale contour step is REDISCOVERED: the current polynomial Gaussian
modules already prove it with the half-scale cosine retained. No duplicate
leaf is warranted. A different consequence connects those linear source
coefficients to C16's nonlinear forward ratio.

Claim, original hW only: there exist real ell_2, K>=0 and eta>0 such that
for every 1<sigma<1+eta,

  |L_2(sigma)-ell_2| <= K*(sigma-1),
  L_2(sigma)=sum_(n>=2, 2 divides n) lambda(n)/(log(n)*n^sigma).

This is a right Abel limit with a Lipschitz remainder. It is not ordinary
convergence at sigma=1, analytic continuation across1, nor ell_2=log2.
The competing possibility of a divergent even logarithm would contradict
the following source-specific argument. The broader C16 claim still allows
a wrong finite constant as a possible falsifier.

Fix sigma>1 and put d=lambda_0-Lambda, D=sum d(n)/n^sigma,
E=sum_(2|n) d(n)/n^sigma, x=2^(-sigma), z=zeta(sigma),
b=d*1*1, V=sum b(n)/n^sigma, V_alt=sum (-1)^n*b(n)/n^sigma.
All these series converge absolutely by full positivity's actual source
summability and the convolution theorem. All values are real. The odd
mask is completely multiplicative, hence restricting b to odd indices
gives d_odd*1_odd*1_odd. Since sum_(odd n) n^(-sigma)=(1-x)z,

  V=D*z^2,
  V_alt=V-2*(D-E)*(1-x)^2*z^2
       =z^2*((-1+4*x-2*x^2)*D+2*(1-x)^2*E).                 (27.1)

For a fixed real c, the proved polynomial Gaussian profile is
H_c(t)=(1+c^2/2)H(t)-(c/2)H_alt(t/4)-c*H(4t).
Its real part is <=C_c*t^(-5/12) for 0<t<=1. Its norm is <=D_c/t
for all t>0: bound the three actual summable Gaussian series separately
using exists_norm_source_twisted_gaussW_le at r=1 and1/2, then rescale.
The polynomial Mellin theorem supplies absolute Mellin convergence for
sigma>1 independently of that signed upper bound. For1<sigma<3/2,
multiply the real upper bound by t^(sigma/2-1). An integrable upper
envelope is C_c*t^(-11/12) below1 and D_c*t^(-5/4) above1. Therefore
there is a finite B_c, independent of sigma, with

  Gamma_R(sigma)*[(1+c^2/2-c*x)*V-c/(2*x)*V_alt] <= B_c.   (27.2)

Every term and scale in (27.2) is the actual polynomial Mellin identity;
no factorization of a parity-free dilated profile is used. Substituting
(27.1) gives

  Gamma_R(sigma)*z^2 *
    [(1+c^2/2-2*c+c/(2*x))*D - c*(1-x)^2/x*E] <= B_c.    (27.3)

Use ONLY the two fixed tests c=1 and c=-1. The ordinary harmonic parent
gives D(sigma)->L=(sourcePoleNumerator hW 1).re. Equivalently this follows
from the proved double-pole limit for V and (sigma-1)zeta(sigma)->1.
Also x->1/2, Gamma_R(sigma)->1, and Gamma_R(sigma)*z^2 is positive and
tends to infinity. Thus the D terms in (27.3) stay bounded, the right
sides after division stay bounded (indeed tend to0), and (1-x)^2/x tends
to1/2>0. The c=1 inequality bounds E below; c=-1 bounds it above.
Consequently |E(sigma)|<=M on some right neighborhood of1, with no limit
for E assumed. More explicitly these two tests give liminf E>=L and
limsup E<=-7L; sharper optimization is unnecessary for this bridge.

The even von Mangoldt contribution is exactly log2/(2^sigma-1): among
even integers, its nonzero terms are precisely powers of2. It stays
bounded near1. Hence E_lambda(sigma)=sum_(2|n)lambda_0(n)/n^sigma
is bounded near1. Termwise differentiation on each compact subinterval
of(1,infinity) is justified by absolute Dirichlet convergence at a smaller
real abscissa; the derivative of lambda/(log n*n^sigma) is
-lambda/n^sigma. Therefore L_2'=-E_lambda is uniformly bounded near1.
The real mean-value theorem gives |L_2(u)-L_2(v)|<=K|u-v| there.
Completeness of R gives the unique right limit ell_2; letting v decrease
to1 in this bound gives exactly the claimed Lipschitz remainder.

The exact convolution-exponential restriction also gives, for sigma>1,
F_odd(sigma)/F(sigma)=exp(-L_2(sigma)). Thus its right limit is the
positive number exp(-ell_2), with O(sigma-1) remainder. Combined with
C15's actual pole B/(sigma-1)+O(1), this gives the radial expansion
F_odd(sigma)=B*exp(-ell_2)/(sigma-1)+O(1). It does not continue F_odd
holomorphically, produce an ordinary mean, or normalize the residue.

Paper verdict: BRIDGE. The analytic completion step is elementary;
the substantive input is the corpus's actual signed polynomial source
inequality. No scientific novelty claim for this consequence alone.
Booker arXiv:1308.3067v2 Definition1.3(A3) and Theorem1.7 retain discrete
support and almost-everywhere integral multiplicities; they do not provide
the present deletion limit without proving those missing source inputs.
Lean status: formalized in the six DeletionMasks/Canonical/Bound/Logarithm/
Ratio/Pole leaves. The exact mask identity, the source bound, and the
derivative/limit passage are proved from original hW. All six targeted
builds and mandatory direct source audits passed; thirteen exported
theorems have only propext, Classical.choice and Quot.sound as axioms.
See cycle27-verification.json. Global lint reports six unrelated unreachable
modules, no owned deletion-leaf errors. C26, ell_2=log2 and full WP05 remain OPEN.


## Cycle28: normalize the now-finite conductor-two residue

**Exact source conjecture.** For every original `hW : WeilPositiveFull lam`,
with `a = sourceCoeff lam`,

    lim_(sigma down to 1) L(oddPart a,sigma)/L(a,sigma) = 1/2.

By Cycle27 this ratio already has a positive real limit. The conjecture is
therefore a value assertion, equivalently `ell_2 = log 2`, rather than a
newly assumed existence or continuation statement. It is the conductor-two
case of Cycle16, returned to with a verified source bridge. It would remove
the radial principal term of the alternating forward series. It would NOT
by itself prove Cycle26's ordinary square-root cancellation: continuation
and growth of the actual parity twist remain separate debts.

**Preliminary attack: SURVIVES PRELIMINARY ATTACK.** No counterexample meeting
original full positivity has been produced, and no applicable parent theorem
was found. This is not an absence or significant-novelty claim: search
coverage is incomplete. A bounded logarithmic derivative controls variation
near one, not the logarithm's endpoint value. The normalized polynomial
inequalities concern derivative-series data and retain source-dependent
constants; the limit cannot be set to `log 2` by notation or normalization.

Booker's converse theorem starts with a discrete, eventually integral
spectral divisor. Kaczorowski--Perelli's twist theorem starts inside the
Selberg class with analytic twist bounds. The corpus's
PrimeDeletion.residue_quantization_complex concerns the actual indicator
of integers free of a specified prime set and assumes counting and
Chebyshev asymptotics. None applies to the arbitrary signed forward source
at this stage. Importing those unpaid inputs would be circular.

**Meaning of success/failure.** Success would force one canonical local
arithmetic normalization directly from the original positive functional,
without a prior atomic spectral representation or filtered-source positivity.
A counterexample satisfying full positivity and having a different ratio
would refute both this normalization and Cycle26, and would require a new
route to the assigned phase problem. Merely changing an Euler factor of a
Dirichlet series is not such a counterexample unless full positivity is
proved for its resulting coefficients.

**[OPEN CORE].** Produce a signed original-source identity or inequality that
fixes the endpoint value. The next mechanism to audit is Abel regularization
of the two-fibre pairing, retaining every cross term and error. Cycle27's
bounded derivative can only be used where it controls the exact signed
quantity. It must not be substituted for the absolute `NotchSmall` costs
that killed the previous sharp-cutoff argument. If those costs persist,
reject this mechanism and conjecture another source normalization law.

### C28 mechanism audit after C27 formal verification

The existing notch route cannot be invoked with C27 in place of NotchSmall.
Its absolute harmonic, square-root and tail envelopes enter before the
signed limit. Abel transformation preserves those obligations; it does not
prove them. This rejects that transfer, not the source conjecture. The
positive survivor is C27's signed finite-limit theorem, already formalized.

The refreshed finite-polynomial source theorem gives, simultaneously in
N,c,T>=1,

  Re Q_N(c,T) <= D E_N(c) (N+1)^(9/8) T^(5/6),
  E_N(c)=sum_(1<=m<=N) c(m)^2/m,
  Q_N(c,T)=sum_(m,n<=N) c(m)c(n)/n *
       sum_k (d*1*1)(k) exp(-4*pi^2*(km/n)^2/T^2) cos(2*pi*km/n).

Here d=lambda_0-Lambda; the notation T>=1 applies to T, and N is any
natural number. This is the actual FiniteBound parent, not a conjectured
new inequality. For E_N=1 and N+1<=T^theta it is sublinear when theta<4/27.
A contradiction would require a source-derived positive lower bound for
this same signed form with the same length and energy budgets. Neither
C27's residue nor the upper bound constructs such a coefficient vector.
No unbounded-degree limit is taken without its displayed N-cost.

The exact spectral identity keeps the nonnegative measure term

  Re integral_(Re s=3/4) sourceZetaPairing(s) gaussWeight_T(s)
    = -pi * integral |zeta(1/2+it)|^2 exp(-t^2/T^2) d(boundaryMeasure hW)(t).

A proposed higher-moment attack must first derive its own source identities
and sharp asymptotics. Hölder for a positive measure by itself cannot force
this integral to vanish. No higher-moment asymptotic was proved or adopted,
and the exploratory moment search is not a new completed conjecture cycle.

C28 still has [OPEN CORE]: an actual signed source constraint fixing ell_2,
rather than bounding it. C26's ordinary parity cancellation and the original
WP05 representation/settlement inputs remain separate unresolved targets.

## Cycle29: forward-coefficient sign proposal

Exact competing conjecture: for every original hW and n>=1, the real
coefficient sourceCoeff(lambda)(n) is nonnegative. This is stronger than
reality of the coefficients and is not an input of the assigned problem.
Search62763's proposed recipe explicitly lists this target as an obligation;
it does not prove it. Li-coefficient positivity concerns a different sequence.

Verdict SURVIVES PRELIMINARY ATTACK, but no source proof or original-hW
counterexample was found. The energy bound controls squares, not coefficient
signs. Even a proof would not normalize C28 by positivity alone: for 0<c<1,
the model F(s)=zeta(s)(1+c*2^(-s)) has positive coefficients
1+c*1_(2 divides n), mean (1+c/2)N+O(1), and odd/full radial ratio 1/(2+c).
This is NOT a full-positive counterexample. Its logarithmic coefficient
deviation is supported on powers2 and absolutely summable at the critical
weight, so existing regular/excess rigidity excludes hW for c!=0. No such
model is substituted for the original source. A positive Tauberian theorem
would still need its exact boundary hypotheses; a radial limit alone does
not produce ordinary parity means. Deprioritize this sign-only detour.

## Cycle30: rational reciprocity and every finite prime deletion

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The parity endpoint should belong
to a whole finite arithmetic deletion system, produced by rational
reciprocity of the original signed source, before Euler factorization.

Exact target, original hW only: for every integer Q>=2, put
L_Q(sigma)=sum_(n>=2, gcd(n,Q)>1) lambda(n)/(log(n)*n^sigma).
There exist real ell_Q, K>=0, eta>0 such that L_Q has right limit ell_Q at1
and |L_Q(sigma)-ell_Q|<=K*(sigma-1) for 1<sigma<1+eta.
Consequently the actual coprime-to-Q forward series divided by the full
forward series tends to exp(-ell_Q)>0 with error O(sigma-1). Neither
exp(-ell_Q)=phi(Q)/Q nor an Euler product is asserted.

The competing falsifier is a full-positive source with a divergent finite
prime-deletion logarithm. A noncanonical finite endpoint is not a falsifier
of C30; it remains the issue in C28. Success would replace a parity accident
by an entire family of actual arithmetic projections.

Paper mechanism: write d=lambda_0-Lambda, b=d*1*1, and for rational r set
V_r(sigma)=sum_n b(n)cos(2*pi*n*r)/n^sigma and
W_r(sigma)=(sigma-1)^2 Re(Gamma_R(sigma)V_r(sigma)).
Every series here converges absolutely for sigma>1. Define
H_r(t)=sum_n b(n)cos(2*pi*n*r)exp(-pi*n^2*r^2*t) for r>0.
Then M H_r(sigma/2)=Gamma_R(sigma)r^(-sigma)V_r(sigma).
Norm-Fubini follows from absolute convergence of b at sigma; it is not
inferred from a signed upper bound.

For finite real c_1,...,c_N, the actual finite profile
P_c(t)=sum_(m,n=1..N)c_m*c_n/n * H_(m/n)(t) has real part
O_c(t^(-5/12)) above and norm O_c(t^(-1)) at all t>0.
The first is FiniteBound after T=sqrt(4*pi/t); the second is the finite sum
of the actual absolute Gaussian bounds. The existing Mellin-envelope lemma
therefore bounds Re M P_c(sigma/2) uniformly for 1<sigma<3/2.
Its transform equals Gamma_R(sigma) times
sum_(m,n)c_m*c_n*n^(sigma-1)/m^sigma * V_(m/n)(sigma).

Choose c supported on two distinct labels m,n, with values1,+1 and1,-1.
After multiplying by (sigma-1)^2, both quadratic forms have an upper bound
tending to0. Their common diagonal is (1/m+1/n)W_1(sigma), bounded because
W_1(sigma)->L by the original source pole theorem. Hence their off-diagonal

  n^(sigma-1)/m^sigma * W_(m/n)(sigma)
   + m^(sigma-1)/n^sigma * W_(n/m)(sigma)

is bounded in absolute value near1. Both coefficients have positive finite
limits. Thus boundedness of either W_(m/n) or W_(n/m) gives the other.
No separate lower estimate for the positive spectral measure was used.

Now W_r is periodic in r with period1, and W_0=W_1. Strong induction on
denominator q proves boundedness for W_(a/q) for every natural a,q>0:
reduce a modulo q; remainder0 is the base case. For 0<k<q, W_(q/k) is
bounded by the induction hypothesis on denominator k. The preceding
two-label relation gives boundedness of W_(k/q). This is a qualitative
fixed-rational result, with no denominator-uniform constant claimed.

Let chi_Q(n)=1_(gcd(n,Q)=1). Its finite Fourier expansion contains only real
cosine coefficients, since chi_Q(-n)=chi_Q(n). The just-proved rational
bounds imply boundedness of (sigma-1)^2 Gamma_R(sigma) L(b*chi_Q,sigma).
Here b*chi_Q denotes pointwise masking. This mask respects Dirichlet
convolution, so

  L(b*chi_Q,s)=L(d*chi_Q,s) zeta(s)^2
                  * product_(p divides Q)(1-p^(-s))^2.

The product tends to a nonzero real number, and
(sigma-1)^2 Gamma_R(sigma)zeta(sigma)^2 ->1. Since the real-axis series
are real, L(d*chi_Q,sigma) is bounded. Subtracting from the bounded full
d-series gives boundedness of the excluded d-series. The excluded
von-Mangoldt series is harmonically summable: among primes only finitely
many divisors of Q contribute, and the proper-prime-power tail is already
harmonically summable. Thus the excluded lambda-series is bounded near1.

Termwise differentiation gives L_Q' equal to minus that series. The mean
value theorem and completeness give the finite endpoint and Lipschitz
error, exactly as in C27. Finally chi_Q commutes with the Dirichlet
exponential, so the actual coprime/full ratio is exp(-L_Q). Local
Lipschitz continuity of exp gives its error estimate. No arithmetic sign
condition, filtered-source positivity or continuation of the deleted
series enters.

Paper proof status: dependency-closed subject to checking the current
finite-profile parent and its exact normalization in Lean. The intended
first Lean capstone is boundedness of every rational W_r. The subsequent
finite Fourier/mask/endpoint transfers remain to formalize. Literature and
corpus novelty audit is running; no significant novelty claim yet.

C30 implementation refinement: the principal-character L-function in this
installed mathlib already supplies the canonical coprime factor and its nonzero
residue (`DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`,
`LFunctionTrivChar_residue_one`, DirichletContinuation.lean 174–197). This may replace
a fresh finite Euler-product derivation in the masked-convolution transfer. Only the
canonical masked zeta factor uses this theorem; no Euler product is assumed for the
unknown source.

The finite Fourier search was partial (budget exhausted during secondary queries,
semantic retrieval/reranking and judgment); all returned statements and source
arguments were inspected. Existing cyclic DFT/inversion in mathlib supplies the
algebraic transfer. No indexed hit closes the actual-source analytic bound.

### Next attack exposed by C30 (not yet certified or novelty-audited)

The two-label quadratic suggests more than fixed-rational boundedness. Put
A=Re(sourcePoleNumerator hW 1)<=0. After normalizing and taking a right limsup,
optimization in the coefficient c should give

  limsup |W_(m/n)/m + W_(n/m)/n| <= 2*(-A)/sqrt(m*n).

For 0<m<n this becomes a contracting reciprocal estimate with multiplier m/n.
Along the Euclidean algorithm, products of these multipliers telescope; the
remainders decrease by at least a factor two every two steps. This suggests an
absolute constant K with sup over rational r of limsup |W_r| <= K*(-A).
The sigma-neighborhood may still depend on r: exchanging the rational supremum
and sigma-limit is NOT justified. A=0 would then force each rational normalized
twist to tend to zero, but A=0 is not assumed and has not been proved.

This is a new conjecture/attack to audit after the current C30 finite-deletion
transfer. It is not included in the present formalization or progress claim.

C30 part 2 source transfer (implemented, final audit pending): for the complement
mask E_Q=1-C_Q, linearity gives E_Q lambda = D_1-D_Q+E_Q Lambda at every real
sigma>1, where D_Q=L(C_Q(lambda-Lambda),sigma). The first two terms are bounded
by the masked-square result, and the last is bounded even on sigma>=1 by its
absolutely convergent harmonic series. Hence the literal excluded logarithm
L_Q has bounded derivative -L(E_Q lambda,sigma) on some right interval.
A Lipschitz extension gives ell_Q and |L_Q(sigma)-ell_Q|<=K_Q(sigma-1).
Since C_Q is multiplicative as a mask, it commutes with every Dirichlet
convolution power and the formal exponential. Therefore the actual coprime/full
forward ratio is exp(-L_Q(sigma)). Its limit exp(-ell_Q) is positive, with linear
error by local Lipschitz continuity of exp. Q=1 is permitted (trivial deletion);
no property of the unknown source is assumed beyond the original hW.
The principal L-function residue belongs only to the canonical constant-sequence
factor in the masked source square. It is not an Euler product for lambda.

## Cycle31: force the residual logarithmic variance to vanish

Exact source conjecture: with a(n)=sourceCoeff(lam,n),
B=sourceCompletion(hW,1), and original hW alone,

  (1/log N) sum_(1<=n<=N) |a(n)-B|^2/n -> 0.

The refreshed corpus now proves this expression has a finite nonnegative limit V,
with total energy coefficient K=|B|^2+V. It does not determine V. This is weaker
than C14's ordinary mean-square conjecture but still attacks the missing source
rigidity, rather than adding another unspecified endpoint constant.

Competing mechanisms: (i) every source has V=0; (ii) positive V is necessarily
visible in a finite rational arithmetic mode and C30's endpoints expose it;
(iii) positive V could escape every fixed finite deletion test. These are research
alternatives, not assumptions. C30 alone cannot exchange growing Q with the
radial limit; fixed-Q constants do not establish (ii) or exclude (iii).

First attack: Cauchy--Schwarz only gives K>=|B|^2. Existing
norm_residue_sq_le_log_energy has precisely this direction. The multiplicative
Toeplitz self-test with coefficients a(n)/sqrt(n) produces the log-moment
inequality; its leading terms are compatible with every K>0. Reapplying that
same scalar inequality cannot set V=0. A new signed cross-correlation or sharp
energy upper bound is required. [OPEN CORE]: derive K<=|B|^2 from hW, preserving
the exact source and without assuming periodicity, coefficient sign, spectral
integrality, or analytic continuation of deleted twists.

Booker's degree-one classification is not a closure: its L-data axioms already
require a discrete spectrum with only finitely many nonintegral masses. No such
input is supplied by C30. The deep-search suggested use of RegularDeviation
likewise adds an unproduced premise. These mechanisms are rejected, not the
source conjecture. Verdict: SURVIVES PRELIMINARY ATTACK; no proof or novelty claim.

### C31 mechanism audit: reciprocal positivity does not normalize its diagonal

The algebraic limiting constraints alone permit the rational profile
w(p/q)=-1/q for a reduced rational p/q with q>0. It is even and1-periodic,
|w|<=1, and w(k)=-1 for every integer k. For positive integers m,n,

  w(m/n)/m = -gcd(m,n)/(m*n).

Consequently its finite source-shaped quadratic equals

  -sum_d phi(d) (sum_(m<=N,d|m) c_m/m)^2 <= 0,

using gcd(m,n)=sum_(d|m,d|n)phi(d). Thus even a uniform rational bound and
all finite nonpositive reciprocal quadratics do not force w(0)=0. This is
an abstract kernel diagnostic, NOT an actual full-positive source. In the
formal convolution model it resembles a forbidden degree-one coefficient;
the actual d(1)=0 constraint must be retained through any proposed transfer.
The positive survivor is the exact divisor-incidence factorization and
positivity classification; both already exist in
DivisorStationaryKernelPositivity.lean. No new GCD theorem is claimed.
Verdict for the scalar-normalization inference from these constraints alone:
FALSE. Verdict for its positive GCD classification: REDISCOVERED.
This does not refute C31's actual-source V=0 conjecture.

### C32 candidate attack: finite prime masks can miss valuation-depth variance

Before choosing another source claim, audit a sharper diagnostic family. Let p
be prime and P be a real polynomial with P(0)=1 and P(1/p)=1. The ordinary
Dirichlet coefficients of zeta(s)P(p^(-s)) have mean1. Every coprime deletion
has canonical radial ratio: if p divides Q, the mask retains only the constant
polynomial term; otherwise multiplication by p preserves coprimality and the
same P factor occurs upstairs and downstairs. In either case P(1/p)=1 gives
ratio phi(Q)/Q. Nonconstant P may nevertheless give positive periodic variance.
The explicit p=2 candidate is P(z)=1+c*z-2*c*z^2 with0<c<1/3:
coefficients are1+c*1_(2|n)-2*c*1_(4|n), mean1 and variance c^2/2.
For |z|<=1, |c*z-2*c*z^2|<=3*c<1, so even zero-freeness on Re(s)>=0
holds for this factor. Its logarithmic deviation is regular and is excluded
by the existing full-positive regular-deviation rigidity theorem. It is NOT
an hW counterexample.

Proposed exact positive survivor: for finite prime-power Euler polynomials,
all finite coprime endpoint normalization detects P(1/p), whereas the invisible
polynomial directions with P(0)=P(1/p)=1 are exactly multiples of z*(z-1/p).
Their nonconstant periodic coefficient energy remains observable by prime-power
residue classes. Internal/external novelty and exact proof audit pending;
no Lean code yet. Search /tmp/wp05-c32-invisible-valuation-search.json started.

C32 completed first paper attack: all coprime masks inspect only whether a prime
divides n, not its valuation depth. For a degree-D polynomial P(z)=sum c_j z^j,
a(n)=sum_(j<=v_p(n))c_j (n>=1). Its ordinary mean is P(1/p). The exact periodic
variance around B=P(1/p) is

 (1-1/p) sum_(k=0..D-1) p^(-k) (sum_(j=0..k)c_j-B)^2
       + p^(-D)(sum_(j=0..D)c_j-B)^2.

Every summand is nonnegative; zero variance forces all successive prefix sums
to equal B, hence c_j=0 for j>=1. With P(0)=P(1/p)=1, this is equivalent to P=1.
The invisible polynomial space P-1 is exactly the ideal z*(z-1/p)R[z], by the
factor theorem at two distinct points. This classification is elementary
polynomial/periodic-coefficient theory, not a scientific novelty claim.
Exact source applicability still fails: these deformations are regular and
full Weil positivity excludes the nonconstant cases. The no-go is against
using only finite coprime normalization to prove zero variance. It remains an
unsealed diagnostic until its exact positive survivor has a Lean audit; no
failed-route closure is claimed.

## Cycle33 entry: recover the prime-power depth actually discarded by C30

Exact proposed source theorem: for every prime p and integer k>=1, original hW
alone gives a finite right endpoint, with O(sigma-1) error, for

 L_(p,k)(sigma)=sum_(v_p(n)=k) lambda(n)/(log(n)*n^sigma).

A stronger forward conclusion would give the actual radial residue in every
fixed valuation stratum from these logarithmic endpoints and the already proved
coprime pole. The residue may be signed; positivity of forward coefficients is
not assumed. Canonical values remain a distinct source conjecture.

New mechanism suggested by C32: the exact-valuation mask is the difference of
two divisibility masks, each a finite rational cosine average. Thus C30 controls
the normalized b=(lambda-Lambda)*1*1 series in every fixed valuation stratum.
Write t=p^(-s), A(s)=(1-p^(-s))*zeta(s), and B_k,D_k for the valuation-k series of
b and d=lambda-Lambda. Formal p-adic convolution gives

 B_k=A(s)^2 sum_(j=0..k)(k-j+1)t^(k-j)D_j,
 D_k=[B_k-2t B_(k-1)+t^2 B_(k-2)]/A(s)^2,

where negative subscripts mean0. This retains only a finite second difference,
so no growing-modulus limit or uniform rational constant is needed. The positive
canonical residue of A supplies a lower bound for its normalized square. Restore
the canonical valuation-k term (only n=p^k for k>=1), then use bounded derivative
as in C30. No full proof/novelty verdict yet: exact convolution-stratum transfer
and source/API eligibility are under search. Current search receipt
/tmp/wp05-c33-valuation-endpoint-search.json. [OPEN CORE] for implementation:
prove the actual local second-difference identity with every zero-index convention.

### C33 dependency-closed paper proof of the logarithm endpoint

Fix prime p, k>=1. Define P_j f(n)=f(n) when p^j divides n and p^(j+1)
does not, and0 otherwise (including n=0). Let S_p f(n)=f(n/p) if p divides n,
and0 otherwise. Each P_j is the difference of the p^j and p^(j+1) divisibility
masks. Finite cyclic character orthogonality expresses these masks as real
cosine sums. C30 and finite linearity therefore bound
(sigma-1)^2 Re[Gamma_R(sigma)L(P_j b,sigma)] for every fixed j.

Let u(n)=1_(p does not divide n). The coefficient identity

 b-2 S_p b+S_p^2 b = d*u*u

follows from b=d*1*1 and (1-S_p)1=u. Here * is Dirichlet convolution. One checks
n=0 directly; for n>0 S_p commutes with convolution by assigning the factor p
to either divisor coordinate. Since u vanishes on multiples of p,
P_k(f*u)=(P_k f)*u. Also P_k S_p f=S_p(P_(k-1) f) for k>=1, and P_0 S_p f=0.
Absolute convergence on sigma>1 justifies the Dirichlet identities and gives

 L(P_k b)-2 p^(-sigma)L(P_(k-1)b)
 +1_(k>=2) p^(-2sigma)L(P_(k-2)b)
   = L(P_k d) L(u)^2.

For k=1, the S_p^2 term is zero. At n=0 all projected sequences are zero, so
there is no discarded exceptional coefficient. The factors p^(-sigma) remain
bounded as sigma->1+. L(u)=(1-p^(-sigma))*zeta(sigma). Hence
Gamma_R(sigma)*((sigma-1)L(u))^2 tends to (1-1/p)^2>0.
The coefficients of P_k d are real, so division by an eventually positive
lower bound yields bounded |L(P_k d,sigma)|. All sums here are absolutely
convergent at every sigma>1; no convergence of d at one is assumed.

The canonical term P_k Lambda is dominated in absolute harmonic norm by the
entire excluded canonical part at p, already proved summable in C30. Thus
|L(P_k lamC,sigma)| is bounded on a right interval. The literal real logarithm
F_k(sigma)=sum_(n>=2,P_k(n)=1)lam(n)/(log(n)*n^sigma) has derivative
-L(P_k lamC,sigma), by the existing absolutely convergent log-series derivative
lemma. Bounded derivative makes F_k Lipschitz on that interval; extend it to
one, obtaining ell_(p,k) and an O(sigma-1) remainder. This proves exactly the
stated logarithm endpoint with no new source premise. The stronger forward
valuation-residue conclusion requires a separate finite exponential-coefficient
transfer and is not included in this paper closure.

Source audit: deep search95786 completed partial=false but returned mostly
unrelated uses of stratum/valuation; inspected every candidate/source statement
and rejected its unverified recipe. Lexical valuation-convolution search94569
found no actual source endpoint. Strongest usable parents remain C30 rational
Mellin bounds, original absolute source convergence, canonical p-coprime residue,
and the original log-series derivative. External primary comparators remain
Estermann (canonical divisor twists) and Booker's L-data classification (extra
spectral integrality); neither supplies this arbitrary signed-source producer.
Verdict: BRIDGE. Novelty beyond literature unestablished. Paper proof closed for
fixed positive valuation logarithms; proceed to exact Lean identities and audit.

### C32 positive-survivor audit: exact finite-period realization

The finite variance formula can be audited directly on the actual periodic
coefficient sequence, without a guessed probabilistic model. For p>1, degree D,
and real coefficients c_j, put A(n)=sum_{j=0}^D c_j 1_{p^j|n} and
S_k=sum_{j=0}^k c_j. For any F:Real->Real, nested divisibility gives the exact
pointwise identity

F(A(n)) = sum_{k<D}(1_{p^k|n}-1_{p^(k+1)|n}) F(S_k)
          + 1_{p^D|n} F(S_D).

Average over 1<=n<=p^D. Nat.Ioc_filter_dvd_card_eq_div gives exactly
p^D/p^j multiples, so the resulting weights are
(1-1/p)p^(-k) for k<D and p^(-D) at D. Taking F(x)=x recovers
B=P(1/p); taking F(x)=(x-B)^2 gives the previously stated variance formula.
Every weight is positive. Zero variance forces every S_k=B and hence c_0=B,
c_j=0 for j>=1. Conversely these coefficient conditions give zero variance.
For P(0)=P(1/p)=1, zero variance is therefore equivalent to P=1.
The invisible-polynomial ideal is exactly X*(X-C(1/p)): factor P-1 first by X,
then evaluate the quotient at 1/p and apply the factor theorem again.
These are model classifications, not full-positive source counterexamples.
Lean status: Models and Periods leaf builds pass, including literal period
mean, variance, periodicity and zero-variance classification. Final cycle audit
remains outstanding.

### C32 dependency-closed same-model endpoint transfer

Put b=sum_j c_j delta_(p^j) and a=b*1 (Dirichlet convolution). For n>0,
a(n)=sum_j c_j 1_(p^j|n), exactly the periodic sequence above. Its Dirichlet
series is F(s) zeta(s), F(s)=sum_j c_j(p^j)^(-s), absolutely convergent on
Re(s)>1. Coprime restriction commutes with convolution. If p is coprime to Q,
it keeps b; otherwise it keeps c_0 delta_1, since every positive power of p
has the same prime support. Thus the restricted series is G_Q(s)L_Q(s),
where G_Q=F or c_0 and L_Q is the trivial-character L-function.

Every nonzero base complex power is continuous in s. Hence F(sigma) tends to
P(1/p)=1 as sigma decreases to1. Also c_0=P(0)=1, so G_Q tends to1 in either
case. The canonical residues of zeta and L_Q are1 and
prod_(q|Q)(1-1/q)=phi(Q)/Q. Multiply both numerator and denominator of the
actual ratio by sigma-1 (nonzero on this right interval) and take limits.
The denominator tends to1, so every actual coprime ratio has exactly the
canonical endpoint. This requires no asserted full-positive source.

For the same a(n), its period average of |a(n)-1|^2 equals the proven real
period variance because P(1/p)=1 and a(n) is real for positive n. It is strictly
positive for every nonconstant P satisfying both endpoints. Existence is
explicit: P=1+X(X-C(1/p)). Both endpoints are1; evaluating at1+1/p shows
P is not1 since 1/p>0. This closes the exact finite-period positive survivor.
No assertion about a full-positive source or an ordinary infinite variance
limit is needed or made. The diagnostic says all coprime endpoint values
alone cannot determine this local polynomial coefficient variance.


## Cycle34 candidate: uniform sparse forward-source control

Corpus correction: MaskedEnergy already proves the density-weighted radial
residue bound, and CoprimeEnergy already applies it simultaneously to every
coprime modulus. Repeating either theorem would be rediscovery.

The stronger exact candidate, under original hW only, is:
there exist C>=0 and eta>0 such that for EVERY q>=1 and EVERY
1<sigma<1+eta,

norm(((sigma:Complex)-1) * LSeries(divisibilityPart q (sourceCoeff lam),sigma))^2
  <= C/q.

OPEN_CORE: uniformity in q before taking the boundary limit, with no premise
that a masked residue exists. This would prevent forward-source mass from
escaping to arbitrarily high powers of any fixed prime. It does not normalize
coprime ratios or force the total residual variance to vanish.

Candidate mechanism to audit: the existing Abel majorant for the source's
critical log energy and masked Cauchy--Schwarz. The exact square-mask series
for multiples is q^(-sigma)*zeta(sigma), so q>=1 and sigma>1 give a common
q^(-1) bound. A common neighborhood bounds the normalized source energy and
(sigma-1)*zeta(sigma). No interchange of modulus and radial limits is needed.
Status: BRIDGE candidate, source applicability and external novelty audit not
finished; no Lean code and no new result claimed. C32 closure remains active.

### C34 attack and dependency-closed strengthened paper proof

Exact-search77871 returned partial=false, no errors, semantic coverage unmeasured.
All20 candidate and20 source statements inspected. Its recipe combines an
unrelated Gaussian notch bound and a triangle inequality, and does not apply.
The applicable parents are the source critical log-energy limit, Abel majorant,
and the existing weighted masked Cauchy--Schwarz inequality. External comparison
with Hedenmalm--Lindqvist--Seip remains a square-summable Hilbert-space parent;
the periodic-series paper arXiv2007.14008 concerns critical-line value distribution,
not arbitrary full-positive source uniform mask bounds. A search-result textbook
URL returned404 and supplies no evidence. Verdict: BRIDGE, standard analytic
mechanism, scientific novelty unestablished. No counterexample or circular
source premise found. The improved exact target keeps the sharp energy constant:

For the actual source a there is its log-energy constant K>=0 such that, for
every e>0, eventually for sigma->1+, SIMULTANEOUSLY for every integer q>=1,

  |(sigma-1)L(1_(q|n)a(n),sigma)|^2 <= (K+e)/q.

Let d=sigma-1>0, w(n)=|a(n)|^2/n (w(0)=0). The already proved energy limit
and Abel theorem with error e/2 supply A>=0, summability of the square energy,
and d E(sigma)<=d A+(K+e/2)sigma=:M(sigma). The literal square of the divisibility
mask has Dirichlet series q^(-sigma)zeta(sigma): away from n=0 it is the
Dirichlet convolution delta_q*1; at n=0 both L-series terms vanish. This
identity also gives nonnegativity of the real canonical series Z(sigma).
Weighted Cauchy--Schwarz gives

  |d L(1_(q|n)a,sigma)|^2 <= M(sigma) d Z(sigma) q^(-sigma).

All factors on the right except the last are nonnegative. Since q>=1 and
sigma>1, q^(-sigma)<=1/q. The expression M(sigma)d Z(sigma) tends to K+e/2,
using the canonical zeta residue. Choose a right neighborhood on which it is
at most K+e. This neighborhood is independent of q, proving the stated order
of quantifiers. Taking e=1 and extracting an open right interval gives the
original C/q proposal; q=p^k gives a uniform geometric valuation-tail bound.
No masked residue, sign, multiplicativity, or endpoint interchange is assumed.
Paper proof closed. Lean API eligibility and formalization next.

## Cycle35 candidate: exhaustion by finite divisibility observables

Context corrections: the reciprocal critical-log-energy proposal is already
the z=-1 case of C18, not a new conjecture. Finite canonical residual mass
already implies full rigidity in QuantizationFiniteRemainderRigidity. The
source theta reflection still contains the exact defect; deleting it would
assume the key conclusion. Neither shortcut is reused.

Given the exact corpus frontier, the new structural conjecture is that the
actual forward source has no critical square energy invisible to every finite
divisibility algebra. Explicitly, for a(n)=sourceCoeff lam n and original hW,
for every e>0 there exist Q>=1, c:{1,...,Q}->Complex, and N0>=2 such that for
all N>=N0,

  [sum_(1<=n<=N) |a(n)-sum_(1<=q<=Q)c_q 1_(q|n)|^2/n]/log N <= e.

This is a statement about the actual coefficients, with no multiplicativity,
positivity of coefficients, or local approximation premise. The basis contains
every finite truncated valuation partition, since intersections reduce to lcm
and exact valuation masks are differences of nested divisibility masks.
If true, all residual variance must appear in finite local arithmetic data;
it does not set those data to canonical values and does not alone prove WP05.
Its competitor is an actual hW source with a positive critical energy component
orthogonal to every finite divisibility polynomial. [OPEN CORE]: rule out that
component using full positivity rather than scalar energy and first means.

The candidate is not a density tautology: finite divisibility polynomials do
not approximate every bounded sequence in logarithmic square mean. A nontrivial
Dirichlet character is orthogonal to each divisibility indicator (periodic
averaging on multiples leaves zero mean), yet has positive mean square. That
comparison is not a full-positive source and is not a falsifier of C35 itself.
C32's polynomial examples, in contrast, lie inside the proposed approximation
class. This identifies a genuinely different obstruction from valuation depth.

A necessary finite consequence to audit is a joint Bessel budget for prime
deletion endpoints. Put B=sourceCompletion hW1, V=K-|B|^2, and let r_p be the
already proved coprime/full endpoint. For every finite set P of primes,

  |B|^2 sum_(p in P) [p^2/(p-1)](r_p-(1-1/p))^2 <= V.

Indeed the centered masks g_p=1_(p does not divide n)-(1-1/p) have limiting
square mass d_p=(p-1)/p^2 and pairwise zero covariance. Their source correlations
are B(r_p-(1-1/p)). The finite Hilbert/Bessel inequality would give the stated
shared budget without an ordinary masked mean or any completeness assertion.
This bridge is standard Hilbert geometry, not the scientific conjecture.
The stronger exhaustion assertion remains under exact corpus/external attack;
no dependency-closed proof or Lean assertion for it exists yet.

External parent opened: Alexander P. Mangerel, Additive functions in short
intervals, gaps and a conjecture of Erdos (2022),
https://link.springer.com/article/10.1007/s11139-022-00623-y . The paper treats
additive functions and uses Turan--Kubilius variance estimates; it does not
supply additivity or finite-divisibility approximation for our arbitrary source.
The classical variance framework is ancestry for the finite Bessel bridge,
not proof or novelty evidence for the exhaustion conjecture.

C35 preliminary attack verdict: SURVIVES PRELIMINARY ATTACK, with the
approximation producer still OPEN. Exact search14807 returned partial=false,
all20 candidate and20 source statements inspected; no producer found. Its
recipe combines a scalar energy ceiling with a Gamma-trace partition, which
does not identify a coefficient-space projection. The prime-Bessel search77481
also returned partial=false; the retrieved weighted-Bessel integral theorem has
different spaces and unpaid row/column estimates. No direct application.

External ancestry checked: Daboussi's1975 primary paper
https://www.numdam.org/item/AST_1975__24-25__321_0.pdf proves mean approximation
by finite prime-data models in a multiplicative setting under a prime-series
condition. Its1980 successor https://numdam.org/articles/10.5802/aif.796/
characterizes multiplicative Besicovitch functions with nonempty spectrum.
Frantzikinakis--Host https://arxiv.org/abs/1403.0945 gives a structured/uniform
decomposition for bounded multiplicative functions; the uniform remainder is
not asserted small in square mean. Our source has neither paid multiplicativity
nor the cited prime condition. These parents do not settle C35. They do show
that merely naming finite-prime approximation is classical; novelty would be
its derivation from the full Weil source, not the approximation concept.

### C35 finite covariance bridge: closed paper proof

Use centered source f=a-B. Its critical log energy tends to V, by the existing
actual-source variance theorem. Fix nonzero moduli Q_i and real weights c_i.
Let d_i=phi(Q_i)/Q_i, h_i(n)=1_(n coprime Q_i)-d_i, and g=sum_i c_i h_i.
Every product of coprime masks is the mask at Q_i Q_j. Hence the radial
square density of g exists and equals

  D=sum_(i,j)c_i c_j(d_(Q_i Q_j)-d_i d_j).

This equality uses only finite expansion and canonical trivial-character
residues. Each mask is bounded, so all its weighted square series converge for
sigma>1; the same holds for finite combinations. The original source series
also converges absolutely there, so the masked source series is legitimate.
The source correlation has radial residue

  R=B*sum_i c_i(r_(Q_i)-d_i),

because the centered canonical mask h_i has zero radial mean. Existing masked
energy inequality therefore gives |B|^2*(sum_i c_i(r_(Q_i)-d_i))^2<=V*D.
There is no passage from radial means to ordinary masked means.

For distinct primes, d_(pq)=d_p d_q; on the diagonal d_(p^2)=d_p, so D is
sum_p c_p^2 d_p(1-d_p). Choose c_p=(r_p-d_p)/(d_p(1-d_p)), whose denominator
is positive. Put S=sum_p(r_p-d_p)^2/(d_p(1-d_p))>=0. The inequality is
|B|^2 S^2<=V S. If S=0 the claimed budget is immediate; otherwise divide by S.
Since d_p(1-d_p)=(p-1)/p^2, this is exactly the finite prime Bessel statement.
The bridge is dependency-closed on paper. Formal API/source audit next; it
does not pay the C35 approximation core or imply V=0.

### C35 implementation checkpoint and C36 attack candidate

The finite covariance bridge now has four draft modules: CoprimeCombinations,
CoprimeCovariance, CoprimeVariance, PrimeDeletionVariance. Only the first is
checked so far. The latter three remain subject to Lean audit; no completion
claim is made.

C36 candidate, awaiting corpus/novelty audit: for every nonprincipal Dirichlet
character chi, does the actual twisted forward series satisfy
`(sigma-1) L(chi*a,sigma) -> 0`? This would remove nonprincipal periodic
correlations, but would not establish full divisibility approximation.

Immediate failed proof attempt: rational cosine bounds control
`(sigma-1)^2 Re(Gamma_R(sigma) L(cosine*(d*1*1),sigma))`, not the unnormalized
series. Principal coprime deletion retains a double pole in its squared
canonical L-factor, cancelling that normalization. A nonprincipal character
factor is finite at1; dividing by it leaves a possible double-pole bound.
Thus the C30 proof cannot simply be reused for character endpoint regularity.
Moreover cosine information sees even masks; odd character components need
additional input. Neither missing step is assumed, and no C36 Lean code exists.

C35 forced positive corollary, paper proof closed: the prime terms
`p^2/(p-1)*(r_p-(1-1/p))^2` are summable. They are nonnegative and every finite
sum is at most `V/|B|^2`; the existing source construction gives B nonzero.
Monotone completeness yields summability and the same bound for the full sum.
This is a standard consequence of the finite Bessel inequality, with no new
source premise or independent scientific novelty claim. It still permits
nonzero deviation at finitely many primes, and C32 permits positive variance
invisible even to all coprime endpoints. No variance-exhaustion claim follows.

### C36 finite-prime correction from the corpus

`WeilFiniteSupportRigidity.eq_vonMangoldt_of_weilPositiveFull` already proves:
original full positivity plus agreement with Lambda off the smooth numbers of
any finite prime set implies full equality. Its actual deviation potential is
positive definite by `WeilExcess.positiveDefiniteOnReal_neg_deviationPotential`;
the coefficient bound is produced from hW. Thus classifying another finite-prime
perturbation is not a new core advance. In particular, C32's one-prime polynomial
models remain diagnostics of endpoint information, not admissible hW sources.

The missing extension is not finite-prime rigidity but approximation compatible
with positivity. Pointwise truncation of arithmetic coefficients does not come
with a positivity-preservation theorem. The null potential is convolution of
Riemann autocorrelation with translates at plus/minus log n, not a naive finite
Fourier polynomial. Do not treat a coefficient cutoff as a positive projection.
C35's weighted endpoint square sum controls correlations only, not the critical
coefficient tail required to invoke an existing rigidity receiver.

### C36 audit of the final implication

The zero-variance retrieval did not find a theorem taking V=0 alone to source
rigidity. Its phase-symmetry recipe supplies no proof of that implication.
`WeilWorkQuantizationResonanceEnergy` identifies V with the centered critical
resonance energy coefficient; its comments explicitly distinguish that norm
from phase approximation. Consequently C31/C35 are necessary structural targets,
not a certified complete proof route by themselves.

Existing receivers instead require actual phase control (for example frequent
sublinear-power cumulative residual mass/phase variation), finite residual mass,
or suitable periodic phase expansions. Those premises must be produced from
hW. Logarithmic mean-square data by themselves ignore finite perturbations of an
arithmetic sequence; no pointwise source rigidity follows from an abstract
zero-seminorm statement. This observation is a diagnostic, not a full-positive
counterexample.

## Cycle 37: audit the missing energy-to-phase implication

The new source conjecture under attack is: original hW plus zero centered
critical logarithmic variance forces canonical source rigidity. This is an
OPEN conjecture, not a proved receiver and not an extra assumption silently
added to a theorem. It is a necessary route audit for C31/C35, not a change of
the assigned constant-phase target.

The abstract seminorm argument fails: a finite alteration of the constant
arithmetic sequence has zero logarithmic square seminorm but changes individual
coefficients. Such examples are not claimed to satisfy hW. The actual source's
positive Herglotz structure would need to eliminate this nullspace. Existing
resonance energy identifies the seminorm exactly, but supplies no such step.
The corpus search's recipe substitutes a phase-lock premise at this point;
rejected. No new Lean theorem is justified by this audit.

The actual theta reflection identity retains defectKernel(sourceDefect hW).
It is not an available functional equation. CrystallineProducerRigidity already
handles boundary measure supported on canonical critical zeros; that support
condition is unpaid. Boundary measure singularity itself was not found as an
unconditional theorem. SFinite is countable decomposition into finite measures,
not finite total mass; the singularity search's proposed shortcut is invalid.
Likewise the annulus winding results assume a summable periodic representation
of the actual phase, not just the existing local BV clock profiles.

The strongest useful paid receiver found here is
`eq_vonMangoldt_of_weilPositiveFull_of_atomPairing_eq_zero`: zero deviation
pairing against the Riemann autocorrelation forces coefficient rigidity. A
quantitative connection from source resonance energy to that null-test pairing
would close the missing implication, but none has been proved. It is the next
specific producer obligation to investigate, rather than adding more covariance
wrappers. C37 has not retired a mathematical route or disproved hW rigidity.

## Cycles 38--39: null-test and unitary-transfer attacks

C38 candidate: the actual null-test deficit E=-atomPairing(lam-Lambda,K)
is bounded by a finite source constant times centered critical variance V.
This would make V=0 a rigidity criterion. OPEN; no proof or new source theorem.
Existing quantitative exposedness gives |T(K,H)|^2 <= E*cost(H), the opposite
direction. The spectral pairing with the finite Bochner measure retains a
CauchyBounded excess hypothesis. Neither result supplies E<=C*V. Abstract
finite coefficient perturbations again obstruct estimates from the bare
logarithmic seminorm. They do not refute the conjecture under hW.

C39 candidate mechanism: the actual unit-valued phase multiplier might preserve
the critical resonance norm and force K=|B|^2. The asserted isometry on the
resonance completion is UNPAID. Pointwise unit norm gives an isometry in ordinary
L2, but the radial resonance functional is not an ordinary bounded L2 functional.
The existing ResonanceEnergy/ResonanceMean modules explicitly identify its
unbounded norm and discontinuity. Completeness, invariance of the arithmetic
frequency subspace, and passage through the critical radial limit have not been
proved. RealResonance does not assert noninteger reflected residues vanish.
The corpus recipe replacing actual-source phase by an unrelated finite local
model is invalid. This closes the shortcut, not the phase research route.

External check: Perelli--Righetti, arXiv:1702.01683, concerns approximation by
vertical translates in the half-plane of uniform convergence. It does not
supply the critical radial uniformity missing here. A publisher PDF on converse
theorems returned403; no theorem was taken from that unread source. Broad
search hits claiming RH reductions were not used as evidence.

## Cycle 40: exact valuation residues of the actual forward source

Candidate: for every prime p and k>=0, the actual ratio
L(valuationPart p k sourceCoeff,sigma)/L(sourceCoeff,sigma) has a finite real
limit as sigma decreases to1. No canonical value or positivity for k>0 is
asserted. This addresses the valuation information discarded by C30 and
exposed by C32. It does not itself settle WP05.

Dependency-closed paper mechanism:
Let f=lamLog, f0=coprimePart p f, h=f-f0, a=exp_star f, a0=exp_star f0,
b=exp_star h. Absolute convergence for sigma>1 and scalar exponential
multiplication give a=b star a0 by Dirichlet-series uniqueness. Coprime
projection gives a0=coprimePart p a. Every nonzero coefficient of h is divisible
by p, so h^(star r) is supported on multiples of p^r. Therefore the kth exact
valuation part of b equals the finite sum over 0<=r<=k of the kth valuation
part of h^(star r), divided by r!.

Exact valuation projection of a convolution is the finite sum of convolutions
of valuation-j and valuation-(k-j) parts. Consequently each L-series of a
fixed valuation part of h^(star r) is a finite polynomial in the L-series
L_j=L(valuationPart p j f,sigma), j=1,...,k. C33 gives every such L_j a finite
real endpoint and O(sigma-1) error. The constant power is the Dirichlet unit.
Thus L(valuationPart p k b,sigma) has a finite real endpoint, namely
[z^k] exp(sum_(j=1)^k ell_j z^j). Convolution with a0 commutes with valuation
projection, so the requested ratio is exactly this finite polynomial times
L(a0,sigma)/L(a,sigma). C30 supplies that positive real ratio's endpoint.
This proves existence at every k (and finite-level linear errors if retained).
All sums in the valuation-depth argument are finite; no limit interchange
in k, p, or a prime set, coefficient sign, or Euler product is used.

Novelty classification: BRIDGE/source endpoint producer; exponential generating
function algebra is standard, independent scientific novelty unestablished.
The capstone must quantify over every k, rather than sampling a few depths.
Formal plan: valuation convolution splitting; supported exponential truncation;
actual source exponential factorization; finite endpoint induction; capstone;
targeted builds, direct audits, axioms, wiring, cleanup.

External comparison checked during C40: Cormac O'Sullivan, *De Moivre and Bell
polynomials* (March 5, 2022),
https://fsw01.bcc.cuny.edu/cormac.osullivan/Research/demoivre-paper.pdf,
records the finite power-series coefficient algebra and its convolution
recurrences. Mahipal Gurram, https://arxiv.org/abs/2605.22784 (May 21, 2026),
has an abstract about Bell transforms, arithmetic functions and Dirichlet
convolution; only the abstract was inspected, so no detailed theorem comparison
is claimed. Neither source is used as an unproved Lean dependency. C40's
candidate contribution is the actual-source endpoint producer using the
corpus's C30 and C33 results, not the classical polynomial identity itself.

## Cycles 41--42: screen the remaining phase producer

C41 screening question: do fixed-depth endpoints plus the uniform divisibility
tail identify the canonical local profile? The tail estimate pays tightness in
valuation depth, but does not determine the finite-depth values. C32 already
shows noncanonical local polynomial freedom in abstract models, not in hW
sources. No proof or disproof of canonicality for the actual source was found.
The scalar normalization/finite-energy direction is insufficient as a phase
detector; no new wrapper or duplicate model module is added.

C42 screening question: does an existing source theorem or distributional
converse theorem remove the residual fractional/diffuse measure? Two refreshed
deep corpus searches recover exact phase coupling, local finiteness, integer
floor domination, conditional near-integer/mixed-spectrum receivers and the
special higher-denominator multiplicity results. None of these returned
statements supplies general source integrality or removes diffuse mass.
The first proposed search recipe again conflates local/S-finiteness with total
finiteness and unrelated phase shifts with the actual cumulative phase; the
second assumes the atomic representation it needs to produce. Both are rejected.

External audit: Booker, https://arxiv.org/pdf/1308.3067, Definition 1.3(A3),
requires discrete spectral support and integer masses outside finitely many
exceptions. Theorem 1.7 classifies that class, not arbitrary positive boundary
measures. Kaczorowski--Molteni--Perelli (2010),
https://sites.unimi.it/molteni/research/papers-pdf/23-molteni-A_converse_theorem_for_Dirichlet_L-functions.pdf,
states Hamburger's theorem with full functional equation and finite-order
continuation. Those hypotheses remain unpaid for the current source. Search
engine crawl dates are not these papers' publication dates. No classification
is imported, no source conjecture is refuted, and WP05 remains OPEN.


## Cycles 43--45: source restrictions still missing

C43: native spectral-law weak closure can lose energy. The returned
WeilPaperEnergyFiberClosure statements exhibit nearby native points with
arbitrarily larger energy; this supplies no upper bound for the actual-source
variance. Source read, not recompiled or imported. No actual hW counterexample.

C44: local H^(1/2) regularity of the canonical unit phase would forbid nonzero
jump discontinuities, because the cross-jump fractional energy diverges.
But regularity of the trace F does not imply regularity of F/conj F at its
zeros. Actual quantization Gaussian phase identities retain an uncontrolled
energy defect. Even unit-phase regularity would not by itself remove smooth
diffuse mass. Thus the desired source estimate remains OPEN; no division at
zeros or unsupported regularity claim is made. Brezis--Mironescu's author-hosted
2021 book summary was inspected, not used as a proof of this source estimate.

C45: refreshed rigidity search returned receivers retaining coefficient order,
summability, atomic representation, or counting-integrality hypotheses.
The RH/full-positivity equivalence concerns von Mangoldt specifically.
No returned statement proves arbitrary-source phase settlement.

## Cycle 46: scale-adapted phase regularization

Initial candidate BRIDGE (final audited range below is Y>=4): from original hW alone, for Y>=2 and 0<eta<=1,
E(Y,eta) = integral_[Y,2Y] |regularizedPhase_eta-canonicalPhase|
<= C_hW eta Y log(Y+3) log(1+6Y/eta).
This would allow power-saving relative error at every polynomially shrinking
width. It does NOT yield settlement: the existing cancellation bound requires
eta^2 log Y large, outside the region where this error is small.

Parent theory / attack: logarithmic Poisson smoothing of interval indicators
is classical. Acuna Valverde, arXiv:1502.06139v3, Theorem1.1(ii), gives the exact
one-dimensional Cauchy heat-content formula. arXiv:1602.04499 develops the
finite-perimeter parent setting. Both primary PDFs opened. No independent
scientific novelty is claimed for the kernel mechanism. The actual-source
quantitative improvement is the proposed corpus contribution.

Paper proof plan, before coding: use w_Y(r)=Y/(Y^2+r^2), whose integral is
Re weilContinuation(1/2+Y). The elementary endpoint bound gives
windowError <= 8eta/(eta+|y-r|)+8eta/(eta+|y+r|).
For |r|<=4Y, translation into [-6Y,6Y] bounds its y-integral by
32eta log(1+6Y/eta). Since w_Y >=1/(17Y) there, this is bounded by
544eta Y log(1+6Y/eta) w_Y. For |r|>4Y, C9's far estimate gives
integral_y windowError <=32eta Y^2/(1+r^2)
<=64eta Y w_Y, absorbed by the same coefficient since log(1+6Y/eta)>1.
Fubini and the existing exact phase comparison prove the estimate with
Re weilContinuation(1/2+Y) in place of C_hW log(Y+3).
[OPEN CORE for final logarithmic corollary]: verify the corpus real-axis
archimedean bound and the source Dirichlet-series bound uniformly for Y>=2.
No Lean code until this last paper dependency is verified.


C46 paper closure: the refreshed real-axis search found the stronger existing
`WeilSpectral.exists_re_herglotzFunction_le_log`, valid for Re v>=4, with
Re H(v)<=log(||v||+1)/2+K_hW. The continuation differs from H(s-1/2) by a
pure imaginary constant. Hence Re W(1/2+Y)<=log(Y+1)/2+K_hW for Y>=4.
Take Y>=4 (the asymptotic target needs no smaller heights), absorb K_hW into
(1+K_hW)log(Y+3), and the C46 proof above is dependency-closed. No new
archimedean or coefficient estimate is needed. Raw constant544 remains valid:
log(1+6Y/eta)>=1, so it absorbs the far coefficient64. Positive integrands,
C9 product integrability, and the Poisson identity justify every integral.
Formalization proceeds for Y>=4 in the source-log capstone, Y>=1 in the raw
Poisson-moment estimate. No added source premise.

C46 scale consequence (paper, not yet a separate Lean corollary): for fixed
epsilon>0 and eta=Y^(-epsilon), the displayed capstone gives
E/Y <= C_epsilon Y^(-epsilon)(log Y)^2 for large Y, hence
O(Y^(-epsilon/2)). This preserves a power-saving passage from interior to
boundary at any polynomial width. It supplies no interior concentration.
In contrast C10 gives 18/(eta^2 logY), which is vacuous at those widths.
Thus the new estimate closes a rate defect, not the source phase producer.


## Cycles 47--48: phase regularity and coefficient signs

C47 screening: the exact native Gamma-energy formula is an amplitude-weighted
phase discrepancy. Finite native energy does not bound the unweighted unit
phase at amplitude zeros. The search returned no link paying a local compact
Hankel or H^(1/2) statement for canonicalPhase. Fisher--Hartwig determinant
asymptotics concern prescribed symbols, and are not a producer for this source.
This is an unresolved source route, not a no-go theorem or new invariant.

C48 competing source-sign conjectures, well-typed since sourceCoeff is complex:
(A) for every lam and hW : WeilPositiveFull lam, every n satisfies
0 <= (sourceCoeff lam n).re and (sourceCoeff lam n).im = 0;
(B) some lam, hW and n satisfy (sourceCoeff lam n).re < 0. The stronger logarithmic claim is lam(n)>=0 for n>=2. These are
exact assertions about the existing source, not new input hypotheses.
Candidate mechanism: derive positive definiteness of the normalized source
Dirichlet series from the canonical positive spectral measure. [OPEN CORE]:
the proved positive-definite spectral kernel and negative-deviation potential
are NOT that normalized source function. Exponentiating an unrelated kernel
does not supply the missing identity. No sign theorem is claimed.

External attack: Nakamura, arXiv:2209.13257, Theorem1.5 and Main Theorem,
place positivity of ordinary/logarithmic coefficients exactly at the
characteristic-function/infinite-divisibility boundary. Using that classification
to create signs from an unproved characteristic-function claim is circular.
Nakamura--Suzuki, arXiv:2306.08317, Theorems1.1--1.2 treat an exponential of a
specific zeta-zero potential, not the normalized arbitrary-source Dirichlet
series. That distinction prevents importing an RH criterion as a sign producer.
Verdict for the classification shortcut: CIRCULAR. The original source-sign
conjectures remain OPEN. Next interrogation: what actual arithmetic identity
could identify a positive-definite kernel with the source ratio? No duplicate
conditional receiver is to be added before this is answered.

## Cycles 49--50: exact-source deformations and analytic geometry

C49 competing candidate: construct lam and hW with some n>=2 for which
(sourceCoeff lam n).re<0, retaining the exact Gamma datum and pole weight1.
This would refute C48(A), not merely an auxiliary coefficient-sign argument.
No such source is constructed. Two deep searches inspected20+20 each; no
returned theorem produces this deformation. Exponential-sum sign recipes
require positive coefficients already and do not identify the actual source.

Stable-polynomial deformation shortcut: Kurasov--Sarnak arXiv:2004.05678
formula(27) retains a nonzero h(0) conductor contribution. Adding its positive
spectral measure does not preserve our exact archimedean functional. Their
introduction explicitly distinguishes the prime explicit-formula example from
a Fourier quasicrystal, even under RH. Alon--Cohen--Vinzant arXiv:2303.03201v3
Corollary1.4 classifies N-valued Fourier quasicrystals; integer/discrete masses
and the Fourier-quasicrystal hypotheses are unpaid here. Verdict for that
classification shortcut: CIRCULAR / outside the exact hypothesis class.
The original C49 existence conjecture remains OPEN. Existing corpus conductor
obstructions already formalize the positive survivor for quadratic-character
mixtures, so no duplicate no-go theorem is added.

C50 geometric screening: sourcePrimitive has derivative weilContinuation,
whose real part is nonnegative. Inferring phase quantization from this analytic
property alone is FALSE: on the right half-plane, P(z)=a*log(z), a>0, has
Re P'(z)>0, while exp(P) has arbitrary positive boundary branch exponent a.
The horizontal-segment proof of log-primitive injectivity when Re P'>0 is
classical and gives no arithmetic integrality. This example is not an hW
source. Positive survivor: analytic geometry controls monotone lifted phase;
that mechanism is already formalized in WeilLinearTwistPositivity (e.g.
antitone_im_vpt). No new Lean wrapper or claimed source counterexample.
Next conjecture must use the discrete arithmetic source, not positivity of
the logarithmic derivative in isolation.

## Cycles 51--52: arithmetic modes omitted by scalar energy

C51 exact prospective assertion: for every hW, every nonprincipal Dirichlet
character chi modulo q, ((sigma-1)*LSeries(chi*sourceCoeff lam,sigma)) tends
to0 as sigma decreases to1. This is a weaker assertion than finite twisted
LSeries limit, which must not be silently substituted. It would eliminate
character residue modes; it would NOT identify principal/coprime residues.
Its competitor is an actual hW with a surviving nonprincipal character pole.
Neither is proved. The refreshed20+20 statements do not supply the twist
producer. Continuous height modulation is not a Dirichlet character twist;
existing quadratic-character mixtures carry an explicit conductor defect.
The unresolved core is the literal source twisted residue, not twist notation.

C52 reassessment of C35: individual prime-depth endpoints and uniform deep
valuation tails do not establish logarithmic square-mean exhaustion by finite
divisibility polynomials. The earlier character diagnostic is still decisive
against generic density: a nonprincipal character has positive logarithmic
square mean but pairs to zero with every divisibility indicator. It is not an
hW counterexample. Bessel bounds give only one inequality. Reading a bounded
projection norm as full-energy equality would assume the open orthogonal
complement vanishes. No new finite-profile wrapper is warranted here.
Verdict: original C35/C51 source assertions remain OPEN; a claim that C40
automatically closes C35 would be FALSE as an abstract inference.

## Cycle 53: positivity is not the Markov property

A candidate C48 sign mechanism was to promote full Weil positivity to a
positivity-preserving semigroup and extract coefficient signs from its jump
kernel. The required intermediate statement is a modulus contraction for
the exact quadratic form on every aperture, allowing a scalar lower-bound
shift. It is FALSE in the existing corpus: SuzukiScrewDisjointCrossCoupling
constructs disjoint nonnegative bumps with positive regular cross pairing,
avoiding every log(n) atom, and proves no scalar shift satisfies Beurling--Deny.
CCMThetaModulusObstruction additionally proves an exact smooth modulus
increase surviving every continuous local potential. These exact source
statements were read, not replaced by a toy operator. This does not refute
C48's coefficient-sign conjecture; it refutes the proposed semigroup producer.

Primary audit: Suzuki arXiv:2606.09096v3 (September24,2026), Theorem1.4 and
Section5 use the limiting small-aperture logarithmic Dirichlet form. They do
not assert an all-aperture Markov property for the full arithmetic form.
Positive survivor is the limiting Markov form/small-aperture ground result,
already treated in SuzukiLimitingLogClosedMarkov and related corpus modules.
Verdict: FALSE shortcut, REDISCOVERED obstruction/survivor; no new Lean file.

Next research checkpoint: preserve C46 as the sealed rate improvement.
Return to the literal source concentration producer. C48 signs and C35
critical-energy exhaustion are still competing structural possibilities,
not proven routes to settlement. Require an exact source estimate that
preserves the Gamma/pole terms and handles the unresolved arithmetic tail;
do not introduce another conditional representation or generic positivity
principle. No source theorem is to be coded without paper closure.

## Cycle 54 entry: enlarge the arithmetic approximation class

The C35 diagnostic suggests separating finite-divisibility data from all
periodic arithmetic data. Exact candidate, original hW only: for every e>0
there exist q>=1 and b : N -> C with b(n+q)=b(n) for all n, and N0>=2, such
that for every N>=N0,

  sum_(1<=n<=N) |sourceCoeff(lam,n)-b(n)|^2/n <= e*log N.

This allows nonprincipal character components excluded by the earlier
divisibility algebra. Its competitor is an actual hW whose centered source
has positive critical square energy invisible to every periodic sequence.
Neither is proved. This is not a density tautology: irrational additive
oscillations give non-source comparison sequences invisible to every rational
periodic mode. No assertion about an actual hW follows from that comparison.
[OPEN CORE]: obtain a uniform source tail estimate for periodic projections
from full positivity and the exact Gamma/pole datum. Finite projection bounds
and pointwise residue limits do not suffice. This statement does not by
itself settle phase. Next cycle must first audit whether the corpus already
proves this or a stronger source assertion, then attack novelty and the
source-tail mechanism before any Lean edit.

## Cycle 54 audit and Cycle 55 entry

C54 verdict: SURVIVES PRELIMINARY ATTACK, still OPEN. All20 candidate and
20 source-argument statements in the deep search were inspected. Reciprocal
vertical mean-square approximation is not approximation of sourceCoeff in
logarithmic mean over integers. The search recipe repeats that reciprocal
result and leaves the required summability/limit exchange unpaid. No producer
for rational periodic exhaustion was found. Search partial=false, no errors;
semantic coverage unmeasured, refresh incomplete (background indexer).

Primary parent audit: Erdos--Kac--van Kampen--Wintner (1940),
https://users.renyi.hu/~p_erdos/1940-09.pdf, explicitly restricts to strongly
multiplicative sequences. arXiv:1609.08183 defines the periodic closure in
ordinary Cesaro square mean and asserts its residue means inside that closure.
Frantzikinakis--Lemanczyk--de la Rue, arXiv:2304.03121, Theorem2.6 assumes
a unit-disc-valued multiplicative function and convergence of the complex
prime defect sum. Their more general pretentious result gives subsequential
approximation with phase factors. None supplies C54 for this nonmultiplicative
source. No Lean edit is justified for C54.

C55 exact candidate (stronger than merely recording C40 endpoints): for each
prime p, the actual real endpoint sequence u_k from C40 has a generating
function U_p(z)=sum_k u_k z^k analytic and nonvanishing on |z|<sqrt(p), with
U_p(0)>0 and U_p(1)=1. Original hW is the only source premise. No positivity
of u_k or multiplicativity of sourceCoeff is asserted. Competitor: an actual
hW for which this local residue function acquires a zero in that disk.

Proposed mechanism to audit before Lean: twist coefficients by z^v_p(n).
The twist respects Dirichlet convolution although the source need not be
multiplicative. For sigma>1, Cauchy--Schwarz gives absolute convergence for
|z|<p^(sigma/2) from square-energy convergence. The twisted source is the
exponential of the twisted logarithm and hence nonzero. C40 coefficient
limits and a geometric uniform bound give locally uniform convergence of
normalized twists on |z|<sqrt(p). Hurwitz and U_p(0)>0 would give nonvanishing;
U_p(1)=1 follows from the exact untwisted ratio.
[OPEN CORE]: audit every summability and normal-family bound in this argument,
including the logarithmic source; verify no stronger corpus theorem exists.
This is a prospective source BRIDGE, not an assertion of scientific novelty
or phase settlement. Even if proved, local normalization cannot remove
energy invisible to all finite arithmetic projections.

### C55 dependency-closed paper proof (before Lean)

Write a=sourceCoeff(lam), f=lamLog(lam), and A(s)=L(a,s). C40 supplies
u_k=lim_(sigma->1+) L(valuationPart p k a,sigma)/A(sigma), with u_k real
and u_0=r_p>0. The actual source residue is B=sourceCompletion(1) !=0
(DeletionPole / forward_source_residue). Choose one right neighborhood with
|(sigma-1)A(sigma)|>=|B|/2. C34 supplies one C for every p^k there.
Writing rho=p^(-1/2), the divisibility ratios are bounded by D*rho^k.
The valuation ratio is the difference of adjacent divisibility ratios, so
its norm is at most 2D*rho^k. This uses no signs and no limit exchange.
Hence |u_k|<=2D*rho^k and their power series U converges locally uniformly
on |z|<sqrt(p), as do the ratio power series U_sigma, to U. All coefficients
of U are real. For z=1, each U_sigma(1)=1 by the disjoint valuation partition
and absolute convergence of A. Thus U(1)=1; U(0)=r_p>0.

For nonvanishing, fix sigma>1 and |z|<sqrt(p). The source square series
sum |a(n)|^2/n^sigma is finite by its existing logarithmic energy bound
and Abel majorant. The logarithmic source square series is finite too:
WeilPrimitiveSetMeanSquare bounds the jth dyadic block of lam^2 by
O(2^j(j+1)^2), so summing after multiplication by 2^(-j*sigma) converges;
|f(n)|<=|lam(n)|/log 2 for n>=2 and f(0)=f(1)=0.
The mask square series is exactly
  sum_(n>=1) |z|^(2v_p(n))/n^sigma
   = zeta(sigma)*(1-p^(-sigma))/(1-|z|^2*p^(-sigma)),
by writing n=p^k*m with p not dividing m. It is finite because
|z|^2<p<p^sigma. Cauchy--Schwarz therefore makes both twisted Dirichlet
series absolutely convergent. The weight z^v_p is completely multiplicative
on positive integers, including z=0 with 0^0=1, so twisting commutes with
every finite convolution power and its absolutely convergent exponential.
Consequently U_sigma(z)=exp(L(z^v_p f,sigma)-L(f,sigma)) is nonzero.
The same summability uniformly on smaller disks proves holomorphy. Hurwitz
applied along sigma_j=1+1/(j+1), using local uniform convergence and
U(0)>0, gives U(z)!=0 throughout the connected disk |z|<sqrt(p).
No boundary zero-free claim at |z|=sqrt(p) is made.

Attack verdict: BRIDGE. Both deep searches returned20 candidates+20 source
arguments, all statements inspected; no stronger source assertion found.
Their recipes did not provide this proof: one substitutes the unrelated
exposing-ray weight; the other repeats fixed-depth endpoints. Both searches
partial=false/no errors, semantic coverage unmeasured, refresh incomplete.
Parent mechanism is classical absolute convergence plus Hurwitz, not new
complex analysis. Primary Hurwitz reference opened:
https://www.math.stonybrook.edu/~bishop/classes/math627.S22/cf_notes.pdf.
The OSU PDF fetch failed; no proof was taken from it. No independent
scientific novelty established. Finite local analytic constraints alone do
not prove C54 or settled phase.

Implementation plan: (1) exact telescope/uniform valuation tightness;
(2) normalized real endpoint series and local uniform convergence;
(3) twisted exponential absolute convergence and disk Hurwitz;
(4) source capstone, direct audits, axiom/import/index/lint/cleanup.
No source statement is considered sealed until its exact capstone is audited.

C55 interpretation audit: nonvanishing would imply U_p(x)>0 for real
-sqrt(p)<x<sqrt(p), by real coefficients, continuity, and U_p(0)>0.
In particular the finite-prime valuation-parity twist has a nonzero positive
normalized pole ratio. This does not assert positive coefficients of U_p;
a signed exponential series can be zero-free and normalized. Nor is a
finite-prime twist a nonprincipal Dirichlet-character twist, which changes
infinitely many prime values. The distinction matters for C51 and C54.
The finite-prime perturbation diagnostics from C32 can have their polynomial
zeros outside this disk, so they are not eliminated solely by C55.

C55 implementation refinement: the twisted absolute-convergence step can use
the existing divisibility square-energy bound directly, avoiding a new exact
mask-mass identity. Apply it to |f| (as a real-valued complex sequence) to
bound each absolute valuation row by A_sigma*p^(-k/2). Sum after multiplying
by |z|^k, valid throughout |z|<sqrt(p), and use the unique valuation partition
to recover the twisted series. This suffices for both a and lamLog.
The lamLog square-energy summability follows from the paid dyadic lam^2 bound;
a further corpus search now checks for an already formalized version.

C55 further proof simplification: for the zero-free identity, only lamLog
requires a separate square-summability-to-twist lemma. Absolute convergence
of its twisted convolution exponential then supplies the twisted a-series
automatically. Thus no new sourceCoeff square-energy module is needed.
The normalized source power series is already locally uniformly analytic
near the radial endpoint by the Tightness envelope. Regroup the absolutely
convergent twisted a-series by its unique valuation to identify that analytic
series with the exponential ratio.

C55 Lean implementation details for remaining regrouping: define normCoeff
f(n)=ofReal(norm(f(n))). At real sigma, term(normCoeff f)=ofReal(norm(term f)).
Apply existing norm_divisibility_LSeries_sq_le_energy to normCoeff f, take
square roots, then dominate each absolute valuation row by its divisibility
row. This gives row_k<=sqrt(E_sigma*Z_sigma)*p^(-k/2). Summing weighted rows
uses summable_prod_of_nonneg; the proof pattern for exchanging row/column
sums is already in HTGeometry/DirichletConvolutionExponential.lean204--251.
The unique valuation decomposition identifies each column with the twisted
term. This produces LSeriesSummable(valuationTwist p z f) and the exact
valuation generating identity on |z|<sqrt(p). Use it first for lamLog, then
use LSeries_valuationTwist_dirichletExp for the actual source.

The local Hurwitz implementation is in new DiskHurwitz, using PerturbationZero's
exists_zero_of_sphere_domination on a small closed ball contained in the source
disk. It keeps both the punctured nonzero sphere and the positive center value;
no entire extension or zero-sequence premise is introduced. Not yet compiled.

### C56 candidate: endpoint independence across primes (OPEN; C55 audit continues)

Exact conjecture: for every actual hW and distinct primes p,q, the unique paid
coprime endpoints satisfy r(pq)=r(p)r(q). Equivalently, the endpoint of the
logarithmic source restricted to integers divisible by both p and q is zero:
D(p)+D(q)-D(pq)=0. Existing deletion endpoints pay existence; they do not pay
this equality. This is weaker than multiplicativity of every source coefficient
and weaker than vanishing of every mixed-prime logarithmic coefficient.
Competing conjecture: an actual hW has a nonzero mixed deletion endpoint.
[OPEN CORE] No producer or actual-source counterexample found. Do not convert
one-prime nonvanishing or a convolution split into independent Euler factors.

Two corpus searches (80 candidate/source statements inspected, plus20 lexical
hits in the second) recover C30/C35/C40 and C55's unfinished modules. The
sourceCoeff_prime_factorization splits noncoprime logarithm from coprime
source; it is not an Euler product. No returned theorem supplies C56.

Primary parent audit (8 October2026): Booker, L-functions as distributions,
https://arxiv.org/pdf/1308.3067, Definition1.3(A3), requires discrete spectral
support with only finitely many nonintegral masses before Theorem1.7's degree1
classification. Those are unpaid here. Kaczorowski–Molteni–Perelli,
https://sites.unimi.it/molteni/research/papers-pdf/23-molteni-A_converse_theorem_for_Dirichlet_L-functions.pdf,
conditions(i)–(iii) explicitly require continuation, prime-power logarithmic
support and functional equation. Their multiplicativity receiver cannot
produce missing source independence. Search crawl dates are not publication
dates. These are assumption audits, not a novelty or completeness claim.

C56 preliminary attack verdict: SURVIVES PRELIMINARY ATTACK, OPEN, no proof.
A coprime mask identity 1_(n,pq)=1_(n,p)1_(n,q) does not factor its weighted
source mean. Canonical mask orthogonality is likewise not source independence.
Even canonical one-prime marginals leave mixed interactions undetected.
Therefore C55 alone has no path to C56. Next investigation must address the
actual spectral/archimedean source coupling; do not spend a new formalization
cycle encoding this elementary failure as if it were scientific progress.
No C56 Lean code. The live formal task remains sealing C55.

### C57 candidate under investigation: actual critical second moment

The source spectral target is not an unweighted norm identity. Exact corpus
identity quantizationGaussian_energy_extraction controls 2E(T)-Q(T), where
E integrates |quantizationTraceF|² on positive heights with Gaussian weight,
and Q includes |canonicalPhase-1|². Q remains nonnegative and unpaid.

Candidate C57: every original hW admits C>=0 with E(T)<=C*T*log(T+3) for T>=2.
Competing possibility: an actual hW has unbounded E(T)/(T*log(T+3)). This is an
estimate on the actual critical trace, not a hypothetical source class. The
returned frontier supplies radial domination, subpolynomial pointwise bounds,
Gaussian integrability, and logarithmic coefficient square energy. None is
the proposed sharp height average. No proof yet: [OPEN CORE] uniformly recover
a finite-height critical mean square from the arithmetic source energy.
Carlson/Bohr long-time means at fixed interior abscissa do not permit a silent
moving-abscissa or boundary interchange. Likewise Gamma-weighted trace L²
cannot be divided through vanishing amplitudes. Even C57 alone would not
settle phase: its use must control the nonnegative Q, not erase it.

Research ledger: two new hybrid searches,80 candidate/source statements
inspected, partial=false/errors=[], semantic coverage unmeasured, background
refresh incomplete. Sources archived cycle57-phase-energy-search.json and
cycle57-critical-moment-search.json. No C57 Lean work authorized by a proof;
continue external parent and exact-statement attacks before selecting a route.

C57 external parent audit (8 October2026, primary texts opened):
- Hedenmalm–Lindqvist–Seip, https://arxiv.org/pdf/math/9512211, Theorem4.11
  controls unit-height L² at real part1/2 by the unweighted coefficient ℓ²
  norm. For the shifted source a_n*n^(-1/2-eta), it controls original real
  part1+eta, not1/2. The half-plane shift is essential.
- Brevig–Kouroupis, https://arxiv.org/pdf/2510.05793, Theorem1 assumes a
  uniform height-mean bound; it cannot produce that same bound from analytic
  continuation alone. Almost-every-character conclusions do not identify the
  original untwisted source.
- Saksman–Seip, https://arxiv.org/pdf/0712.0492, Theorem1 gives bounded
  Dirichlet-series counterexamples to boundary Carlson limits and singular
  inner functions with arbitrarily small coefficient H² norm. This defeats a
  general boundary-interchange shortcut, not C57 for an actual hW.
- Chen–Fang–Guo–Hou–Shao–Zhou, https://arxiv.org/pdf/2609.11560v2,
  submitted10September2026/revised13September2026, Theorem1.1 claims the
  local embedding for every p>2. Its theorem statement retains the H^p norm
  and real-part1/2 sampling shift. It supplies neither missing source Hardy
  membership nor the moving-height boundary estimate. Only statement and
  applicability audited here; its121-page proof has not been independently
  verified in this task. Do not cite the non-even embedding problem as still
  open from older sources.

C57 preliminary verdict: SURVIVES PRELIMINARY ATTACK, OPEN. Its proof cannot
be obtained by deleting the uniform bound in Carlson or replacing almost
every vertical limit by the actual source. No counterexample satisfying the
actual hW was found. No paper proof, hence no C57 formalization.

C57 proof attack: radial domination can compare the critical trace to the
line1/2+eta, with a Gamma quotient costing a height factor depending on eta.
Choosing eta~1/logT keeps that cost bounded. The unpaid step is now effective
finite-height mean square on this moving line. A fixed-abscissa Carlson limit
has no uniform rate allowing eta to move. Truncating the source series at
length~T gives a plausible polynomial mean-value bound, but identifying that
polynomial with the actual continued source at the required precision is
unpaid; an approximate functional equation would already contain the unknown
reflected phase. Record this failure rather than assume such an equation.
Exact lexical research for quantizationGaussianEnergy returned its definition
only (no semantic coverage fields in lexical mode); exhaustive rg also checked
the signed-energy/extraction call sites. No missing upper-bound theorem found
among these available results. C57 remains open, not refuted.

## Cycle 58: centered arithmetic energy is the phase cost

8 October 2026. C57 remains OPEN: its proposed critical second-moment ceiling
has no source proof. The new target keeps the complete phase defect instead
of trying to erase it while estimating the uncentered trace.

Let `hW : WeilPositiveFull lam`, `B = sourceCompletion hW 1` (real),
`F(t) = quantizationTraceF hW t`, and
`H(t) = quantizationCenteredTrace hW t = F(t)-B*zeta(1/2+it)`.
Write `w_T(t)=exp(-t^2/T^2)` and
`E_c(T)=integral_(0,infinity) |H(t)|^2 w_T(t) dt`.
The exact candidate is

    exists C >= 0, forall T >= 1,
      |quantizationGaussianDefect hW T - 2*E_c(T)| <= C*T^(5/6).

Competing candidate: an original full-positive source for which this
normalized discrepancy is unbounded. The constant is source-dependent;
there is no coefficient sign, Euler product, atomicity, continuation through
the critical line, or source functional-equation premise. Initially the
[OPEN CORE] was a sublinear signed second moment of the pole-centered source.
It is paid below by signed hyperbola cancellation, not a critical mean-square
upper bound.

### Attack and novelty audit

The old signed Gaussian theorem concerns `F^2` and retains its polar term.
Centering at B is essential: subtracting an arbitrary constant times zeta
would leave a pole and a linear-size coefficient contribution. The new
identity controls the difference of two nonnegative energies, not either
energy separately. It does not prove `Q=o(T)`, `E_c=o(T)`, V=0, or WP05.
The September 2024 Broucke--Hilberdink mean-value theorem assumes positive
coefficients; with summatory error exponent beta its mean-value boundary is
(1+beta)/2. It cannot pay C57 here. Their result is not used in this proof.
Coppola--Laporta's weighted Gallagher argument (2014) is a classical
short-window/mean-square transfer, not a source window estimate. The
hyperbola decomposition below is classical. No independent scientific
novelty claim is made for these tools.

Corpus searches on the exact centered phase-energy mechanism return the
uncentered `quantizationGaussian_energy_extraction`, literal centered source,
Gaussian Fourier recovery, and the Abel disorder receiver, but no returned
centered signed-energy estimate. Search coverage is recorded separately.
Verdict: BRIDGE. New intended corpus content is an actual-source global
phase/arithmetic energy identity with sublinear error. Its significance is
that any surviving phase disorder must have matching pole-centered critical
energy; local valuation compatibility alone cannot hide that cost.

### Dependency-closed paper proof (before Lean)

1. Put b(0)=0 and b(n)=sourceCoeff(lam,n)-B for n>=1. The existing source
   summatory theorem at epsilon=1/16 gives a constant A>=0 with
   |S_b(N)|<=A*(N+1)^(9/16), all natural N. For N>=1 replace A by
   A*2^(9/16) to obtain |S_b(N)|<=A_1*N^(9/16); at zero the sum is zero.
   The centered absolute Dirichlet series at nu=17/16 gives the finite
   number M=sum_(n>=1)|b(n)|/n^nu. Both facts follow from original hW.

2. Set alpha=9/16 and q=(alpha+nu)/2=13/16. For X>=1 integer and
   r=floor(sqrt(X)), the finite hyperbola inclusion-exclusion identity is

     S_(b*b)(X)=2 sum_(m<=r) b(m) S_b(floor(X/m))-S_b(r)^2.

   Every pair mn<=X has m<=r or n<=r; their overlap is the entire square
   m,n<=r. This proves the formula without rearranging an infinite series.
   Since floor(X/m)<=X/m and alpha>=0, the first term has norm at most

     2*A_1*X^alpha sum_(m<=r) |b(m)|/m^alpha
       <=2*A_1*M*X^alpha*r^(nu-alpha)
       <=2*A_1*M*X^q.

   The overlap has norm <=A_1^2*r^(2*alpha)<=A_1^2*X^alpha<=A_1^2*X^q.
   Thus |S_(b*b)(X)|<=D*X^q for every X>=1, D=2*A_1*M+A_1^2.
   At X=0 both sides vanish. This estimate retains signed coefficients.

3. Put c=b*b and g_T(x)=exp(-4*pi^2*x^2/T^2). Absolute convergence of
   L(c,9/8) pays summability against g_T. Finite summation by parts gives

     sum_(n<=N) c(n)g_T(n)
       =S_c(N)g_T(N)+sum_(n<N) S_c(n)(g_T(n)-g_T(n+1)).

   The endpoint tends to zero, since N^q exp(-a*N^2) tends to zero for a>0.
   Moreover g_T is decreasing on [0,infinity), and
   g_T(n)-g_T(n+1)=integral_n^(n+1)(8*pi^2*x/T^2)g_T(x)dx.
   On this interval n^q<=x^q. Therefore

     |sum c(n)g_T(n)|
       <=D integral_0^infinity (8*pi^2/T^2)*x^(q+1)*g_T(x)dx
       =D*T^q * integral_0^infinity 8*pi^2*u^(q+1)*exp(-4*pi^2*u^2)du.

   The last integral is finite: q+1> -1 at zero and Gaussian decay dominates
   every power at infinity. This also justifies passage in the finite Abel
   identity. For T>=1, T^q<=T^(5/6).

4. On the open right critical half-plane, use the existing holomorphic
   filled centered source H(s)=quantizationCenteredProdF hW s. Its literal
   coefficients are b on Re(s)>1, hence H(s)^2=L(c,s) there. The function
   chi(1-s)H(s)^2 g_T(s), with g_T(s)=exp((s-1/2)^2/T^2), is holomorphic
   throughout 1/2<Re(s)<=3/2, including at s=1. Here chi(1-s) is analytic
   because its denominator Gamma_R(s) is nonzero; it has no pole at one.
   The centered source has a uniform linear bound on the strip, including
   a single radial majorant. The Gamma-ratio bound is polynomial. Gaussian
   decay thus supplies an integrable O((1+t^2)^(-1)) bound for each T,
   uniform across the strip. Rectangle contour shifting and dominated
   radial passage give, with no residue,

     J_c(T):=integral_R chi(1/2-it) H(t)^2 w_T(t)dt
       =2*pi*sum_(n>=1)c(n)*leftKernel(T,n).

   The series interchange occurs only on Re(s)=3/2 where it is absolute.
   Exactly the existing scalar kernel extraction is used. The universal
   bound n^(9/8)|leftKernel(T,n)-2*g_T(n)|<=K*T^(5/6), together with
   L(c,9/8) absolute summability, gives

     |J_c(T)-4*pi*sum c(n)g_T(n)|<=K'*T^(5/6).

   Step 3 proves |J_c(T)|<=C*T^(5/6).

5. For s=1/2+it, put u=chi(s); |u|=1. The genuine zeta functional equation
   gives zeta(s)=u*conj(zeta(s)), unconditionally; no equation for F is used.
   B is real, so F-u*conj(F)=H-u*conj(H). The existing canonical phase
   identity gives, almost everywhere for t>0,

     |canonicalPhase(t)-1|^2 |F(t)|^2
       =|H(t)-u*conj(H(t))|^2
       =2|H(t)|^2-2 Re(chi(1-s)H(t)^2).

   This algebra is valid also when F or zeta vanishes. It divides by neither.
   Real symmetry H(-t)=conj(H(t)) and chi(conj(s))=conj(chi(s)) show
   J_c(T)=2*integral_(0,infinity) Re(chi(1-s)H(t)^2)w_T(t)dt.
   Every displayed integrand is integrable by the previously paid polynomial
   bounds and Gaussian factor. Integration therefore gives the exact law

     quantizationGaussianDefect(hW,T)=2*E_c(T)-Re(J_c(T)).

   Step 4 completes the candidate estimate, with no remaining paper premise.

Formalization status: NOT YET FORMALIZED. No C58 theorem is claimed verified.
Next stronger question: can the original Weil form force this actual centered
energy to be o(T)? C58 alone supplies no upper bound and cannot answer it.

### C58 stronger smoothed estimate (paper audit, 8 Oct 2026)

The hyperbola bound remains a valid unsmoothed statement. For the Gaussian
step, existing `WeilWorkQuantizationGaussianMellin` permits a stronger direct
argument. Fix `c` with `1/2 < c < 1`. Put
`Psi(s) = Gamma(s/2)/2 * H(s)^2` and `x=2*pi/T>0`.
On `c <= Re s <= 3/2`, `Psi` is holomorphic: the centered source has its pole
filled, and `Re(s/2)>0`. Existing centered tail bounds give
`|H(s)| <= A(1+|Im s|)`. The corpus Gamma strip bound gives a polynomial times
`exp(-pi*|Im s|/4)`. Thus `x^(-s)*Psi(s)` has uniform quadratic decay on this
closed strip for each fixed x. Indeed `|x^(-s)|=x^(-Re s)` is at most the sum
of its two endpoint powers, and exponential decay absorbs every polynomial.
The residue-free vertical contour theorem therefore equates lines 3/2 and c.
Absolute Dirichlet convergence of the centered convolution on 3/2 justifies
Gaussian Mellin inversion there. On line c, the inverse integral is bounded
by `x^(-c)/(2*pi) * integral_R |Psi(c+it)| dt`. The latter integral is finite,
by continuity on a compact interval and the same quadratic tail bound, and
independent of T. Consequently the actual centered convolution Gaussian sum
is `O_c(T^c)` for every fixed `c` in `(1/2,1)`. Choosing `c=3/4` improves the
paper's `13/16` smoothed exponent; the independent kernel error `5/6` still
determines the C58 phase-energy discrepancy. No boundary-energy estimate is
obtained by taking an absolute value of this signed Gaussian sum.

### C58 direct obstruction corollary (paper proof before Lean)

Combining the exact C58 discrepancy with the existing source-only Gaussian
coefficient-detection dichotomy gives a quantitative alternative for the
original canonical phase itself:

    arithmetic rigidity and RH, or exists kappa>0 such that eventually
    quantizationGaussianDefect(hW,T) >= kappa*T.

Indeed in the second existing branch E_c(T)>=kappa*T. Since
`C*T^(5/6)/T=C*T^(-1/6)->0`, eventually `C*T^(5/6)<=kappa*T`.
Then C58 gives Q(T)>=2*E_c(T)-C*T^(5/6)>=kappa*T. All constants are
source-derived. This is a phase-cost obstruction, not a producer eliminating
its second branch. It introduces no extra source hypothesis. Its scientific
novelty beyond the corpus/literature is not established.

## Cycle 59 entry: pole-normalized completed quotient (OPEN CORE)

C58 separates signed analytic cancellation from positive physical energy.
A new producer candidate must use more than half-plane holomorphy/growth.
Let G be the actual source completion, B=G(1)>0, and let Z be the filled
completed zeta `s*(s-1)*GammaR(s)*zeta(s)`, with Z(1)=1. Since G is zero-free
on Re(s)>1/2, the actual quotient R(s)=B*Z(s)/G(s) is holomorphic there and
R(1)=1. No RH or zero-free assertion about zeta is needed to form R.

Conjecture C59: original hW implies |R(s)|<=1 throughout Re(s)>1/2.
Competing statement: some actual hW and s in that half-plane have |R(s)|>1.
A source derivation of the bound would close rigidity by the maximum modulus
principle and the coefficient normalization. This implication is classical;
formalizing the implication alone would not advance the frontier.

[OPEN CORE]: derive this very specific comparison from full arithmetic Weil
positivity. Positivity of Re(G'/G) alone does not compare G to completed zeta;
C50 already disproved the analytic-geometry shortcut on weaker data. Assuming
positivity of a difference with zeta's logarithmic derivative would import an
unpaid comparison and may import RH. Likewise Booker's degree-one classification
requires discrete almost-integral multiplicities (and its coefficient axioms),
which cannot be used as a producer for those same properties. Verdict of these
shortcuts: CIRCULAR or outside the actual hypothesis class. C59 itself remains
OPEN, with no paper proof and no Lean module. Quotient-specific corpus search
is in progress; check whether the claim is already a corpus receiver before
pursuing an exact finite-form or operator inequality for it.
