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
