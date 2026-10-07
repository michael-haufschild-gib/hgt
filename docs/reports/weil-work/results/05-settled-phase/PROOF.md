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
