# CCM-FU: complete reserve-extension induction

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] / direct proof attempt for frozen PE4
- **Parent:** [adaptive prime ceiling](ccm-fu-adaptive-prime-ceiling.md)
- **Primary goal:** Complete source bound, CCM-FU boundary transport, RH.

## Attempted complete proof

Write `Phi(P)=Q_P+2 sqrt(G_P D_P)` for the literal source at one cutoff,
and `B=Q_empty`. Initial parity gives `Phi(empty)=B`. The proved merger
estimate gives `Q_(P+p)<=Phi(P)` for every unprocessed prime p.

The missing induction step proposed here is: every proper P with
`Phi(P)<=B` has an unprocessed p such that either P+p is complete or
`Phi(P+p)<=B`. If established for every actual cutoff and state, induction
on the number of remaining primes constructs a complete PE4 order; its
terminal energy is bounded by the predecessor's certificate. This does
not assume a bound for the complete source.

This is a derived proof strategy, not a replacement or weakening of PE4.
The existing arbitrary positive-cube obstruction prevents deriving it from
unsigned positivity alone. The actual arithmetic field and its signed
overlaps must enter. A failure of this sufficient extension property does
not refute existence of a complete PE4 path.

## Frozen diagnostic

Use all 8860 saved states through cutoff32 in
`defect-reserve-reanalysis.json`. Do not regenerate channels, heads,
energies, or existing complete paths. Retain the input's original tolerance
`1e-12*max(1,B)` and every state, including degenerate cutoffs.

Test the exact local extension property above at every certified proper
state. Separately test the stronger homogeneous descent assertion
`min_p Phi(P+p)<=Phi(P)` over every proper state. For any failure, retain
all outgoing Q, G, D and Phi values, and whether P is reachable from the
empty state through certified predecessors. Do not select a larger budget
after a failure. Existing existence results do not predict whether all
certified states extend; this test distinguishes an inductive invariant
from a set that merely contains some successful paths.

Run only on RunPod with cutoff jobs distributed over at most eight workers,
a 60-second foreground limit, and no background jobs. Save exact script,
input hash, output and interpretation under `2-fully-proven/computations`.
Numerical evidence supplies no Lean premise. A passing finite test leaves
the all-cutoff induction open; a failing numerical witness must be
analytically verified before it is called a formal obstruction.

## Bounded hostile extension

The saved-data test passes all 7350 certified proper states, while the
stronger homogeneous descent assertion fails at 975 states. Its first
failure is M=7, P={2}. The all-cutoff extension statement is unchanged.

Before investing in its proof, test every subset state at every integer
cutoff33..64. Reuse the existing defect/unit-clock table; do not recompute
that source. Derive dilated coefficients by the exact clipped formula and
obtain all oriented fibres by subset summation with literal Möbius signs.
Check the original diagonals against the existing greedy summary, and
independently reconstruct every reported witness and each of its successors
by direct prime merging. Retain the same tolerance and extension predicate.
Use at most eight workers and a 60-second foreground deadline. This larger
test targets an unproved induction step, not another greedy pass. Record
all failing states and all outgoing values; a failure does not retire PE4.

## Present evidence and exact proof gap

The [saved RunPod outputs](../2-fully-proven/computations/ccm-fu-reserve-extension-2026-09-07/README.md)
contain no extension failure in either range. The extension covers all
1746944 subset states at cutoffs33..64, including 999880 certified proper
states. This is numerical evidence for the same induction statement, not
an all-cutoff proof or a Lean premise.

For a proposed next prime q, write `a_R=A_P(R)` and
`b_R=A_P(R+q)` for oriented coordinates on q-free labels. Then
`A_(P+q)(R)=a_R-b_R` and

`Q_(P+q)=Q_P-2 sum_R a_R b_R`.

If `r_P=(B-Q_P)/2`, the exact required comparison is

`sqrt(G_(P+q) D_(P+q)) <= r_P + sum_R a_R b_R`

for at least one unprocessed q, unless that merge completes the order.
The current certificate only gives `sqrt(G_P D_P)<=r_P`. It does not bound
the newly redistributed positive and negative parts. Replacing r_P by
`sqrt(G_P D_P)` would demand homogeneous certificate descent, which fails
already in the saved cutoff-seven source. Bounds for the first merger's
defect apply to oriented input and cannot be iterated after that hypothesis
is lost.

## Why the available local channel bounds do not close the induction

The following exact algebraic model tests the attempted proof, not the
literal arithmetic source. On a four-coordinate Boolean cube set
`A(R)=3+(-1)^card(R)`. Its positive values are 4 and 2, so every directed
child/parent ratio is at most two. Its initial energy is 160. After k>=1
distinct coordinate differences the surviving field is
`2^k*(-1)^card(R)`: the first difference removes the constant, and each
later difference doubles the parity part. For k=1,2,3 its energies are
32,64,128, and its geometric certificates are 64,128,256 respectively.
After k=4 its sole value is 16 and energy is 256.

Thus every first-prime reserve and every two-prime original-energy bound
holds in this model. Nevertheless every two-prime state is certified and
has no certified successor: the next state is still nonterminal and has
certificate256>160. Positivity, factor-two comparisons and initial reserve
estimates together do not imply the missing induction. These explicit
counts are paper algebra, not a new Lean certificate; no actual-source
claim or route retirement follows.

The positive information in this model is the exact separation of a
constant background from a higher-order parity component: all subsequent
growth belongs to that component. The source argument must control such
joint interactions in the actual arithmetic field. The common-head
identity alone supplies no bound on them. No replacement potential,
source-specific extension proof, complete uniform energy bound, or RH
proof is claimed here.

## Frozen final-overlap attack

Test the same universal extension claim on every actual state at every
integer cutoff65..1024 whose remaining primes form a subset of
`{p prime : p*p<M}` of cardinality two through five. Every other parent
prime is processed. These are complete source fields, not isolated chosen
packets. This targets the final overlapping sector; it does not repeat the
earlier all-subset enumeration or greedy-path searches. Saved defect and
unit-clock values supply the source. All states in this declared family
are tested, including every outgoing prime, at the original tolerance.

The empirical question is the actual certificate-extension claim. The
two-remaining-prime endpoint identity below is an analytic validation check,
not an uncertain numerical prediction. A failure must retain every
remaining coordinate and every successor. Independently audit every failed
field by direct signed source summation and exact support grouping before
interpreting it. No bound or state family is changed after observing a
failure. Run only on RunPod with eight workers, one-thread BLAS and a
60-second foreground limit; download and document outputs. No numerical
value may become a Lean premise.

The [final-overlap diagnostic](../2-fully-proven/computations/ccm-fu-final-overlap-extension-2026-09-07/README.md)
tests all306999 states in this declared family. All54466 certified states
extend. This supplies no universal inequality and no Lean premise.

## Terminal arithmetic burden

If only one prime remains, let x and y be its two oriented coordinates.
The complete signed source is x-y. Its certificate is exactly

`Phi=max(x^2+y^2,(x-y)^2)`.

Indeed, equal signs give defect energy zero or good energy zero, hence
Phi=x^2+y^2; opposite signs give Phi=(abs(x)+abs(y))^2=(x-y)^2.
This is elementary paper algebra, not a new formal certificate.

Consequently, when two primes remain and the current state is certified,
every successor has energy at most B by the existing Lean merger bound.
Such a successor is certified if and only if the complete signed source
square is at most B. The proposed induction therefore still contains the
terminal SD1 comparison; a proof cannot treat this comparison as already
available. The positive-cube discussion above shows the insufficiency of
local hypotheses, but does not justify locating all remaining difficulty
only in high-dimensional fields. The actual arithmetic endpoint must also
be controlled.

## Cutoff quantifiers required by the receiver

`MobiusDivisorSquareRootAbelBounded` in
`CCMFUSuzukiMobiusDivisorAbelProducer.lean` requires one B at **every**
integer cutoff M>=2. Its RH equivalence does not merely require bounded
values along a selected cofinal sequence. PE4 supplies the every-cutoff
bound directly. A cofinal construction could also suffice by supplying
one common bound at every earlier cutoff m<=M for arbitrarily large M,
with normalization at m; this is a prefix requirement, not a bound only
at the chosen parent M. A separate propagation theorem would be needed
for any other sampling scheme.

Neither eventual sign changes nor cofinal small returns of this particular
Abel source are established here. Existence of both signs somewhere in
each finite retained field does not assert either tail property. No
cofinal-endpoint-only RH receiver has been found in the cited Lean chain.

## Direct signed-source estimate audit

The endpoint remains the literal full sum
`S(M)=sum_(k=1..M-1) (sqrt(k+1)-sqrt(k))*psiDefect(k)`.
The producer requires `abs(S(M))<=C*M` with one C at every cutoff.
No new bound for this sum is obtained by the estimates below.

`abs_psiDefect_selberg_core` in `SelbergSymmetryCore.lean` controls the signed
combination
`psiDefect(k)*log(k)+sum_(d<=k) Lambda(d)*psiDefect(floor(k/d))`
by `384*k`. Applying absolute values before the square-root Abel sum
therefore leaves the allowance
`384*sum_(k<M) k/(sqrt(k+1)+sqrt(k))`, of order `M^(3/2)`.
This is an audit of that particular absolute-value estimate, not a lower
bound on the actual signed sum or a rejection of signed Selberg methods.
The coupled signs must supply a further saving; the displayed bound does
not supply it.

`exists_sum_normSq_moebius_window_le` in `Sieve/MoebiusMeanSquareUnconditional.lean`
is unconditional, but its input rate is only a function B tending to zero
and its output is a mean square over moving interval starts, with explicit
frequency-tail and discretization costs. No estimate for the present
weighted full source follows without bounding those costs and proving the
weight transfer. In particular, `B(N)->0` cannot be replaced by a
square-root power saving. The inspected
`eventually_dyadicMeanSquare_moebius_le_menonCentral` in `Sieve/MenonMobiusLargeValues.lean`
also retains its central-disc and complementary-frequency costs; no
application closing the Abel bound is proved here.

The exact lcm bilinear identity in `Sieve/DivisorSumBilinearSmooth.lean` retains
arithmetic cross terms. Its accompanying floor-replacement error estimate
is a sum of absolute coefficient products, which does not establish the
required signed comparison. These are still possible ingredients in a
source-specific argument, not an unconditional completion of that argument.

This audit adds no Lean theorem, assumes no numerical result, and does not
retire the route. The missing output is still the uniform complete signed
bound itself, or an actual-source inequality that proves it.

## Frozen logarithmic successor-slack test

This is a derived proof candidate for the extension step, not a new RH
conjecture. For every certified actual state P with at least three unused
primes, test

`sum_(q unused) log(q)*((B-Q_(P+q))^2-4*G_(P+q)*D_(P+q)) >= 0`.

The existing merger theorem gives `Q_(P+q)<=B` at a certified state.
Consequently each squared slack is nonnegative exactly when that successor
is certified. Positive logarithmic weights make the displayed comparison
sufficient to select a successor. Unlike a nonincreasing-energy proposal,
it keeps the original reserve; actual stalled states already exclude
requiring every step's overlap to be nonnegative. Logarithmic weights are
chosen to test whether a Selberg-weighted aggregate can prove selection.
Existence of a good successor does not predict this aggregate's sign.

Read all saved states through32 in `defect-reserve-reanalysis.json`.
Regenerate no source or path for the initial test. Retain the original
state-certification tolerance, and use `1e-12*max(1,B^2)` for the weighted
mean squared slack. Record every failure, every outgoing slack, and whether
the failed state has a certified predecessor path. Do not change the
weights or budget after observing the output. If failures occur, independently
reconstruct every failed state and every successor from the defining divisor
defect and Abel sums at 80 decimal digits. This audit is numerical guidance,
not a Lean premise or a formal counterexample.

Run on RunPod with at most eight workers, one-thread BLAS and a 60-second
foreground deadline. Download script, input hash, output and interpretation
to `2-fully-proven/computations`. A pass would justify attacking this precise
signed aggregate analytically; a failure would rule out this proposed
averaging step at the numerical-evidence level without refuting extension,
PE4 or RH. No larger screen is scheduled.

The [completed RunPod diagnostic](../2-fully-proven/computations/ccm-fu-logarithmic-successor-slack-2026-09-07/README.md)
finds 645 failures among all 6659 tested states, each reachable through
certified predecessors. Every failed field and successor was independently
reconstructed at 80 decimal digits. The first is M=17, P={5,7,11}:
prime 2 preserves the certificate while primes 3 and 13 do not. The
negative logarithmic mean therefore does not refute existence of a good
successor. It rejects this proposed averaging proof at the numerical-evidence
level; no formal counterexample or route retirement is claimed.

At this witness the oriented coordinates are a negative head h and positive
`a=A_{2}`, `b=A_{3}`, `c=A_{2,3}`, `z=A_{13}`, with `a<c<b`.
Choosing prime 2 keeps `b-c` positive; choosing prime 3 makes `a-c` negative.
For a field of this exact shape, the paper-algebra criterion for prime 2 to
contract the certificate is `a*sqrt((b-c)^2+z^2)<=b*c`. This comparison is
independent of the negative head's size. It identifies a concrete transverse
compensation to retain in a source argument, but its all-cutoff arithmetic
validity and propagation through more general retained fields remain unproved.

The [complete transverse compensation criterion](../3-formalized/ccm-fu-head-defect-compensation.md)
is now formal for the literal retained source with a nonpositive head,
nonnegative nonempty coordinates, and nonnegative transverse differences.
It retains every nonempty q-free label: with selected singleton a,
transverse residual square sum T and partner overlap C, the geometric
certificate contracts exactly when `a*sqrt(T)<=C`. The same hypotheses
preserve the sign class after the merger. Selecting such primes along a
complete order, and paying for the other necessary steps from the original
reserve, remain open; the numerical witness is not a Lean input.

The [head-supported path strategy](../5-failed/ccm-fu-head-supported-defect-path.md)
is formally refuted: at cutoff21 every list containing2,3,5 has a proper
prefix with an unprocessed oriented singleton below -1/50, independently
of any energy budget. Exact source support and analytic bounds prove the
three-prime obstruction without enumerating orders. Saved diagnostics also
find restricted path failures at ten other cutoffs through32, with all183
restricted extension failures independently reconstructed at80 digits.
Those additional numerical results are not Lean premises. Unrestricted
reserve extension remains open.

The [formal mixed transverse comparison](../3-formalized/ccm-fu-mixed-transverse-compensation.md)
retains newly created defects when leaving that class. For current head -b,
selected singleton a, transverse positive/negative square sums T,U and
overlap C, it gives `G=a^2+T+U+2C`, `D=b^2`, `G'=T`, `D'=(a+b)^2+U`.
With `v=sqrt(G)-sqrt(T)`, radius contraction is exactly
`sqrt(T)*v-C<=b*(v-a)`. A frozen transverse field can be repaired by some
finite b>=0 exactly when `U+2C>2a sqrt(T)`, or U=0 and `C>=a sqrt(T)`.
No transverse-domination hypothesis or computed source value enters this
comparison. Arithmetic payment, subsequent already-mixed states and
complete ordering remain open.

The [unconditional first-prime reserve](../3-formalized/ccm-fu-first-prime-quadratic-reserve.md)
now supplies universal c>0 and T>=1 with
`Q_empty(M)-Q_{p}(M)>=c*M^2/p` whenever p is prime and `M/p>=T`.
The proof retains the full squarefree coprime overlap, using a uniform
unsigned-channel floor and the corpus's analytic counting estimate. The
paired cofactor sum is identified with the literal retained energy. Thus
every fixed prime supplies a quadratic initial credit eventually. No bound
for its geometric defect cost or the later mixed-state costs follows yet;
the complete reserve-extension comparison above remains open.

The existing first-defect estimate does not spend this credit successfully.
For M>=p its adjacent-cutoff right side is at most `2888*M^2/p`;
together with `B<=722*M^2`, the resulting geometric cost allowance is
`2888*M^2/sqrt(p)`. The new credit lower bound is `c*M^2/p`.
These allowances therefore do not establish the required comparison. For
example, the sharper sufficient defect bound
`D_{p}<=c^2*M^2/(2888*p^2)` would make the new credit pay the cost, but that
bound has not been proved. This is a limitation of the available estimates,
not a lower bound on the actual defect or evidence against extension.

The [quadratic first-defect theorem](../3-formalized/ccm-fu-quadratic-first-defect.md)
now proves the actual defect has the same quadratic order as this budget:
for every `M>=143360000000000`,
`M^2/2048000000000 <= D_{2}(M) <= 722*M^2`.
The analytic cutoff-seven reversal persists on a relative cofactor interval,
and the squarefree counting estimate places a positive density of distinct
retained labels there. Thus the prime-two defect cannot be treated as
`o(M^2)`. The released reserve must be compared with its actual geometric
cost at the level of coefficients and signed correlations. This theorem
neither refutes the first-prime certificate nor closes that comparison.

The [signed terminal modular mean](../3-formalized/ccm-fu-terminal-modular-mean.md)
closes the coefficient uncertainty in the actual unsigned source:
`K_1(M)/sqrt(M) -> c=log(2*pi)/2-gamma-1/4`.
For every epsilon>0, one quotient threshold T gives
`|K_d(M)-c*sqrt(M)|<=epsilon*sqrt(M)` for all positive d with `M/d>=T`,
including clipped endpoints. The proof retains the complete terminal
modular sum and proves its cancellation using reciprocal Fourier phases;
the centered hyperbola coefficient is exactly `-1/24`. These are
unconditional source estimates. A reserve comparison must still control
the bounded quotient profiles and their signed interactions in changing
retained states; summing the separate uniform errors does not supply the
complete signed bound.

The direct [binary gcd compensation attempt](ccm-fu-binary-gcd-compensation.md)
also fails its frozen numerical test: 59 of all 2,550 saved packets
`G_r+G_(2r)` at odd r and cutoffs through 100 are positive. The first,
at cutoff eleven, survives independent 80-digit source reconstruction even
though the complete cross sum there is strictly negative. The omitted
compensation is exactly the released pairs at odd cofactors three and five.
Thus the full reserve must remain available across odd gcd classes; this
test supplies no new Lean premise, formal no-go, or full source bound.

The [negative-support extension candidate](ccm-fu-defect-supported-extension.md)
allows already mixed fields. At every saved cutoff through32, all3949
certified proper states with negative nonempty coordinates have a certified
or terminal exit using a prime in the union of those labels. Every saved
cutoff has a complete certified path following this rule whenever that
union is nonempty. These are finite numerical results. The separate
[analytic transport theorem](../3-formalized/ccm-fu-negative-support-transport.md)
proves that an active prime outside this union can only decrease good energy
and increase defect energy; every strict defect decrease must use the union.
Inside the union, new defects may appear elsewhere in the same merger.
Controlling their complete geometric cost under the original budget remains
the missing arithmetic step, and no complete extension theorem follows yet.

The [fixed-quotient source calculation](../5-failed/ccm-fu-universal-first-prime-certificate.md)
now refutes universal first-prime geometric certification. At M=12p, the
actual quotient-twelve profile exceeds the proved unsigned mean. For all
sufficiently large primes this gives `D_{p}>=p/2000000`, whereas
`D_{p}<=122018p`, `B-Q_{p}<=14112p` and `G_{p}>=b*p^2-136130p` for one b>0.
Consequently `Phi({p})-B` exceeds every prescribed linear multiple of p,
despite `Q_{p}<=B`. The source estimates and arbitrary-large-prime failure
are closed in Lean without numerical premises. The extension conjecture
asks for some successful successor of a certified state, so this result
does not refute it. It excludes certifying every initial prime by the
geometric radius; a complete proof must preserve that selection distinction.

The [exact-overlap recovery](../3-formalized/ccm-fu-exact-overlap-recovery.md)
shows why that distinction matters: throughout this same12p family, all
available second primes meet the actual diagonal once p is large. The source
proof controls every original four-cofactor block using a global3/5 unsigned
ceiling and the exact parent mean. Thus the geometric certificate rejects
some states that already bound every immediate successor. An exact-overlap
induction can use a larger class, but its complete signed comparison and
closure under repeated mergers have not been proved.

The [exact successor-energy extension candidate](ccm-fu-exact-successor-extension.md)
uses that larger class directly: current energy and every immediate
successor energy must meet the original diagonal. Every initial state has
this property. All8176 eligible proper saved states through32 have a
successor with the same property, including826 states rejected by the
geometric certificate; every saved cutoff has a complete path. This bounded
RunPod reanalysis regenerates no channels and is numerical evidence only.
The missing estimate retains all four-coordinate mixed terms
`C_pq=sum_R(a_R*d_R+b_R*c_R)`: one p must satisfy
`Delta_p+Delta_q+2*C_pq<=B-Q_P` for every other q. At two remaining primes,
this still includes the unproved complete-source endpoint. No new Lean
premise, all-cutoff closure, or RH proof is supplied by the finite passes.
