# Actual Möbius–divisor source diagonal dominance

- **Stage:** 1-in-progress
- **Type:** [BRIDGE] candidate; unproved
- **Target:** an independent arithmetic inequality strong enough for RH.

## Frozen statement

Let `D(q)=log(q!)-sum_(n<=q)tau(n)+2 gamma q`, and

`K_d(M)=sum_(k=d)^(M-1) (sqrt(k+1)-sqrt(k)) D(floor(k/d))`.

**SD1:** for every integer M>=1,

`(sum_(d<=M) mu(d)K_d(M))^2 <= sum_(d<=M) mu(d)^2 K_d(M)^2`.

This is a source-specific proposal, not a statement about arbitrary square-root-bounded D.
Earlier finite controls provide motivation: the literal complete source had much smaller mean
square than its independently signed channels. Those observations do not imply SD1 pointwise.
The statement is classified as a bridge because the desired cancellation estimate determines it.
No novelty or proof claim is made.

## Why this strength would suffice

The unconditional signed hyperbola estimate gives

`C_d(M)^2 <= 361 M sqrt(floor((M-1)/d))`,
`Q(M)=sum_(d<=M) C_d(M)^2 <= 722 M^2`,

where `C_d=mu(d)K_d`. Exact periodic cancellation is taken inside each time channel;
complete quotient blocks and the clipped final block are all retained.
`RHTower.sum_mobiusDivisorDilationChannel_sq_le_quadratic` in
`MobiusDivisorAbelQuadraticDiagonal` certifies the second inequality. The complete
[paper proof and Lean audit](../3-formalized/ccm-fu-signed-divisor-hyperbola-cancellation.md)
record the signed hyperbola argument.

Thus SD1 would directly imply `|S(M)/M|<=sqrt(722)` for M>=1. The existing
`riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded` receiver then applies; no
subpower-loss continuation is needed. The remaining arithmetic content is SD1 itself.
The quadratic diagonal bound does not establish it.

## Attacks

1. Exhaustive finite counterexample search, initially M<=2^21, using exact piecewise-quadratic
   channel structure. Numerical results guide research only.
2. Expand the off-diagonal and retain gcd, quotient, squarefree and coprimality labels. The
   corpus identity `mu(br)mu(ar)=mu(ab)mu(r)^2` identifies orientation but does not sum it.
3. Test proposed source-shape proofs on nearby kernels before applying them to this D.
   A general-kernel failure does not refute SD1 for the literal divisor source.

The negative two-prime renewal determinant is not a proof of SD1: that determinant is evaluated
after complete renewal collapses to `exp(-ax)`, while SD1 concerns the unresolved inverse source.

## Verification protocol

See the frozen [experiment protocol](../2-fully-proven/computations/mobius-divisor-diagonal-dominance-2026-09-06/PROTOCOL.md).
No finite pass will be called an all-scale proof, and the factor one will not be adjusted after
a counterexample. The elementary diagonal bound alone is not recorded as new RH progress.

## Current evidence and formal boundary

SD1 survives exhaustive floating-point testing at all integers through 2,097,152. M=2 is exact
equality; the largest other ratio is 0.77306365027833565955 at M=17, independently checked at
60 and 100 digits. These checks do not prove SD1. Full data and audits are in the
[computation report](../2-fully-proven/computations/mobius-divisor-diagonal-dominance-2026-09-06/REPORT.md).

**SD2, independent stronger [BRIDGE], numerically rejected:** the margin
`E(M)=sum_d mu(d)^2 K_d(M)^2-S(M)^2` is nondecreasing for all M>=1. The first decrease is
M=4 to 5, about -0.01312330656601420691. There are 21,863 recorded decreases; the largest
absolute one occurs at M=1,851,018. Rejecting this monotone producer does not reject SD1 or
this RH branch. No damped monotonicity statement replaces the frozen claim.

The positive residue is an exact evolution retaining the signed mixed term. With
`C_d=mu(d)K_d`, `v_d=mu(d)D(floor(M/d))`, and `w=sqrt(M+1)-sqrt(M)`, Lean proves

`C_d(M+1)=C_d(M)+w v_d`,
`Q(M+1)-Q(M)=2w sum_d C_d(M)v_d+w^2 sum_d v_d^2`,

where Q is the complete arithmetic diagonal and the new terminal channel is zero.
[MobiusDivisorAbelDiagonalBound.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorAbelDiagonalBound.lean)
proves the exact successor laws and a harmonic envelope. The sharper
`Q(M)<=722M^2` is closed in `MobiusDivisorAbelQuadraticDiagonal.lean`, using signed
hyperbola summation. No experimental result is used in either proof.
The numerical SD2 counterexample itself is not a Lean certificate. The signed total
off-diagonal upper bound remains open; the diagonal needs no subpower-loss continuation.


**Other proposed producers:** arbitrary nonnegative decreasing time weights fail in Lean,
including some positive strictly decreasing geometric weights. Mixed positivity against every
flat prefix fails numerically at M=17,t=6; mixed positivity against every geometric kernel
fails numerically at M=1802,q=1/1000000, despite passing the initial grid through512. The
[obstruction card](../5-failed/mobius-divisor-decreasing-weight-producer.md) retains the exact
all-scale Abel prefix representation and states the separate proof statuses. These failures
do not refute SD1. A source proof must still control the total signed half-order pairing.


**Separate gcd-component sign (SG1) is refuted in Lean.** For the literal half-order
source, `G_1(11)>1/100` while `sum_r G_r(11)<-1/100`. Exact prime homothety
`G_p(pM)=p G_1(M)` for prime p>M makes positive individual components unbounded
at unbounded cutoffs. Thus neither separate nonpositivity nor a uniform individual
upper ceiling can supply SD1. Complete gcd reconstruction and the exact masked
integer homothety survive in Lean. The [closed obstruction and positive-survivor
proof](../5-failed/ccm-fu-gcd-cross-sign.md) records both. The remaining source
problem is compensation in the complete signed sum; SD1 itself is unchanged.


**Actual unsigned orientation is formal at every cutoff.** Lean proves
`A(N)>=0` for every natural N and `K_d(M)>=0` for every natural M,d, including
births and terminal partial blocks. [The analytic orientation proof](../3-formalized/ccm-fu-unsigned-channel-orientation.md)
uses geometric harmonic centering, sharp paired square-block mass, an analytic
initial interval through 24, and floor-prefix Abel transfer. The earlier
`K_1(M)>=sqrt(M)/48-3501` floor and divergence remain valid. Thus U1/U2 are closed;
unsigned signs are proved source data for the remaining complete Möbius-signed
pairing. They do not establish SD1.

**First-prime contraction is formal; uniformly budgeted increasing-prime elimination is terminal.**
Pairing d and pd on p-free cofactors preserves S and releases exactly
`2 sum_(p-free d)mu(d)^2 K_d K_pd>=0`. This is genuine source cancellation.
However the smooth-prime head H after all primes through M/2 satisfies
`H-S=T`, with late-prime positive mass `T(4N)/(4N)->+infinity`.
Lean excludes every fixed original-diagonal budget for `H²+S²`.
Consequently neither successive energy decrease nor a fixed stage/original-energy
ceiling can supply SD1 through this increasing-prime order. The [closed obstruction
and positive survivor](../5-failed/ccm-fu-prime-pair-energy.md) retain both the first
contraction and the exact compensation law. The [actual head asymptotic](../3-formalized/ccm-fu-late-prime-head-asymptotic.md)
is also formal: quantitative PNT and the exact source sum give
`S(M)log(M)/(M sqrt(M))->0`, hence `S(4N)/T(4N)->0`, `H(4N)/T(4N)->1`,
and `H(4N)/(4N)->+infinity`. The intermediate head itself carries the large mass,
without assuming a bound on S. Leading cancellation is established; the critical
final residual `S(M)=O(M)` and complete signed order remain open.


**Adaptive stepwise contraction is also refuted, with its own order-independent proof.**
At cutoff seven, the literal three-prime merger increases energy in its final step
for all six orders of 2,3,5. Both terminal signed groups are negative whichever
prime remains last. Nevertheless `Q(7)-S(7)^2>1/125` is proved analytically in Lean.
The [closed PE3 obstruction and positive survivor](../5-failed/ccm-fu-adaptive-prime-energy.md)
show that even an adaptive proof must permit local energy increases. They do not
exclude an adaptive order whose fluctuating intermediate energies stay below the
original diagonal. The separate [PE4 and greedy PE4G candidates](ccm-fu-adaptive-prime-ceiling.md)
remain open; stored subset data through32 and greedy stages through1024 show no
finite failure of that ceiling. A generic positivity/endpoint mechanism is nevertheless
refuted in Lean: one strictly positive four-coordinate cube has energy sequence
`337/16,20,22,18,0` in every order. Its [sharp background-parameter classification](../5-failed/ccm-fu-positive-prime-cube-ceiling.md)
is formal as well. That cube is not the actual divisor source; it requires any PE4
proof to use additional arithmetic structure and does not refute SD1.
The [actual late-prime block law](../3-formalized/ccm-fu-late-prime-block-endpoints.md) supplies one such structural control: primes at least half the cutoff occur only as isolated singleton fibres, and every intermediate subset of an unprocessed block has energy at most its larger endpoint energy. The exact source law reduces a whole-block ceiling to its two endpoints. It leaves smaller-prime interleaving and the final complete signed bound open. The [exact retained-source recursion](../3-formalized/ccm-fu-prime-fibre-recursion.md) identifies the new-prime update at cutoff pN, p>N, as subtraction of the reflected smaller-cutoff field. Its complete energy change retains the mixed inner product between both actual fields. Smaller-prime processing can reverse singleton orientation: after primes2,3,5 are processed, the p singleton at cutoff7p is `-sqrt(p)*S(7)>0`, cofinally unbounded. The remaining comparison must retain these inherited signs. The stronger [all-cutoff interpolation law](../3-formalized/ccm-fu-prime-fibre-interpolation.md) is formal for every prime, with no p>N restriction: the reflected smaller field is the convex square-root-clock interpolation of cutoffs floor(M/p) and floor(M/p)+1. It includes the clipped block and gives an unconditional copied-packet energy bound in the two smaller retained energies. Their common processed set and the complete signed mixed inner product must still be controlled.
The [square-root terminal ordering theorem](../3-formalized/ccm-fu-square-root-terminal-order.md) handles arbitrary retained singleton signs: after all primes with `p^2<M` are processed, remaining labels have cardinality at most one, and some complete remaining-prime order has every prefix below `max(Q_P(M),S(M)^2)`. This is an exact optimal terminal ceiling, proved at every cutoff. It leaves earlier overlapping-label control and both original-diagonal endpoint bounds open; the final endpoint bound remains SD1 itself.

**Every fixed number of late-prime phases is also excluded in Lean.** The
[exact partition capacity](../5-failed/ccm-fu-fixed-block-prime-schedules.md) bounds
the positive mass of one unprocessed late-prime block by the sum of its actual
endpoint energy square roots. K blocks under ceiling B therefore have capacity
`2K sqrt(B)`. Since the complete late mass divided by cutoff tends to infinity
along 4N while the original diagonal is quadratic, any fixed K and diagonal
multiplier are eventually exceeded at a block endpoint. A successful adaptive
energy proof needs increasingly many late/earlier-prime interleavings. The theorem
retains all source mass and does not assume SD1. A common order meeting all smaller
cutoff ceilings passes the saved range through32 as the separate PE4C numerical
diagnostic; PE4C and all-cutoff SD1 remain open.

**Removing the head does not produce universal dissipation.** The
[nonempty-energy obstruction](../5-failed/ccm-fu-nonempty-energy-contraction.md)
proves that at cutoff21, after prime two, prime five increases the remaining
fibre energy by more than 1/1000. Its positive survivor is the exact all-cutoff
late-block law: nonempty energy loses only the removed singleton squares, while
another prime's full-energy gain changes by `-2 t_L F_P({q})`. The actual retained
singleton sign determines whether late consumption helps. A growing adaptive
proof must control the remaining nonempty signed products as well as its head;
finite nonempty-path success through32 does not establish the full ceiling.

**Initial head balancing is unconditional in Lean.** At every sufficiently large
cutoff M=4N, a [selected active late-prime block](../3-formalized/ccm-fu-late-prime-head-neutralization.md)
leaves the head in `[-sqrt(M),0]`, bounds its square by M, and reduces complete
energy below the original nonempty energy. Every intermediate subset stays below
the original diagonal. The finite selector pays its discrete overshoot from the
removed singleton squares; actual late mass eventually covers the original
nonnegative head. This releases the entire original head square without a final
signed-energy hypothesis. Continued availability and the signed budget across
later smaller-prime mergers remain open, so this initial operation does not
supply SD1.
The [oriented variant](../3-formalized/ccm-fu-oriented-initial-prime-extension.md)
leaves the head in `[0,sqrt(M)]` with `Q_L<=V_empty+M` and preserves the
alternating retained signs. Every available prime then contracts energy after
every intermediate subset R of L: `Q_(R union {q})<=Q_R<=Q_empty`. This controls
every interleaving of the block with any one additional prime. Repeated smaller
mergers can destroy the sign condition, as the actual positive three-singleton
after prime two at cutoff21 already proves. Their joint budget remains open.

**Changed signs have a quantitative source budget.** The
[parity-defect transport](../3-formalized/ccm-fu-parity-defect-transport.md)
splits every retained energy into aligned G and reversed-sign D, and bounds
every prime-merger gain by `2 sqrt(G) sqrt(D)`. A first merger creates at most
its actual copied-packet energy in D, with an unconditional quadratic budget
at the two adjacent quotient cutoffs. The second-prime bound
`Q_{p,q}<=Q_p+2 sqrt(Q_empty) sqrt(D_p)` is formal without a parity-preservation
premise. Paying accumulated possible gains from released energy remains open.
All stored two-prime states through32 pass the original ceiling numerically;
that finite result is not an all-cutoff theorem or a Lean premise.

**Every unsigned channel has a uniform square-root ceiling.** The
[closed source bound](../3-formalized/ccm-fu-uniform-channel-square-root-bound.md)
proves `K_d(M)<=7 sqrt(M)` for every M,d by retaining the half-logarithmic
Stirling endpoint and the exact clipped clock. The initial head square is
at most `49M`. Any initial late block leaving its head above `-sqrt(M)`
releases at most `57M` total energy, including its removed singleton squares.
This reserve is uniformly subquadratic; larger subsequent reserves must come
from paired source contractions if they are needed. The complete signed
comparison remains open. The separate [geometric reserve diagnostic](ccm-fu-geometric-defect-reserve.md)
admits a complete certified path at every saved cutoff through32 and certifies
every saved first-prime state's second-step cost, numerically only.

**The two-prime question has a bounded unit-channel obstruction.** The
[sharp local criterion](../3-formalized/ccm-fu-two-prime-local-criterion.md)
proves that any original two-prime ceiling failure at M forces
`2K_1(N)<K_r(N)` for one of those primes at `r<N<=M`. Exact cofactor
decomposition and clipped interpolation retain the original source. The
factor two is sharp for the nonnegative local comparison class. The actual
[unit-channel bound](ccm-fu-two-prime-local-blocks.md) remains open; all
first-prime geometric reserve tests through1024 pass numerically only.

**Second centering retains a quantitative arithmetic contribution.** The
[closed modular mean and cubic-primitive bounds](../3-formalized/ccm-fu-second-centered-hyperbola.md)
put the actual centered Abel term between square-root coefficients `-5/96`
and `-1/48`, up to logarithmic error. Its complete contribution tends to
negative infinity. Keeping the smooth-prefix square-root error gives the
actual unit floor `K_1(M)>=sqrt(M)/16-5log(M+1)-14`. This is unsigned source
control. The [exact smooth mean and bounded-quotient theorem](../3-formalized/ccm-fu-smooth-square-block-mean.md)
proves the exact smooth coefficient `a=log(2*pi)/2-gamma-1/6>1/6`, with
logarithmic Abel error. The complete unit band from `a-5/48` to `a-1/24`
has a strict factor-two margin. One universal T therefore proves
`M/p>=T -> K_p(M)<=2K_1(M)` for every positive dilation. Every original
two-prime ceiling failure has a unit witness `r<N<=M` with `N/r<T`.
The [large first-prime orientation theorem](../3-formalized/ccm-fu-large-prime-orientation.md)
closes `M<=5p` at every sufficiently large parent cutoff. Every child
cofactor is dominated by its parent, all retained signs survive, and every
second prime contracts complete energy. Any two-prime ceiling failure in
that parent tail requires both primes below M/5. Large-parent unit failures
lie in `5<=M/p<T`; the finite parent regime, remaining middle profiles and
aggregate signed SD1 remain open.

The [source-supplied two-channel blocks](../3-formalized/ccm-fu-two-channel-prime-blocks.md)
control a further initial sector. For large M and primes `2M<=5p`, the exact
head budget `sum K_p<=K_1` controls every retained sign and both complete and
nonempty energies at every subset. Actual primes in `(8N,9N]` supply a nonempty
block at cutoff20N, with head at most `sqrt(M)/15`, strict expenditure of the
cofactor-two reserve, and energy at most `V_empty+M/225`. Every available next
prime contracts from every intermediate subset. No complete growing schedule
or repeated sign preservation after an arbitrary small prime is established.

The [complete quotient-subpool ordering theorem](../3-formalized/ccm-fu-quotient-window-orders.md)
controls sequences after arbitrary processed states. Fixed adjacent-cutoff
packet fields give an exact signed Gram kernel; the source's transverse sign
fixes two classes with nonnegative internal overlaps. A complete order of any
selected same-quotient subpool has every prefix below the maximum of its
initial, source-fixed separating, and final energies. This requires no retained
parity premise, but supplies no original-diagonal bound for those three values.
Global endpoint estimates and growing interleaving choices remain the source
obligation for SD1.

**Independent half-probability averaging is refuted for the actual source.** The
[PE5 obstruction](../5-failed/ccm-fu-bernoulli-prime-energy.md) proves in Lean that
for every real C and every cutoff M₀, some M>=M₀ satisfies
`C*M<|H(M)|`, where `H(M)=sum_d mu(d)K_d(M)/2^omega(d)` is the literal mean.
The exact variance bound `H(M)^2<=E_(1/2)(M)` and `Q(M)<=722M^2` imply that every
fixed averaged-energy budget fails arbitrarily far out. The [closed discrete transfer](../3-formalized/ccm-fu-half-selection-growth-obstruction.md)
uses two exact Abel summations, locally uniform kernel bounds and the literal
L-series landing. A linear mean bound would contradict the [formal Euler/pole obstruction](../3-formalized/ccm-fu-half-selection-euler-pole-obstruction.md).
The survivor is unbounded magnitude on every tail, without a sign or precise
asymptotic assertion. Adaptive PE4, final SD1 and RH remain open.


## Actual growing signed batches under a uniform quadratic ceiling

The [growing signed-batch certificate](../3-formalized/ccm-fu-growing-signed-prime-batches.md)
proves positive macroscopic source supply after the fixed prime core below eight.
Clipped reflection of the negative complete source at seven gives a uniform
positive singleton floor on one fixed quotient-seven window. The corpus prime
count theorem makes its total positive mass superlinear; the actual negative
late-prime supply is superlinear along the same cutoffs.

All primes in both pools are isolated after that fixed core. Exact scalar
transport retains the removed singleton-square reserve. Matching opposite
subpools makes this reserve pay the final head square, and a complete distinct
order stays below the starting core energy. For every real T and all sufficiently
large cutoffs `M=7(b+1)(4N)` for one fixed b, the selected batch consumes at least
TM of each sign while every prefix has energy at most `184832M²`. Every partial
preparation of the fixed core has that same bound.

This is an unconditional source-produced growing partial schedule. It does not
claim the original diagonal ceiling, complete prime coverage, or control of
later middle-prime steps and their changed retained fields. Those remaining
interactions, the full growing schedule, PE4, PE4G, SD1, and RH stay open.
