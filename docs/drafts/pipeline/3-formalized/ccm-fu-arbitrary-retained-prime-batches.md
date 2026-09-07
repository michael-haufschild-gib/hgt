# CCM-FU: actual bounded batches for every finite retained field

- **Type:** [BRIDGE], exact source transport and finite scheduling.
- **Parent:** [finite source control and cofinal coverage](../1-in-progress/ccm-fu-finite-source-cone-exhaustion.md).
- **Input:** [finite clipping-stable directional control](ccm-fu-finite-retained-directional-control.md).
- **Scope:** Every fixed finite retained prime field; the core and budget may depend on that field. Complete compatible cofinal coverage and RH remain open.

## Exact source transport

Let S be a finite set of primes, U(M) the active primes strictly below M,
and C_d(M) the literal Möbius dilation channel. The actual state after
processing P has fibre

`F(M,P,R) = sum_(1<=d<=M, primeFactors(d) minus P = R) C_d(M)`.

The complete retained profile is

`V_S(M,R) = sum_(1<=d<=M, primeFactors(d) intersect S = R) C_d(M)`.

If `U(M) minus S` is contained in P and P is disjoint from S, then
`F(M,P,R)=V_S(M,R)` for every R contained in S. Every fibre outside S
vanishes under the complementary-core condition, without needing the
disjointness condition for that vanishing statement. At the terminal index
d=M the channel is zero, so the strict active-prime cutoff loses no term.
Nonsquarefree source channels also vanish exactly.

Write `w=divisorPrimeClipWeight(M,p)` and `k=floor(M/p)`. The existing
all-cutoff homothety identifies each unprocessed prime packet with
`-sqrt(p)*((1-w)F(k,P,R)+w F(k+1,P,R))`. If P covers the complementary
active primes at k+1 and is disjoint from S, both child fields are the
corresponding complete V_S profiles. Provided S consists of active parent
primes and p is outside S and P, the complete energy change is exactly

`E(M,P union {p}) - E(M,P)`
` = -2 sqrt(p) * sum_(R subset S) F(M,P,R)`
`                  * ((1-w)V_S(k,R)+w V_S(k+1,R))`.

This is the full energy difference. The removed prime-packet squares cancel
algebraically; no unestimated outside-coordinate energy is discarded.
The receiving vector uses all `2^|S|` retained coordinates. Its norm in the
margin theorem is the supremum norm.

## Source-defined actual descent

Finite source control supplies a nonempty finite family K, positive c and
`0<delta<=1` such that every parent vector z is detected by one independently
clipped witness with pairing at least `c*norm(z)`. Every witness may be
chosen at k>=2: the integer source is zero at zero and one. Set clips at
those trivial cutoffs to zero, apply the original margin to a nonzero
vector, and then remove the trivial cutoffs. The zero vector is handled by
nonemptiness of the retained family.

If each k in K has an available unprocessed prime p_k with parent quotient
k and clipping at most delta, one of those actual primes satisfies

`E(M,P union {p_k}) - E(M,P) <= -2 sqrt(p_k)*c*norm(z)`.

Thus its energy is nonincreasing, and decreases strictly whenever z is
nonzero. For pools W_k, each of cardinality at least n, any selected set of
fewer than n primes leaves an unused member in every pool. Selecting one
such member per pool and applying the source margin produces a safe next
step. Induction constructs n distinct actual primes with every prefix at
most the prepared energy. All selected primes avoid S, so the complementary
child-field identification persists throughout this induction.

## Unconditional common-parent window supply

Choose a core cutoff B exceeding every k in K and every prime in S, and
let `P=U(B) minus S`. Set `A=product_(k in K) k`. Choose an integer b>=B
large enough that `b*delta >= 2B(B+1)`. At parent `M=A(b+1)N`, use the
actual prime windows

`W_k(N) = {p prime : b(A/k)N < p <= (b+1)(A/k)N}`.

Since k divides A, every such prime has exactly `floor(M/p)=k`.
All these primes exceed b and hence avoid the core and S. The analytic
square-root estimate

`b*divisorPrimeClipWeight(M,p) <= 2k(k+1) <= 2B(B+1)`

puts every window inside the common clipping tolerance. One proof uses
`1 <= 2(k+1)(sqrt(k+1)-sqrt(k))`, the exact clipping-step identity, and
the two window endpoints. No numerical root or source evaluation is used.

The corpus's unconditional fixed prime-window supply theorem makes each
W_k(N) eventually have at least n members. K is finite, so one sufficiently
large N works simultaneously for all witnesses and any prescribed lower
bound on M. The pool-order theorem therefore constructs actual batches of
arbitrary finite length at cofinal parent cutoffs for every fixed S.

## Complete finite preparation budget

The existing one-prime doubling bound and arithmetic diagonal estimate give,
for every subset D of the fixed core P,

`E(M,D) <= 722 * 2^|P| * M^2`.

This covers every possible core-preparation prefix. Each constructed batch
prefix has energy at most E(M,P), so the same quadratic bound controls
preparation followed by the batch. The constant is explicit and independent
of batch length and parent cutoff for this fixed retained field.

## Exact remaining obligation

The theorem leaves S unprocessed, and does not consume all other active
parent primes. Arbitrarily long batches at arbitrarily late cutoffs do not
supply one compatible exhaustive order. The witness family, core P,
clipping tolerance, common multiple and window sizes depend on S; there is
no bound keeping `2^|P|` or the required resources uniform as the retained
field changes. The growing-middle singleton obstruction still prevents
assuming that a cofinally growing complementary core can be prepared first
under a fixed quadratic ceiling.

The remaining producer must coordinate field changes, actual nonisolated
prime processing, and all intermediate energy costs. PE4/PE4G/PE4C, SD1
and RH are not conclusions of this bridge.

## Lean modules and validation

Namespace `RHTower`:

- `RetainedPrimeStateTransport`: exact coordinate identification, outside
  vanishing, clipped source pairing, and complete prime energy identity.
- `RetainedPrimeDescentOrders`: nontrivial finite witnesses, quantified
  prime descent, capacity-controlled distinct pool orders, and full finite
  core-preparation bound.
- `RetainedPrimeWindowSupply`: general analytic clipping bound, literal
  witness windows, quotient identification and unconditional growing supply.
- `RetainedPrimeBoundedBatches`: unconditional assembly for every finite
  retained prime field and every batch-length/cutoff demand.

All four modules passed scratch and exact-file `lake env lean` checks. Only
the four needed oleans were emitted, and all four imports are wired into
RHTower without an umbrella or dependency build. The 17 new public
declarations were axiom-audited once: only `propext`, `Classical.choice` and
`Quot.sound` occur. Global formal lint passed with existing large-file
warnings. New-source whitespace and certificate links passed. No numerical
experiment, computed proof premise, full build or umbrella build was used.

Formal research indexes were refreshed once. All owned scratch files and logs
were removed; no owned Lean/lake processes remain.
