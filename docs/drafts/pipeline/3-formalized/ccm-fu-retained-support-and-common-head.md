# CCM-FU: exact retained support, aperture costs and one common source head

- **Type:** [BRIDGE], source support and exact arithmetic structure.
- **Parent:** [retained support and witness costs](../1-in-progress/ccm-fu-retained-support-cost.md).
- **Input:** [actual arbitrary-field batches](ccm-fu-arbitrary-retained-prime-batches.md).
- **Scope:** Exact finite source statements. Exhaustive compatible coverage, uniform energy costs, SD1 and RH remain open.

## Exact support in every actual state

Let U(M) be the primes strictly below M, P the processed set, and
`F(M,P,R)` the literal retained fibre labelled by R. Every contributing
source index d has `R subset primeFactors(d)`, hence `product(R)` divides d.
The original source indices are positive and strictly below M. Therefore

`M <= product(R)  =>  F(M,P,R)=0`.

This holds for every processed state P. The intersection profile V_S(M,R)
has the same threshold: its only extra terminal index d=M has zero channel.

Define the possible active labels by

`A(M,P) = {R subset U(M) minus P : product(R)<M}`.

Every fibre outside A(M,P) is zero. Consequently the complete actual energy,
without an error term, is

`E(M,P) = sum_(R in A(M,P)) F(M,P,R)^2`.

All labels consist of primes, and distinct labels have distinct squarefree
products. Their products lie in the positive interval `[1,M-1]`, so
`card(A(M,P)) <= M-1`, including M=0 and M=1. This bounds possible source
coordinates, not the magnitude of their coefficients. Cancellation can
still make a structurally permitted coordinate zero.

## Necessary full-field witness cost

For a fixed finite retained prime set S, a coordinate delta functional
reads V_S(M,R) exactly. Any finite cutoff family K that strictly detects
every nonzero real direction must therefore contain a cutoff beyond
`product(R)` for each R contained in S. In particular,

`product(S) < max(K)`.

These are necessary costs of complete ambient-direction detection.
They do not apply automatically to a strategy exploiting only the actual
correlated states and their possible active coordinates.

## Exact masked homothety

Write C_d(M) for the literal Möbius dilation channel and define the complete
coprime head

`G_s(N) = sum_(1<=d<=N, gcd(s,d)=1) C_d(N)`.

For any positive integer r, let `N=floor(M/r)` and let w be the exact
square-root clipping coefficient `divisorPrimeClipWeight(M,r)`. General
signed homothety gives

`C_(r*d)(M) = sqrt(r)*mu(r)`
` * [if gcd(r,d)=1 then (1-w)C_d(N)+w C_d(N+1) else 0]`.

If r and d share a prime, their product is not squarefree and its Möbius
coefficient vanishes. Thus the mask is exact and no source support is
silently dropped. The newly added terminal channel at N+1 is zero.

For the full retained label S, put `s=product(S)`. Its source is precisely
the sum of C_d(M) over multiples of s. Reindexing these multiples and keeping
the shared-prime mask gives

`V_S(M,S) = sqrt(s)*mu(s)`
` * [(1-w_s)G_s(floor(M/s))+w_s G_s(floor(M/s)+1)]`.

## Initial sign chamber and parent aperture

Suppose every integer `1<d<q` shares a factor with s. For `s<=M<=s*q`,
all nontrivial coprime cofactors are excluded; at the upper endpoint the
cofactor q contributes only a zero terminal channel. Hence

`V_S(M,S)=C_s(M)` throughout that interval.

Below s the coordinate is already zero. Since every unsigned dilation
channel is nonnegative, throughout `M<=s*q` one has

`mu(s)*V_S(M,S) >= 0`.

The integer mu(s) is nonzero because S consists of distinct primes. Applying
complete directional detection to the delta functional with coefficient
`-mu(s)` forces a witness cutoff strictly greater than s*q.

A sufficient arithmetic gap condition is that S contains every prime below
q: every `1<d<q` has a prime divisor below q, and that divisor divides s.
In particular q=2 gives a universal initial chamber; for a retained prime
prefix, q may be its first omitted prime.

If every witness k is copied at one parent M by an actual prime p_k with
`floor(M/p_k)=k`, then `2k<=p_k*k<=M`. Thus under the prime-prefix gap
condition the parent must satisfy

`2*s*q < M`.

This is an aperture lower bound for that full-direction witness mechanism.
It is not an energy lower bound, and does not retire general adaptive orders.

## All coordinates come from the same coprime head

The positive structural identity applies to every R contained in S. Put
`r=product(R)` and `s=product(S)`, keeping the distinction between these
two products. With `N=floor(M/r)` and `w_r=divisorPrimeClipWeight(M,r)`,

`V_S(M,R) = sqrt(r)*mu(r)`
` * [(1-w_r)G_s(N)+w_r G_s(N+1)]`.

The head is coprime to the product of the **full** field S, even for a proper
subset R. To prove this, first restrict source indices to multiples r*d.
When r and d are coprime, the retained-label condition is equivalent to
`gcd(s,d)=1`. When they are not coprime, the original channel is zero and
the full-field coprime mask is also false. This proves the complete identity
through both cases, including every clipped endpoint.

If P has processed all active primes outside S and is disjoint from S,
and S consists of active parent primes, the exact actual-state identification
and `mu(r)^2=1` give

`E(M,P) = sum_(R subset S) r`
` * [(1-w_r)G_s(floor(M/r))+w_r G_s(floor(M/r)+1)]^2`.

The full energy is therefore a positive product-weighted sum of differently
scaled samples of one actual coprime head. The active-support theorem can
remove only the terms whose coordinates are proved zero. This identity
retains the correlations lost by treating all coordinates as independent
arbitrary values.

## Remaining source-production target

For the absolute energy identity, S is the entire unprocessed active parent
prime field: every active prime outside S must already be in P. The smaller
retained steering field in the batch theorem need not equal this field. For
that smaller field, the complete energy-change identity applies; it cannot
replace the entire parent energy by its restricted squared norm.

The common head depends on S. Processing another prime changes both the
coprime head and the remaining coordinate scales. The formulas prove no
uniform estimate on those changes or on the complete weighted sum.

The next source-level target is joint control of that arithmetic change and
its values across product scales within a compatible exhaustive order.
The existing full-field batches remain available, with their field-dependent
preparation bound `722*2^|core|*M^2`. A growing core cannot be assumed harmless:
the previously proved middle-singleton obstruction remains in force.

Aperture costs alone do not imply energy growth. Exact support restriction
alone does not produce a bounded-energy schedule. The primary RH objective
and its uniform cofinal gate are unchanged.

## Lean modules and validation

Namespace `RHTower`:

- `RetainedPrimeSupportThreshold`: product vanishing, exact active-label
  energy, cardinality bound, and full-field witness threshold.
- `RetainedPrimeTopHomothety`: masked clipping, full-label coprime head,
  exact initial sign chamber, witness-gap and parent-aperture bounds.
- `RetainedPrimeCoordinateHomothety`: every coordinate from one common
  coprime head, and the complete product-scale energy identity.

Scratch and exact-file Lean checks passed for all three modules. The single
new-declaration axiom audit covered all 21 public declarations and found only
`propext`, `Classical.choice`, and `Quot.sound`. All three modules are wired
into `RHTower`; no umbrella or full build was run. Repository lint currently
reports four unrelated, unwired modules: `ProductAFEContour`,
`ProductAFEDirect`, `ProductAFEIntegrand`, and `RectangleThreePoleResidue`.
No numerical experiment is required: all support and sign-chamber statements
follow from the literal source algebra and established channel positivity.
