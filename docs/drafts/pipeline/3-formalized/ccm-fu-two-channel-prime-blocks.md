# CCM-FU: source-supplied initial blocks with two active channels

- **ID:** CCM-FU-TWO-CHANNEL-BLOCKS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Result:** At every sufficiently large cutoff, any head-budgeted block of primes `2M<=5p` preserves all retained signs and both complete and nonempty energy ceilings at every subset. The actual source supplies a nonempty such block along every sufficiently large cutoff `20N`, strictly changing the cofactor-two fibre and leaving head at most `sqrt(20N)/15`.

## Actual source and common parent comparison

Write `D(n)` for the literal prime-free divisor defect, `K_d(M)` for its unsigned
half-order channel, `F_P(R)` for the retained signed fibre after processing P,
and `O_P(R)=(-1)^card(R) F_P(R)` for its oriented version. Let E denote complete
retained energy and V energy outside the empty head.

The existing exact smooth mean is `a=log(2*pi)/2-gamma-1/6>1/6`. Set
`epsilon=(a-1/6)/4`, `L=a-5/48-epsilon`, and `U=a-1/24+epsilon`.
On one common unit tail, `L sqrt(n)<=K_1(n)<=U sqrt(n)`, with `U<2L`.
The two adjacent endpoint values and their square-root clock mass have exactly
the same nonnegative interpolation weights. Hence, whenever `M/d>=T`, the
entire clipped channel satisfies `L sqrt(M)<=K_d(M)<=U sqrt(M)`.
Consequently one T gives the mutual comparison

`M/d>=T and M/e>=T -> K_d(M)<=2K_e(M)`

for every positive d,e. In particular `K_1(M)<=2K_2(M)` on one parent tail.
No convergence of a single normalized unit coefficient is asserted.

## Exact expenditure ratio

The harmonic correction at sixteen and analytic logarithm bounds give
`D(1)>=1/10` and `D(2)>=0`. For `2p<=M<=3p`, exact clipped homothety gives

`K_p(M)=sqrt(p)(sqrt(2)-1)D(1)+(sqrt(M)-sqrt(2p))D(2)`.

The first-block identity gives
`K_(2p)(M)=(sqrt(M)-sqrt(2p))D(1)` when `2p<M<=4p`.
If `2M<=5p`, the rational square comparisons
`sqrt(M)<=8sqrt(p)/5` and `sqrt(2)>=7/5` show

`2(sqrt(M)-sqrt(2p))<=sqrt(p)(sqrt(2)-1)`.

Multiplying by `D(1)>=0` and retaining the nonnegative D(2) term proves
`2K_(2p)(M)<=K_p(M)`. If `M<=2p`, the child is zero and the same conclusion
follows from actual channel positivity. This covers every positive p and cutoff.
The same exact second block, with `sqrt(2)>=5/4`, gives
`K_p(M)>=sqrt(p)/40` throughout `2p<=M<=3p`.

## Exact block identity and all retained labels

Suppose P consists of primes and every distinct pair has product at least M.
For any prime label R disjoint from P, exact prime insertion gives

`O_P(R)=K_(product R)(M)-sum_{p in P} K_(p*product R)(M)`.

Induct on P. Every term containing two distinct processed primes vanishes at
the actual hard cutoff; each remaining insertion subtracts precisely its
original unsigned child. Labels meeting P vanish because a processed label
cannot remain. Labels containing a nonprime vanish directly from prime factors.
Thus no retained coordinate is omitted.

For `M>=10` and selected primes satisfying `2M<=5p`, pair products exceed M.
Only cofactors d=1 and d=2 can have an active child. Assume the exact head budget

`sum_{p in L} K_p(M)<=K_1(M)`.

The expenditure ratio and parent comparison give
`sum K_(2p)<=sum K_p/2<=K_1/2<=K_2`. Every d>=3 child is zero.
Nonnegative expenditures retain these inequalities at every P subset of L.
Therefore every oriented coordinate lies between zero and its original value.
Squaring and summing controls both E_P and V_P by their original values.
Full retained parity also makes every available next prime contract E_P.
This last statement does not assert preservation of parity after that next prime.

## Unconditional nonempty prime supply

At cutoff `M=20N`, take the actual prime pool `U=(8N,9N]`. Every pool prime is
in the two-channel sector and in the second quotient block. The source floor
above gives `K_p(20N)>=sqrt(N)/20`.

The corpus prime-window theorem, at ratio 9/8 and x=8N, eventually gives
`card(U)>=x/(16 log(x))`. The analytic inequality
`log(x)<=2(sqrt(x)-1)` follows by applying `log(y)<=y-1` to y=sqrt(x).
Thus `card(U)>=sqrt(x)/32`, and eventually `card(U)>=700`.
The complete pool mass is then at least `35sqrt(N)`, covering the actual
unit bound `K_1(20N)<=7sqrt(20N)<=35sqrt(N)`.

Each pool contribution is at most `sqrt(M)/15` by the existing analytic
five-quotient ceiling; the unit source is eventually at least that amount.
Select one prime first, then apply the finite selection theorem from below to
the remaining pool and remaining target. This supplies a **nonempty** L subset U
with

`0<=K_1(M)-sum_L K_p(M)<=sqrt(M)/15`.

The exact block identity identifies this residual with F_L(empty), so the head
budget is supplied by the source. Every selected prime also has `2p<M`, hence
`K_(2p)(M)>0`. Consequently

`0<=O_L({2})<K_2(M)`.

This is an interacting block, not an isolated-head block. Its head square is
at most M/225, and nonempty energy contracts, giving

`E_L(M)<=V_empty(M)+M/225`.

Every intermediate subset preserves all retained signs and both original
energy ceilings, and every available next prime contracts there. The theorem
does not assert a lower bound of two on the selected block cardinality.

## Remaining frontier

The result supplies a selected initial block. It does not consume the complete
prime pool, bound a complete growing schedule, or preserve signs after an
arbitrary additional small prime. Those remaining operations require further
source control. The all-cutoff two-prime ceiling, middle quotient profiles,
aggregate SD1 and RH remain open.

## Lean and verification

- `RHTower.MobiusDivisorTwoChannelPrimeBlocks`: five public theorems, including
  the mutual quotient comparison, expenditure ratio, sparse block identity,
  and all-subset parity/energy theorem.
- `RHTower.MobiusDivisorTwoChannelPrimeSupply`: three public theorems, ending in
  `eventually_exists_mobiusDivisorTwoChannelPrimeBlock`, which has no unproved
  arithmetic premise.

Both scratch files and both exact leaves passed `lake env lean`. Only the two
new required oleans were emitted; both leaves are wired once without umbrella,
full, or dependency rebuilds. The eight new public declarations were audited
once in a separate scratch file: only `propext`, `Classical.choice`, and
`Quot.sound`; no added axioms or computational certificates. No numerical
experiment was run for this result. Formal lint passed with 132 existing large-file warnings only. The declaration
index was refreshed once. New card links, added references, umbrella wiring,
new-file whitespace and scoped tracked whitespace checks passed.
