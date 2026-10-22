# CCM-FU: signed three-prime repair interaction

- **Stage:** 1-in-progress; complete third-interaction and late-block source laws are [formalized](../../../3-formalized/ccm-fu-three-prime-late-block-transport.md). General prescribed-prime repair remains open.
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH.
- **Target:** The complete third energy difference needed when a prescribed first prime is followed by a repair and any further successor.
- **Parent:** [prescribed-prime repair](../../ccm-fu-forced-prime-repair.md).

## Exact source calculation

Fix distinct unprocessed active primes p,q,r. For every remaining label R
free of these primes, let a,b,c,d,e,f,g,h be the literal signed fibres at
R, R+p, R+q, R+r, R+p+q, R+p+r, R+q+r, R+p+q+r respectively.
Define D3 as the eight-term third energy difference: the triple energy,
minus all three double energies, plus all three single energies, minus
the current energy. Then

D3(P;p,q,r)=2 sum_R(a*h+b*g+c*f+d*e).

Proof: subtract the proved p,q mixed difference at P from the same
difference at P+r. Split each sum into r-free and r-containing labels.
The inserted fibres add their two r partners and vanish on r-containing
labels. Expanding cancels all terms except the four complementary pairs.
This is a finite exact source identity, including every overlap.

## Removing the uncontrolled parent

If p*q*r>=M, h=0 at every label by the proved product support theorem.
Every surviving factor then contains at least one of p,q,r. Each such
factor depends only on processed primes below its adjacent quotient
cutoffs, by the proved fibre interpolation. Consequently the whole D3
is unchanged when P is replaced by P intersect [0,N), provided
M/p+1, M/q+1 and M/r+1 are all at most N.

This quotient-core refinement is a paper consequence, not among the
checked declarations. The late-block theorems below establish a stronger
sign statement for isolated late cores without that quotient condition.

If every processed prime is at least N, all copied factors equal the
original empty-core factors. Their parity signs are known from the
literal unsigned channels: every complementary singleton/doubleton
product is nonpositive. Thus D3<=0, with no premise about the current
energy, head sign, cardinality or reserve. This controls a class of
already mixed source states at the actual cutoff, not a fixed-core limit.

If all three pair products are at least M, every doubleton and the
tripleton vanish, so D3=0 for arbitrary P. This exact zero boundary needs
no condition on processed primes.

## Remaining hard comparison

The full repair must still choose q so the triple energy lies below the
original budget for every r. A nonpositive D3 removes one source of
additional cost, but does not by itself pay the complete first and
second differences. The overlapping triple sector and active processed
primes inside the copied quotient fields still need signed control.
No full repair or RH theorem is assumed here. No numerical experiment
is needed for the displayed identities and sign argument.

## Complete overlap transport for late-prime blocks

The corpus supplies a stronger source invariant than quotient inactivity:
processing only primes s with M<=2s preserves the original parity of
every nonempty fibre. Thus D3<=0 for every such processed block when
p*q*r>=M, independently of the current head sign. Lean checks this
statement and D3(empty)<=0 including all joint overlaps.

For the remaining overlap, an isolated late-prime merger changes energy
by twice its literal signed coefficient times the current scalar head.
Taking three further differences differentiates that head exactly to
the p*q*r fibre. Lean proves the exact batch law

D3(L;p,q,r)=D3(empty;p,q,r)
 +2*(sum_(s in L) K_s(M))*K_(p*q*r)(M),

where K is the original unsigned channel and p,q,r are outside L.
This retains the complete overlap cost and measures precisely how the
late block spends the initial negative third-order margin. Lean also
proves the stronger transport identity at every starting core P: the
change is twice the signed block mass times the retained triple fibre
at P. No reserve or head-sign hypothesis is required. Product support
makes this change exactly zero whenever p*q*r>=M.

## Intermediate admission through a whole late-prime block

The same literal block-energy theorem extends from Q to the full exact
successor envelope. For R subset L, with L an unprocessed late-prime pool,
Lean proves

Psi(P+R)<=max(Psi(P),Psi(P+L)).

For a successor q outside L, apply the existing block endpoint theorem
at the starting core P+q. Its two endpoint energies occur in the two
displayed envelopes. For q in L but not yet in R, apply the original
block theorem to R+q. The current energy is its R instance. This proves
all successor comparisons at once, without an additive cost per merger.
It closes intermediate admission within a late-only block once its two
endpoints are controlled. It does not choose an admitted endpoint or
permit the block to include a nonisolated prime.
