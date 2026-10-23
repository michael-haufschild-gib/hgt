# Exact balanced product collision fibres

- **ID:** goldbach-balanced-product-collisions
- **Stage:** 3-formalized
- **Type:** BRIDGE; finite arithmetic classification, no novelty claim
- **Source:** [compensated smoothing failure](../../5-failed/goldbach-compensated-product-collision-cost.md)
- **Lean:** [BalancedProductCollisions.lean](../../../../../formal/GaloisForLFunctions/goldbach/BalancedProductCollisions.lean)

## Statements

Let I_X be the integers in `(X,2X]`. For actual rows m₁,m₂ in I_X and
a natural shift h, let F(m₁,m₂,h) contain the pairs n₁,n₂ in I_X with

    m₁n₁+h=m₂n₂.

Writing g=gcd(m₁,m₂), the unconditional fibre bound is

    #F(m₁,m₂,h) ≤ g if g|h, and 0 otherwise.          (1)

Let C_X(h) sum these fibre cardinalities over both rows. For every
positive h,

    C_X(h) ≤ Σ_(g|h) g·#{m∈I_X:g|m}²
           ≤ 4X² Σ_(g|h) 1/g.                       (2)

For h=0, let a=m₁/g and b=m₂/g. There is an exact classification:

    F(m₁,m₂,0)={(bt,at): X/min(a,b)<t≤2X/max(a,b)}.

Consequently

    #F(m₁,m₂,0)=floor(2X/max(a,b))−floor(X/min(a,b)),  (3)

with natural-number subtraction. Summing (3) gives the complete diagonal
collision count. Zero-length intervals are included: the formal row
indices are `Fin X`, so empty intervals contribute no rows or columns.
Positive h is represented by `ℕ+`; there is no analytic premise.

## Dependency-closed paper proof

Fix m₁,m₂ and put b=m₂/g. Subtract two collision equations and cancel
the common factor modulo m₂. Their n₁ coordinates are equal modulo b.
Writing n₁=X+i+1, the quotient floor(i/b) lies in `[0,g)` because
`i<X<m₂=gb`. Equal quotient labels and equal residues recover i, hence
n₁. The original equation and m₂>0 then recover n₂. This injects the
fibre into g labels. Also g divides both products, so it divides h.
This proves (1), including h=0.

For h>0, the contribution of each row pair is at most the sum of its
common divisors g that divide h. Interchanging the finite sums gives
the first bound in (2). There are at most floor(2X/g) rows divisible by
g. Since g>0 on the divisor set,

    g·#{m∈I_X:g|m}² ≤ g(2X/g)² = 4X²/g.

This proves the second bound without an estimate for a signed sum.

At h=0, cancellation modulo m₂ gives b|n₁. Put t=n₁/b. The original
equality and `g a=m₁`, `g b=m₂` give n₂=at. The interval conditions
are precisely `X<min(a,b)t` and `max(a,b)t≤2X`. Conversely, each t
in that interval gives one actual column pair. The explicit inverse
t=n₁/b proves the bijection and (3). All bounds and positivity used in
the proof follow from the actual interval membership.

## Lean declarations and audit

Namespace `GaloisForLFunctions.Goldbach`:

- `card_balancedProductCollisionFiber_le_gcd`
- `card_balancedProductCollisionFiber_le_gcd_gate`
- `balancedProductCollisionCount_le_divisorMass`
- `balancedProductCollisionCount_le_reciprocalDivisors`
- `card_balancedProductCollisionFiber_zero`
- `balancedProductCollisionCount_zero`

`lake --old env lean GaloisForLFunctions/goldbach/BalancedProductCollisions.lean`
passed from `formal/`, exit 0, without warnings. All six closures were
audited; only `propext`, `Classical.choice`, and `Quot.sound` occur.
Temporary audit directives were removed without changing proof bodies.
The module is wired into `goldbach/Main.lean`; the umbrella was not built.

Audit log: `/tmp/hgt-goldbach-balanced-collisions-audit.log`.
Index regeneration passed. The targeted diff check is clean, and the
source contains no forbidden proof marker or raised proof budget.

The prime-harmonic diagonal lower bound and divergence of the compensated
smoothing norm are paper corollaries recorded on the failed-route card.
They are not additional Lean declarations in this module. The signed
Möbius covariance and the all-even Goldbach target remain unproved.
