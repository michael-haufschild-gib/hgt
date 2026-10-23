# Does removing the periodic bias repair product smoothing?

- **ID:** goldbach-compensated-product-collision-cost
- **Stage:** 1-in-progress
- **Type:** CONJECTURE under attack; no analytic input assumed in Lean
- **Parent:** [product smoothing audit](../5-failed/goldbach-balanced-product-smoothing.md)
- **Source:** BVI short-window transfer, followed by exact residue compensation

## Exact candidate

Let d_X count ordered products from `(X,2X]²`. Let H tend to infinity,
with H=o(X²), and fix q≥2 dividing X and H. On a complete residue window
containing the support of `f=d_X−A_Hd_X`, let P_q be the orthogonal
projection onto residue-constant rows. The repaired candidate is

    ||(1−P_q)f||² = o(X²).

The preceding cycle identified P_q f exactly. This candidate asks whether
the remaining multiplicative collisions are cheap enough for the same
absolute-norm transfer. It does not ask for or assume Möbius cancellation.

## Attack: nonzero determinants versus equal products

Write `C_X(h)=Σ_v d_X(v)d_X(v+h)`. At h≠0 decompose
`m₁=ga,m₂=gb` with gcd(a,b)=1. Then g divides h. There are at most
`4X²/g²` choices of a,b. For each, `a n₁−b n₂=h/g` restricts n₁ to
one class modulo b. Since b>X/g, the interval contains at most
`X/b+1≤2g` possible n₁. Thus

    C_X(h) ≤ 8X² Σ_(g|h) 1/g.                         (1)

For h=0, choose a prime p with `11≤p≤X/8`, an integer b with
`3p/4≤b<p`, and independent g,t in `(X/b,2X/p]`. There are at least
`p/8` choices of b and at least `X/(2p)` choices of each g,t. The four
coordinates `(gp,bt,gb,pt)` lie in `(X,2X]` and have equal products.
They determine the parameters uniquely: gcd(gp,gb)=g, then p and b
are recovered, and finally t. Therefore

    C_X(0) ≥ (X²/32) Σ_(11≤p≤X/8, p prime) 1/p.       (2)

The interval counts in (2) follow from
`floor(2X/p)−floor(X/b)≥2X/p−X/b−1≥X/(2p)` since X/p≥8,
and `p−ceil(3p/4)=floor(p/4)≥p/8` since p≥11.

Also

    Σ_(1≤h<H) Σ_(g|h) 1/g
      = Σ_(g<H) floor((H−1)/g)/g ≤ H Σ_(g≥1)1/g² ≤ 2H.

Expand the smoothing norm, discard only the nonnegative norm of the
averaged row, and retain the h=0 term separately. For H≥4, (1) gives

    ||f||² ≥ C_X(0)/2 − 32X².                        (3)

Let E_q=Σ_r(ν_q(r)−q)². The exact projection law gives
`||P_q f||²≤X² E_q/(4q³)` because the window length is at least 4X².
Combining (2) and (3),

    ||(1−P_q)f||² / X²
      ≥ (1/64) Σ_(11≤p≤X/8, p prime)1/p − 32 − E_q/(4q³).  (4)

For every fixed q, divergence of the prime reciprocal sum makes (4)
diverge. This would falsify the repaired candidate more strongly than
the previous periodic obstruction.

## Proof status and remaining work

The finite counting argument is recorded before formalization. Audit
its exact cardinality/injection lemmas before assigning formalized status.
The source `RHTower.tendsto_primeMass_atTop` in
`RHTower/CreaseBudgetPrimeMass.lean` was inspected: it has no premise and
deduces divergence from mathlib's `not_summable_one_div_on_primes`.
That theorem's elementary smooth/rough counting proof in
`Mathlib/NumberTheory/SumPrimeReciprocals.lean` was also inspected.
No prime-counting asymptotic is needed for (4). A new closure audit of this
dependency is not claimed. The formula
for E_q and the exact finite projection mechanism are covered by the
preceding cycle. No Lean version of (1)–(4) is claimed yet.

Positive survivor to extract if the attack closes: a finite arithmetic
collision law that separates equal products from every nonzero determinant,
with the explicit prime-harmonic diagonal lower bound. This is not a signed
Möbius estimate. A failure of absolute smoothing transfer calls for direct
control of the compensated signed covariance, not another norm bound.

No scientific novelty claim; no web novelty audit undertaken for these
elementary counting deductions. The unconditional Goldbach target is unchanged.

## Sharper finite survivor: one gcd label per collision

The previous goal turn made verified progress: the exact residue profile,
actual smoothing row and its error floor were formalized and closure-audited.
The present count refines the nonzero-determinant bound before formalization.

Fix row values m₁,m₂ in `(X,2X]`, put g=gcd(m₁,m₂), b=m₂/g, and
consider pairs n₁,n₂ in the same interval satisfying
`m₁n₁+h=m₂n₂`. Their first coordinates all lie in one class modulo b.
Writing n₁=X+i+1, the quotient `floor(i/b)` lies in `[0,g)` because
`i<X<m₂=gb`. That quotient, together with the fixed residue class,
recovers i and then n₂. Thus the fibre has at most g elements, and is
empty unless g divides h. This argument includes h=0 at the fibre level.

For h≥1, sum over row pairs. Each pair's gcd contribution is bounded by
the sum of all common divisors g of the pair that also divide h. There
are at most floor(2X/g) row values divisible by g. Consequently

    C_X(h) ≤ Σ_(g|h) g · #{m∈(X,2X]:g|m}²
           ≤ 4X² Σ_(g|h) 1/g.                        (1′)

This strengthens (1)'s constant from 8 to 4. In (3)–(4), the constant
32 can consequently be replaced by 16. The stronger finite theorem has
the same closed elementary proof; no cancellation input is involved.
The exact quotient-label injection is the positive arithmetic mechanism
to certify, rather than a negative smoothing statement alone.

## Exact zero-difference fibre

For the same actual row values m₁,m₂, let g=gcd(m₁,m₂), a=m₁/g,
b=m₂/g. The stronger finite classification is

    #{(n₁,n₂)∈(X,2X]² : m₁n₁=m₂n₂}
      = floor(2X/max(a,b)) − floor(X/min(a,b)),        (5)

where subtraction on the right is truncated in the natural numbers.
Its complete parametrization is `(n₁,n₂)=(bt,at)` with

    floor(X/min(a,b)) < t ≤ floor(2X/max(a,b)).

To prove it, divide by g. Coprimality of a,b forces b|n₁, and cancellation
then gives n₂=at. The two lower interval constraints say
`X<min(a,b)t`, while the two upper constraints say `max(a,b)t≤2X`.
Both normalized factors are positive, so integer division gives exactly
the displayed t interval. The parametrization is injective since b>0,
and its inverse t=n₁/b is explicit. This is a dependency-closed finite
paper proof, with verdict BRIDGE and no scientific novelty claim.

Formula (5), together with the gcd-restricted nonzero count (1′), is the
positive classification selected for formalization. Summing its prime-row
subfamilies recovers (2); that summation is still to be certified explicitly.
