# Shifted products and logarithmic winding

- **ID:** SPL-shifted-products
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [§2.9](../../../reports/review-0711/obstacles-summary.md)
- **Statement:** Classify simultaneous product coincidences under translation;
  determine which quantitative information survives reduction of logarithms modulo a period.

## Mathematical targets

1. For natural numbers, equality of `ab` and `(a+1)(b+1)` determines
   the unordered pair `{a,b}`. Obtain the exact mixed collision count on any finite set.
2. Extend from pairs to tuples using translated product polynomials.
3. Transfer integer-product separation to real logarithms, retaining all nonzero
   winding cells. Determine the range where a common cell forces a diagonal collision.
4. Bound the number or occupation of nonzero cells for actual phase level sets.
   This last estimate, not exact algebra, is the proposed input beyond diagonal moments.

## Scope

No zero-free strip follows from targets 1–3 alone. All five tools and four
questions in the programme README remain required. No novel estimate is claimed
before its dependency-closed proof and Lean audit.

## Exact statements

Let `S(a,b)=(ab,(a+1)(b+1))`.

* `S(a,b)=S(c,d)` iff the pairs agree up to permutation. For a finite
  alphabet of cardinality `M`, the ordered collision count is `2M²−M`.
* On `[1,N]`, a real cell of radius `ε` for both coordinates of `t log S`
  contains at most two ordered pairs if `2ε(N+1)²<|t|`.
* The pairs `(n+1,n+4)` and `(n+2,n+3)` have products differing by `2`
  after every common translation; their logarithmic differences are at most
  `2/(n+1)²`. The inverse-square resolution is sharp in order.
* If both `n` and `n+1` belong to prescribed phase arcs of radius `ε`,
  their pair-winding signatures have fibres of size at most two when
  `4ε(N+1)²<|t|`. Consequently there are at least `M²/2` distinct signatures.
* A multiset of cardinality `k` is determined by its translated products
  at any `k` distinct parameters: the difference of the two monic product
  polynomials has degree below `k`.

These are elementary reconstruction and packing results. They are not claimed
as new sum-product estimates in the literature or as a saving past VK.

## Proofs

Subtracting the two product equalities gives equality of pair sums. Equal sum
and product identify the two roots of the same quadratic, hence the unordered
pair. A diagonal pair has one ordered representative; every other pair has
two. Summing the fibre sizes gives `M+2(M²−M)=2M²−M`.

Distinct positive integers at most `B` have logarithmic separation at least
`1/B`. Two readings in a common radius-`ε` real cell differ by at most `2ε`.
Apply this with `B=(N+1)²` to both products, then use pair reconstruction.
For phase arcs, adding two remainders gives radius `2ε`; fixing both winding
sums fixes both real cell centres. Counting fibres gives `M²≤2|W|`.

The displayed neighbouring pairs have equal sums and product difference `2`
after every common translation. For `x>0`,
`0≤log(x+2)−log x≤2/x`, by `log(1+u)≤u`. Their smaller translated product
is at least `(n+1)²`, proving the stated resolution bound.

For tuples of cardinality `k`, the two product polynomials are monic of degree
`k`. Their difference has degree below `k`; vanishing at `k` distinct parameters
forces equality. Unique factorization of the monic linear factors recovers
the multiset, including multiplicities.

## Lean evidence

`ShiftedProductRigidity.lean` passes the direct Lean check. Its classification
and exact collision count depend only on `propext`, `Classical.choice`,
`Quot.sound`. `LogarithmicCollisionCells.lean` passes its dependency build,
and `card_logPairCell_le_two` has the same standard axiom set; its final direct
check remains required. The winding, sharpness and general tuple modules remain
under verification.
