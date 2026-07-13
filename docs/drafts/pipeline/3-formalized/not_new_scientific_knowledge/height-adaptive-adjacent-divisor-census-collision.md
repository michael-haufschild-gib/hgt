# Height-adaptive adjacent divisor-census collision

- **ID:** `height-adaptive-adjacent-divisor-census-collision`
- **Stage:** 3-formalized
- **Type:** `[LARGE OUTLANDISH DETOUR] [PROVED BRIDGE] [NOT AN RH PROOF]`
- **Scientific status:** not new scientific knowledge
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHeightAdaptiveAdjacentCensusCollision.lean`
- **Inputs:** `height-adaptive-finite-rh-ladder.md`,
  `dyadic-sharp-cancelled-source-parity-collision.md`

## Claim

The height-adaptive DISC route does not need a vanishing Xi census, a pointwise multiplicity rung,
or a regional Kummer root.  At each integer height it is enough to prove one equality in a finite
dyadic ring between two adjacent explicit divisor censuses.

Let `M(T)` be the total multiplicity of right-half Xi zeros in the upper box below height `T`, let
`D(T)` be the number of distinct such zeros, and let `P(T)` be the sum of the shifted cancelled
sharp-source orders at those points.  The exact local order-loss theorem gives

```text
P(T) = sum_z (ord_z Xi - 1),
M(T) = P(T) + D(T).                                    (1)
```

Choose `k(T)` from the unconditional Xi zero-count envelope so that `2^k(T)` is larger than the
entire divisor mass in the box.  If

```text
M(T) = P(T)  in ZMod(2^k(T)),                           (2)
```

then `2^k(T)` divides `D(T)`.  But `0 <= D(T) <= M(T) < 2^k(T)`, hence `D(T)=0`.  Applying this at
all positive integer heights exhausts the right critical half-strip and proves RH.

## Why this is a different chain

The existing height-adaptive census asks for `M(T)=0 mod 2^k(T)`.  The new condition asks only for
equality of two generally nonzero adjacent censuses.  It imposes no local divisibility on any Xi
order.  The existing adjacent-parity collision asks that every Xi order and every cancelled-source
order be even.  The new condition is aggregate, height-dependent, and requires no pointwise square
root of either function.

The Lean object `cancelledSourceCommonCensusH` is not yet a source boundary invariant.  It evaluates
the explicit cancelled source at the target-defined Xi box points and then sums the resulting
orders.  A source proof must replace this target-sampled definition by an invariant constructed
before the zero set is extracted.  The natural replacement is not the raw boundary homotopy class
of the pair: common/gcd-divisor degree is unstable under such homotopy.  A viable replacement must
retain the finite zero algebra, a subresultant/Fitting module, or an equivalent derived incidence
object.

## Formal theorem

Lean proves:

- `cancelledSource_shift_order_eq_pred_of_mem_boxFinset` — the source order is exactly the Xi
  predecessor order at every enclosed right-half zero;
- `boxCancelledSourceCommonOrderSum_eq_pred` — the corresponding finite common-divisor sums agree;
- `boxOrderSum_eq_pred_add_distinct` — equation `(1)`;
- `riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus` — the cofinal adjacent-census equality
  implies RH.

## No-go test and positive residue

A pointwise attempt to identify the two divisors is impossible: their local orders differ by one
at every zero.  A global analytic unit relating the two functions would therefore already imply
zero-freeness and would hide RH in the premise.

Raw boundary-pair homotopy is also insufficient.  Let `A,C` be holomorphic on a neighborhood of a
bounded domain and suppose `(A,C)` has no common boundary zero.  For every sufficiently small
generic nonzero constant `epsilon`, the boundary pairs

```text
(A,C)  and  (A,C+epsilon)
```

are homotopic through maps to `C^2 \ {0}`, while `A` and `C+epsilon` have no common interior zero.
Indeed the zero set of `A` in the domain is finite, so `epsilon` may avoid the finitely many values
`-C(z)` at those zeros; compact boundary separation preserves the homotopy.  Thus no invariant of
the raw boundary-pair homotopy class can equal the common-divisor degree.

The positive statement is algebraic.  For a source-defined bounded zero algebra

```text
Q = O(U)/(A),
```

multiplication by the cancelled source `C` has, at a zero of `A` of order `m`, one-dimensional
image and cokernel dimension `m-1`.  Hence its global image is the socle of `Q`, its rank is the
number of distinct zeros, and its cokernel dimension is the adjacent common-divisor census.  The
finite-ring equality is therefore a rank-divisibility target on a source module, not a boundary
winding target.  Local divisor equality, local Kummer roots, and compatibility between heights
remain unnecessary.

## Two-ended audit

- `[PROVED]` the cancelled sharp source is explicit and holomorphic on the relevant half-plane;
- `[PROVED]` its order at each shifted right-half Xi zero is exactly one less than the Xi order;
- `[PROVED]` the unconditional Xi zero-count envelope bounds the distinct count in every box;
- `[PROVED]` one height-adapted adjacent-census equality per integer height implies RH;
- `[PROVED ON PAPER]` raw boundary-pair homotopy cannot determine the common-divisor census;
- `[PROVED ON PAPER]` cancelled-source multiplication on the bounded zero algebra has rank equal to
  the distinct-zero count and cokernel dimension equal to the predecessor census;
- `[OPEN CORE]` construct that finite-ring equality from the completed prime--Gamma/sharp-window
  source module without reading the Xi zero set or assuming a divisor classification;
- `[KILL CONDITION]` retire any construction whose boundary homotopy is defined only after choosing
  the enclosed Xi zeros, whose equality is merely `(1)` reduced modulo the chosen modulus, or which
  treats common-divisor degree as an invariant of the raw pair-valued boundary map.

## Gates

- [x] exact local order-loss adapter
- [x] exact aggregate divisor decomposition
- [x] height-adapted finite-ring capstone
- [ ] source-defined adjacent zero-algebra rank congruence
- [ ] RH
