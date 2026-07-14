# Almost-disjoint isodivisorial frame core

- **ID:** `almost-disjoint-isodivisorial-frame-core`
- **Stage:** 3-formalized
- **Type:** THEOREM / FINITE TAIL-RANK AND DIVISOR BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE] [NOT NEW IN ISOLATION]`
- **Parent route:**
  `../../2-fully-proven/needs-audit/maximal-isodivisorial-ht-free-frame.md`

## Statement

Let `J` be finite, let `P` be an arbitrary coordinate set, and let `A_j` be infinite subsets of
`P` with pairwise finite intersections.  If infinitely many coordinates lie outside all the
`A_j`, define the `j`-th sign column to be negative on `A_j` and positive elsewhere.  Then the
resulting `J` sign columns are linearly independent modulo finite coordinate support.

Multiplying every column by the same nowhere-zero coordinate weight preserves this tail
independence.  Independently, multiplying a meromorphic germ by a holomorphic nonvanishing germ
preserves its local meromorphic order.

## Proof

Inside any finite almost-disjoint subfamily, each `A_j` has an infinite private block: delete the
finite union of its pairwise intersections with the other members.  Suppose a linear combination
of the sign columns is supported on finitely many coordinates.  At an outside coordinate beyond
that support, every sign is positive, so the sum `C` of all coefficients is zero.  At a private
coordinate of `A_j` beyond the support, only the `j`-th sign is negative, so the combination is
`C-2c_j`.  Therefore every `c_j` vanishes.

For a common weight `w(p) != 0`, every linear combination of the weighted columns is exactly
`w(p)` times the corresponding unweighted combination.  The two supports are identical.  The
local divisor assertion is the standard additivity of meromorphic order, with a holomorphic unit
having order zero.

## Scientific role

These finite mechanisms are elementary in isolation.  Their role is to certify the nonclassical
assembly in the parent route: a continuum almost-disjoint sparse-prime frame can preserve one
exact divisor while retaining full finite differential rank after multiplication by the common
Helson phase.

## Formal theorem surface

The implementation is
`formal/GaloisForLFunctions/HTGeometry/AlmostDisjointIsodivisorialFrame.lean` and contains:

- `setFlipOrientation` and its exact sign evaluations;
- `primeOrientationTailIndependent_setFlip_of_exclusive`;
- `infinite_exclusiveBlock_of_pairwise_finite_intersections`;
- `primeOrientationTailIndependent_setFlip_of_almostDisjoint`;
- `tailCoefficientIndependent_commonWeight_iff`;
- `meromorphicOrderAt_mul_analyticUnit_eq`.

## Gates

- [x] exclusive-block tail independence proved
- [x] finite almost-disjoint subfamilies reduced to exclusive blocks
- [x] common nowhere-zero phase invariance proved
- [x] analytic-unit divisor-order preservation proved
- [x] direct module check passed
- [x] narrow module build passed
- [x] axiom audit completed
- [x] project lint and generated indexes refreshed
