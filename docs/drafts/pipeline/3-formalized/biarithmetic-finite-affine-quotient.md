# The exact finite quotient of the positive affine action

- **ID:** biarithmetic-finite-affine-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), finite affine representation theory.
- **Statement:** Every absorbing-horizon positive affine operator is determined by its values on the origin and first cell. The image semigroup has exactly `1+(N+1)(N+2)/2` elements, with explicit canonical representatives.

## Exact classification and proof

Write `T_(a,b)e_j=e_(aj+b)` on `{0,...,N}`, with `a≥1`, `b≥0`, and all out-of-range cells
zero. A cell equality `e_i=e_j` means either `i=j` or both indices exceed `N`.

If `b>N`, the whole operator is zero. Otherwise `T_(a,b)e_0=e_b` determines `b`. The first
positive cell gives `e_(a+b)`. If this is nonzero, it determines `a`. If it is zero, every
positive cell has already escaped, and the operator is just the origin-to-`b` map, independent
of the larger slope. Consequently

`T_(a,b)=T_(c,d)` iff
`(b>N and d>N) or (b=d and (a=c or (a+b>N and c+d>N)))`.

In particular, agreement on `e_0,e_1` implies agreement on every signed row. This also holds
for `N=0`, when the first cell is already zero.

Canonical representatives are one zero operator, and for each `0≤b≤N` the slopes
`1≤a≤N-b+1`. The last slope represents all slopes that erase every positive cell.
They are pairwise distinct by the classification and exhaust the action by replacing `a`
with `min(a,N-b+1)`. The exact count is

`1+Σ_(b=0)^N (N-b+1)=1+(N+1)(N+2)/2`.

The exact affine composition law already proved in the programme closes this finite set under
composition. Thus it is the faithful finite quotient of the positive affine semigroup acting
at this horizon, rather than a periodic quotient of the integer line.

## Contribution and limits

This supplies a complete equality classification and an explicit polynomial-size affine state
space. It concerns the joint additive and multiplicative cell geometry, hence structural
Class III. It does not classify all modules of the finite semigroup algebra, or give a signed
estimate for the actual Möbius coefficients. Changing Euler weights does not change this
geometric classification.

## Verification

- [x] Dependency-closed paper proof, including the exact positive quotient and count.
- [x] Lean equality classification and two-cell criterion.
- [x] Lean canonical code equivalence and exact cardinality.
- [x] Direct leaf check and transitive axiom audit.

Module: `GaloisForLFunctions/BiarithmeticGeometry/FiniteAffineQuotient.lean`. Direct source check passed. All seven principal declarations have transitive axiom sets contained in `propext`, `Classical.choice`, `Quot.sound`. Umbrella import is wired; the umbrella was not compiled.
