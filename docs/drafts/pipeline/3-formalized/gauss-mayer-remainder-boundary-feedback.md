# Remainder boundary poles and rank-one feedback

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2.
- **Input:** [actual source boundary inverse](../3-formalized/gauss-mayer-actual-boundary-resolvent.md).

## Statement

Write `L=R+ζP`, `P f=f(0)1`, and
`r(w)=[Ring.inverse(I−R(w))1](0)`. Put `F(w)=1+2ζ(w−1)`.
Throughout `0<Re w<1`, the meromorphic germ is

```text
r(w) = 2ζ(w−1)/(ζ(w)F(w)).
ord r = −ord ζ − ord F.
```

Thus the observable remainder poles have exactly two possible causes:
`ζ(w)=0` or `ζ(w−1)=−1/2`. Multiplication by `F` recovers the source
scattering germ and its exact zeta multiplicity. No existence or exclusion
of the second kind of pole is asserted.

## Proof

At an invertible source parameter let `g=(I−L)⁻¹1`, `b=g(0)`, and
`Qf=f(0)g`. Then `Q²=bQ` and

```text
I−R = (I−L)(I+ζQ).
(I+ζQ)⁻¹ = I−ζQ/(1+ζb),  when 1+ζb≠0.
```

Hence the actual remainder inverse applied to `1` is `g/(1+ζb)`.
The source boundary identity gives `ζb=2ζ(w−1)` on a punctured
neighborhood avoiding source determinant zeros.

The extra factor has finite analytic order: its entire cleared numerator
is `J(w)=w−2+2Z(w−1)`, where `Z(v)=(v−1)ζ(v)` extends with `Z(1)=1`.
Since `J(2)=2`, the identity theorem excludes an identically zero germ.
Consequently both required inverses exist on a sufficiently small
punctured neighborhood. The shifted numerator is a holomorphic unit
in the strip, so orders add exactly as stated.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerRemainderBoundary.lean`, namespace
`MayerRemainderBoundary`:

- `boundary_eq_feedback`, `feedback_order_ne_top`;
- `boundary_germ`, `meromorphicAt_boundary`;
- `boundary_order`, `boundary_pole_iff`;
- `normalized_boundary_germ`, `normalized_boundary_order`,
  `normalized_boundary_pole_iff`.

Direct production check passed. Ten transitive axiom audits, including
the operator factorization, use only `propext`, `Classical.choice`, and
`Quot.sound`.
