# The full constant-input Mayer scattering channel

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.
- **Inputs:** [actual boundary inverse](../3-formalized/gauss-mayer-actual-boundary-resolvent.md), [holomorphic state](../3-formalized/gauss-mayer-holomorphic-scattering-state.md).

## Theorem

Let `V(w)=(I−L_w)⁻¹1` be the actual `DiscSpace` response, with ring
inversion zero at nonunits. Let `C(w)=(w−2)H_w` denote the certified
holomorphic filled state. On `Re w>0`,

```text
C(w) ≠ 0,
V(v) = [ζ(v)(v−2)]⁻¹ C(v)             as punctured germs at w,
ord_w V = −ord_w [ζ(v)(v−2)].
```

Thus the entire vector channel, not only its evaluation at zero, has
exact zeta-zero pole multiplicity in `0<Re w<1`, a simple pole at two,
and a simple zero at one. At strip zeta zeros, the zeta-cleared vector
converges to the explicit observable remainder eigenfunction `H_w`.
Away from zeta zeros and the scalar poles, `H_w/ζ(w)` is an analytic
particular response even at zeros of the full Fredholm determinant.

## Proof mechanism

The pole-cleared source determinant is holomorphic on the connected
right half-plane and is nonzero at one by the certified positive pole
coefficient. Its zeros are therefore isolated. Away from them and
`w=1,2`, multiply `(I−L_w)H_w=ζ(w)1` by the actual inverse. This proves
the displayed vector identity on every punctured germ.

The filled state never vanishes. At two, its defining Mellin expression
is `2 endpoint_1`. At one, its boundary value is one. Elsewhere, if
`ζ(w)≠0`, the forcing equation excludes a zero state. If `ζ(w)=0`,
classical right-half-plane nonvanishing puts `w` in the open strip,
where `H_w(0)=2ζ(w−1)≠0`. Scalar multiplication therefore gives the exact
Banach-valued meromorphic order without any unobserved vector factor.

The residue unit `(w−1)ζ(w)` has value one, so the scalar denominator
has order minus one at one. At two its only zero is the simple linear
factor. In the open strip, the latter is a unit and the pole multiplicity
is exactly the finite zeta multiplicity.

## Scope

These are germs of the actual constant-input response. Assigned values
of ring inversion at nonunits need not equal their removable analytic
representatives. Full eigenspace classification and a Hermitian form
remain separate obligations; no such input is assumed here.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerScatteringVector.lean` certifies
`clearedState_ne_zero`, `vectorResponse_germ`, `meromorphicAt_vectorResponse`,
`vectorResponse_order`, `vectorResponse_strip_order`, `vectorResponse_pole_iff`,
`analyticAt_regularResponse`, `regularResponse_equation`,
`vectorResponse_germ_regular`, `zeta_cleared_limit`, and
`vectorResponse_order_zero/one/two`.

All declarations pass direct kernel checks with only `propext`,
`Classical.choice`, and `Quot.sound`.
