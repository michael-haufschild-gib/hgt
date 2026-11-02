# Signed constant-input Mayer scattering channels

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.
- **Input:** [full positive channel](../3-formalized/gauss-mayer-vector-scattering-channel.md).

## Theorem

For the actual constant-input responses `V_ε(w)=(I−εL_w)⁻¹1`, on
`Re w>0` the negative channel has the holomorphic, nonzero germ

```text
V_−(w)(z) = 1−(1+z)^(−w).
```

Consequently, in `0<Re w<1`, a signed channel has a pole exactly when
`ε=+1` and `ζ(w)=0`, with the already certified zeta multiplicity.
The full negative operator inverse's nonzero rank-one residue at one
annihilates the constant input exactly.

## Proof mechanism

The certified successor response `h_w=1−(1+z)^(−w)` is entire in the
source parameter, has zero boundary evaluation, and satisfies
`(I+L_w)h_w=1`. This also proves `h_w≠0` on the source half-plane.
The negative signed determinant, after removing its possible source
pole, is holomorphic on that connected half-plane and nonzero at three
by the closed-unit primitive-orbit product. Its zeros are isolated.
Multiplying the response equation by the actual inverse gives the
negative-channel germ and order zero everywhere.

Evaluation of the known operator-valued residue limit at the constant
input agrees with `(w−1)V_−(w)`, whose limit is zero by the holomorphic
response. Hence the operator residue annihilates that input. Combine
negative regularity with the full positive vector divisor to classify
both signed constant-input channels.

## Scope

No absence of complex negative-unit eigenvalues is asserted. This
classifies the actual source channel; unexcited eigenspaces and the
full Hermitian realization remain separate obligations. At nonunits,
ring inversion's assigned value need not equal the removable germ.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerSignedScattering.lean` certifies
`successor_equation`, `successor_ne_zero`, `negativeResponse_germ`,
`meromorphicAt_negativeResponse`, `negativeResponse_order`,
`negativeResponse_limit`, `negativeOperatorResidue_constant_zero`,
`signedResponse_order`, and `signedResponse_pole_iff`.

All nine declarations pass direct kernel checks with only `propext`,
`Classical.choice`, and `Quot.sound`.
