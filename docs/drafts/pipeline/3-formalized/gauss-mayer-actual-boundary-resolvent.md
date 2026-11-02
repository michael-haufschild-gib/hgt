# The actual Mayer boundary resolvent and scattering poles

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 1–2.
- **Input:** [primitive-cone source and cofactor](../3-formalized/gauss-mayer-primitive-cone-scattering-divisor.md).

## Target

For the actual source `L_w=R(w)+ζ(w)P`, define
`b₊(w)=[Ring.inverse(I−L_w)1](0)` and
`b₋(w)=[Ring.inverse(I+L_w)1](0)`.
Ring inversion is the genuine bounded inverse when it exists and zero
otherwise. Let `D(w)=det(I−L_w)` and `B(w)` be its signed constant-mode cofactor.

For `Re w>0`, `b₊(w)=−B(w)/D(w)` and `b₋(w)=0` pointwise.
For `0<Re w<1`, the meromorphic germ of `b₊` is
`2ζ(w−1)/ζ(w)`, with exact order `−ord ζ(w)`.
Thus the actual constant-input/evaluation-output inverse has a pole exactly
at a strip zeta zero, with matching multiplicity. At such a zero the
certified determinant theorem supplies an eigenfunction of `R(w)` at `+1`.
The negative-unit response is identically blind to this scalar sector.

The independently normalized Poincaré scattering coefficient is
`a(w/2)b₊(w)/2`, with `a(s)=π^(1/2)Γ(s−1/2)/Γ(s)`, initially in `Re w>2`
and then as a meromorphic germ. In the open strip, the Gamma factor is
a holomorphic unit: `w/2` has positive real part and `w/2−1/2` has real part
strictly between −1/2 and 0, so neither argument meets a Gamma pole.
Therefore the independent
scattering coefficient at `s=w/2` has the same exact pole multiplicity.
No point value at a singular operator is
used as a pole detector.

## Proof

1. The existing rank-one determinant proof only uses a supplied response
   `(I−L_w)f=1`. Generalizing that proof gives
   `det(I−L_w+tP)=D(w)(1+t f(0))`, hence `B(w)=−D(w)f(0)`.
2. If `D≠0`, the actual Fredholm invertibility theorem supplies the response
   `f=(I−L_w)⁻¹1`. If `D=0`, both ring inversion and division by `D` are
   assigned zero. This proves the pointwise positive-unit identity.
3. The exact successor response `h=1−(1+z)^(−w)` satisfies
   `(I+L_w)h=1` and `h(0)=0`. Uniqueness when invertible, and the zero
   assignment otherwise, prove `b₋=0`.
4. The holomorphic cofactor has finite order everywhere in the source
   half-plane, because `B(1)≠0`. It is therefore nonzero on a punctured
   neighborhood of any point. Cancel it in the certified local
   factorization `D=−ζB/(2ζ(·−1))`. The shifted numerator is a holomorphic
   unit throughout the open strip, giving the exact pole multiplicity.
5. The certified independent Poincaré normalization identifies the same
   scalar germ with the scattering coefficient and fixes the Gamma factor.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerBoundaryResolvent.lean`, namespace
`MayerBoundaryResolvent`:

- `positiveBoundary_eq_cofactor`, `negativeBoundary_zero`;
- `positiveBoundary_germ`, `meromorphicAt_positiveBoundary`;
- `positiveBoundary_order`, `positiveBoundary_pole_iff`;
- `actualScattering_eq_boundary`, `scattering_germ`;
- `scattering_order`, `scattering_pole_iff`.

Direct production check passed. All ten transitive axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This identifies the scalar scattering sector of the actual inverse.
It does not exclude all other remainder eigenvalue events or supply a
Hermitian form, a spectral gap, or resonance exclusion.
