# Ordinary-pair truncation of the actual Hedenmalm current

- **Stage:** 3-formalized
- **Type:** THEOREM; Lean formalized
- **Wall:** Σ6

For `0≤a<1/2` and real `b`, the actual Hedenmalm current is
`J(a,b)=2H(a,b)`, where `H` is the literal aperture-weighted full-source
tail from [the weighted remainder theorem](../3-formalized/full-theta-aperture-pair-remainder.md).
Consequently its ordered-pair truncation has error

`|J(a,b)−2Σ_(1≤n,m≤M)P_nm(a,b)|`
`≤288a C(0)exp(−π(M+1))/((9−a²)²(1−exp(−π))²)`.

## Proof

Write `g(s)=Re W_Φ(s/2,b)` and `w_a(r)=sinh(ar)+ar cosh(ar)`.
The established integrability of the full theta center-mixing kernel
implies integrability of `s sinh(as)g(s)` on `s>0`.
Also `∫_(0<r<s) w_a(r)dr=s sinh(as)` for `s>0`, by differentiating
`r sinh(ar)`. The weight is nonnegative.

For `F(s,r)=1_(r<s) w_a(r)g(s)` on the positive quadrant, its iterated
absolute integral is therefore
`∫_(s>0)s sinh(as)|g(s)|ds<∞`. Measurability and Fubini give

`H(a,b)=∫_(r>0)w_a(r)∫_(s>r)g(s)ds dr`
`=∫_(s>0)s sinh(as)g(s)ds`.

The existing radial Wigner identity says `J` is twice this last integral.
Multiplying the established aperture-weighted remainder by two gives the
claimed bound. This is an exact identification and absolute error bound;
the signed lower bound required for all ranks remains open.

## Lean

[ThetaPairApertureCurrent.lean](../../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ThetaPairApertureCurrent.lean):

- `thetaFullApertureTail_eq_radialIntegral`: justified triangular integral exchange.
- `thetaCuspCenterMixedFourierCurrent_eq_two_mul_apertureTail`: exact source normalization.
- `thetaCuspCenterMixedFourierCurrent_pair_remainder_le`: uniform current truncation error.

Direct source check passes; capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
