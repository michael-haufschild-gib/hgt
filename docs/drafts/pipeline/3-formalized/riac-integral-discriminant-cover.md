# Integral discriminant cover and signed arithmetic fibres

- **ID:** RIAC-integral-discriminant-cover
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [discriminant-cover programme](riac-discriminant-cover-signed-counts.md)
- **Statement:** One integral coefficient equation realizes the actual polynomial discriminant cover, identifies every signed fibre with its arithmetic transporter weight, and gives independent counts `2`, `2q`, `q^n` in degrees zero, one and at least two.

## Integral equation and local signs

There is a single polynomial `Δ_n ∈ ℤ[c₀,…,c_(n−1)]`. For every monic
`f=X^n+Σ_(i<n)c_i X^i` over an integral domain,

`Δ_n(c)=Polynomial.discr(f)`.

The coefficient equation commutes with arbitrary ring homomorphisms. For
an ordered root tuple, its value is `V(x)^2`, retaining root multiplicities
and arbitrary characteristic. Thus the actual affine points `(c,y)` with
`y²=Δ_n(c)` are in bijection with the monic-polynomial discriminant cover.

Over an odd finite field `F`, the quadratic character `χ(disc(f))` equals
the signed transporter weight of the Frobenius-stable root orbit of `f`,
point by point. Each fibre has cardinality `1+χ(disc(f))`: a collision gives
one point; preserved and reversed orientations give two and zero.

## Proof and independent count

Start from the integral symmetric discriminant. Substitute signed reversed
coefficients, using Vieta to identify its evaluation with the Vandermonde
square. For a split monic polynomial, evaluate its derivative at each
labelled root. The resultant is the product of all ordered root differences;
pairing reverse differences gives the discriminant sign times `V(x)^2`.
The Sylvester formula cancels that sign. Splitting-field comparison and
fraction-field descent identify the coefficient polynomial with the actual
discriminant. Monicity also proves compatibility with coefficient maps.

Vieta identifies the complete monic coefficient space with actual stable
root orbits. Independent normal-basis bijections count every permutation
twist equally; a transposition cancels their total signed weight for `n≥2`.
Summing the identified fibres gives

`#D_n(F)=q^n`, and `Σ_(f monic, deg f=n) χ(disc(f))=0` for `n≥2`.

No polynomial Möbius degree-sum theorem enters this count. In degrees zero
and one the discriminant is one, giving `2` and `2q` points directly.

## Formalization

[MonicRootDiscriminant.lean](../../../../formal/GaloisForLFunctions/HTGeometry/MonicRootDiscriminant.lean):
`exists_root_tuple_of_monic_splits`, `resultant_rootPolynomial_derivative`,
`discr_rootPolynomial`, `map_discr_of_monic`.

[CoefficientDiscriminantCover.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/CoefficientDiscriminantCover.lean):
`integralCoefficientDiscriminant`, `coefficientOrientationDiscriminant_prod`,
`coefficientOrientationDiscriminant_map`,
`rootOrientationCover_eq_coefficientOrientationCover`,
`integralCoefficientCoverEquiv`, `integralCoefficientCover_card`.

[ArithmeticDiscriminantCover.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/ArithmeticDiscriminantCover.lean):
`integralCoefficientDiscriminant_eq_discr`,
`discriminant_quadraticChar_eq_orientationWeight`,
`arithmeticDiscriminantCover_eq_coefficientOrientationCover`,
`arithmeticDiscriminantCover_card`, `arithmeticDiscriminantCover_card_low`,
`arithmeticDiscriminantCover_card_signed`,
`sum_discriminant_quadraticChar_eq_zero`.

Direct checks and 24 transitive axiom audits use only `propext`,
`Classical.choice`, `Quot.sound`.

## Exact scope

This constructs and counts an integral coefficient family. The
[cross-resultant comparison](riac-discriminant-cover-signed-counts.md)
identifies its actual fibres with the separate factor-trace cover and
recovers polynomial Möbius signs. No realization of the integer conductor
cutoff, or bound on
`Σ_p index_p(N)=1−M(N)`, follows. The governing target remains
`Oε(N^(1/2+ε))` signed cancellation. No novelty claim is made for the classical
finite-field count.
