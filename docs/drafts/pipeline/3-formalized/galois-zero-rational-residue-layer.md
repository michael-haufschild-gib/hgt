# The rational-real-part residue layer

- **ID:** galois-zero-rational-residue-layer
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Questions:** Arithmetic location of conjugation; quadratic residue extensions; infinite descent.

## Theorems

Let `E_rat` be the subextension of the prime spectral field generated over
`B` by all prime values at actual zeros whose real parts are rational.
This differs from the rational-weight prime field: the exponents here are
nonreal zeros. It includes the entire critical-zero prime field.

Each individual residue field in this layer is quadratic over `B`. Their
full compositum `E_rat/B` is the multiquadratic extension specified by the
actual prime-coordinate discriminants. Its Galois group
is the sign group determined by all finite square-product relations, with
the Krull topology. Complex conjugation is the uniform negative sign,
central on this entire layer. Restriction from `Gal(E/B)` is continuous and
surjective.

## Paper argument

Rational-orbit rigidity gives exactly the two conjugate zeros. Thus
`u=p^ρ+conjugate(p^ρ)` and `v=p^ρ*conjugate(p^ρ)` are fixed by every
arithmetic automorphism and belong to `B`. The rational-weight theorem
also gives `v=p^(2 Re ρ)∈B` directly. A nonreal prime coordinate exists
among any two distinct primes, generates the full residue field, and
satisfies `X²−uX+v`; since `B` is real, its degree is exactly two.

For each nonreal coordinate set `d=p^ρ−conjugate(p^ρ)` and
`D=d²=u²−4v∈B`. Then `D<0` in the chosen real embedding. These radicals
generate the whole layer. Its exact sign group consists of sign assignments
respecting every finite product of the `D` that is square in `B`.
An odd product is negative and cannot be a square. Thus uniform negative
signs satisfy all relations and give ordinary complex conjugation.

This is an infinite compositum over all eligible actual zeros and all
primes. No finite height or bounded prime set defines the layer.

## Boundary

This does not assert that all real parts are rational, that the layer equals
the full spectral field, or that conjugation is central on the remaining
extension.

## Lean

`formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheRationalResidueLayerOfTheZeros.lean`

- `rationalPrimeResidueField_degree_two`
- `criticalPrimeResidueField_le_rationalLayer`
- `rationalZeroResidueRestriction_surjective`
- `rationalPrimeRadicand_negative`
- `rationalPrimeRadicals_adjoin_top`
- `rationalResidueSignAction_unique_extension`
- `rationalResidueSignHomeomorph`
- `rationalPrimeRadicands_square_even`
- `rationalResidueConjugation_unique`
- `rationalResidueConjugation_central`
- `rationalPrimeNorm_coe`

Direct source check passed. All 28 axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.
