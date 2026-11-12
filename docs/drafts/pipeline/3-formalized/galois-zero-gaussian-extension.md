# Gaussian extension of the complete-fibre zero field

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Ordinary conjugation; functional-equation lifts; full Galois group.

The complete-fibre source construction and infinite normal extension `L/K`
are formalized in [the fibre-field theorem](../3-formalized/galois-zero-full-fibre-field.md).
Here `K⊆ℝ`, `L=ℚ(all w)`, and `w=(ρ−1/2)/i`. Every source automorphism preserves
the finite ordinate fibres and commutes with conjugation of `w`.

## Gaussian classification

Set `M=L(i)=ℚ(i, all ρ)`. Then:

1. `M/K` is normal; ordinary complex conjugation is central in `Gal(M/K)`.
2. Every original-zero orbit is finite, confined to the two ordinate fibres `±t`.
3. Functional-equation reflection `ρ↦1−ρ` lifts over `K` iff `i∉L`, equivalently
   iff `−1` is not a square in `L`. Its lift is unique.
4. If `i∈L`, then `M=L`. If `i∉L`, restriction and the action on `i` give
   `Gal(M/K) ≅ Gal(L/K) × C₂`; ordinary conjugation corresponds to `(c_L,−1)`.

## Proof

Both `L/K` and `K(i)/K` are normal, hence so is their compositum. Every
source automorphism preserves the centered fibre equations and sends `i` to
`±i`. It commutes with conjugation on every centered zero and on `i`, hence on
all of `M`. Original-zero images consequently remain in two finite fibres.

If `i∉L`, the quadratic conjugation of `L(i)/L` fixes every `w` and reverses
`i`, yielding the functional-equation lift. Conversely, a proposed lift fixing
`i` would send every `w` to `−w`, contradicting preservation of a nonzero
ordinate. Such an ordinate exists because the support is infinite and each
fibre finite. The lift must reverse `i` and fix every `w`; therefore it fixes
`L`, forcing `i∉L`. These generator values also give uniqueness.

When `i∉L`, each element has a unique expression `a+ib`, with `a,b∈L`.
The maps `a+ib ↦ σ(a)+ε i σ(b)` provide every pair of centered automorphism
and Gaussian sign. Restriction and sign are jointly injective because those
fields generate `M`. Their compatibility with composition gives the direct
product. The square-class formulation follows because a complex square root
of `−1` is `±i`.

## Lean

`formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheGaussianExtensionOfTheZeroField.lean`

- `gaussianZeroExtension_toSubfield`
- `gaussianZeroExtension_normal`, `gaussianZeroConjugation_central`
- `gaussian_original_zero_orbit_finite`, `gaussian_aut_preserves_original_zeros`
- `functional_equation_lift_iff`, `functional_equation_lift_iff_nonsquare`
- `functional_equation_lift_unique`
- `gaussianGaloisProduct`, `gaussian_conjugation_coordinates`
- `gaussianActionCoordinates_surjective_iff`, `gaussian_extension_dichotomy`

Final source audit passed. All twelve principal dependency closures contain
only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

The theorem determines when reflection extends; it does not decide whether
`i∈L` for the actual zeros. Central conjugation alone does not imply RH.
The remaining finite-fibre permutation image is addressed separately in
[the centralizer candidate](../1-in-progress/galois-zero-fibre-centralizers.md).
