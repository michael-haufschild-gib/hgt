# The logarithmic and Weil form domains agree

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Finite positive logarithmic Fourier energy is exactly admission to the complete archimedean weighted-L² domain. Every supported finite-energy test therefore satisfies the actual Weil Riesz equation with its full logarithmic forcing.

## Proof

The exact Gamma weight differs from `1+(1/2)log(1+ξ²)` by a scalar minus
the Fourier transform of an L¹ kernel. This correction is bounded, so its
product with the squared Fourier transform of any L² source is integrable.
The two energy conditions are equivalent. Existing complete aperture admission
then gives the actual form vector. Their mixed forms coincide pointwise on
Fourier representatives, and Hermitian symmetry gives the equation with tests
in the first argument. Reflection preserves the domain and form because the
reference weight is even.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicAndWeilFormDomainsAgree.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `hasLogarithmicEnergy_iff_ccm_memLp`
- `exists_ccm_form_of_logarithmicEnergy`
- `logarithmicFullForm_ccm_embedding`
- `hasLogarithmicEnergy_reflection`
- `logarithmicFullForm_reflection`
- `WeilHilbertBeforeContact.evalVector_logarithmic_fullForm`

Transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`.
Production plain audit passed. Umbrella imports the module.
