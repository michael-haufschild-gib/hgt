# Selberg multiple-twist Gamma geometry

New disjoint Lean module `formal/GaloisForLFunctions/SelbergClass/MultipleStandardTwistGammaGeometry.lean` establishes unconditional geometry of an affine reciprocal-Gamma denominator, without a continuation or residue claim.

- `exists_affine_eq_of_ne_zero`: any nonzero `L : (Fin N → ℂ) →L[ℂ] ℂ` reaches arbitrary `w` after affine shift `b`.
- Specialization at `1` proves `reciprocalGammaAffineEntire_ne_zero_of_linear_ne_zero`.
- `gammaCandidateHyperplane` and `gammaCandidatePolarSet`; polar set equals union and every hyperplane is nonempty for nonzero L.
- exact reciprocal-Gamma zero/nonzero loci and gamma-cleared presentation candidate-polar/regular set identities.

Verification: source `lake env lean` passed; exact module build passed; substantive theorem axiom audit only `[propext, Classical.choice, Quot.sound]`. Module imports GammaClearing and MeromorphicTensorAgreement. No umbrella edit or umbrella build.
