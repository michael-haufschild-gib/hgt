# Gamma three-chart lower-jet extension universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `gammaPoleScaleAndFinitePartJetRationalEval_injective` proves cancellation-free evaluation of
  the factorial scale and finite-part jets over the moving-center field.
- `gammaPoleScaleAndCovariantResidueRationalEval_injective` proves the same for covariant residues.
- `gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective` proves the same for normalized
  inverse-branch coefficients.
- `GammaInverseBranchLowerJetRing` is the corpus coefficient ring obtained by adjoining an
  arbitrary formal lower-depth jet frame to the pole-index germ ring.
- The existing three-chart atlas proves pairwise coordinate interchangeability before adjoining
  the lower-depth frame; the lower-jet freeness module treats only the inverse-branch family over
  `ℂ`.

No corpus theorem states that all three moving-center charts remain cancellation-free after the
same arbitrary lower-jet extension.

## Universal law

For every type `kappa` of formal lower-depth jets, extend each Gamma pole evaluation coefficientwise
through `MvPolynomial kappa`.  The finite-part, covariant-residue, and inverse-branch evaluations
are all injective into `GammaInverseBranchLowerJetRing kappa`.  Consequently every nonzero mixed
polynomial in lower-depth jets and arbitrary moving-center chart coefficients survives in every
one of the three coordinate systems.

## Paper proof

Polynomial extension of scalars by a fixed variable family preserves an injective coefficient ring
homomorphism.  Apply `MvPolynomial.map_injective` separately to the three source evaluation maps.
For the evaluation form, if one extended evaluation of a nonzero polynomial vanished, injectivity
would identify that polynomial with zero.  Conjoin the three contradictions.

No numerical computation is used; proof is symbolic because task forbids computations.

## Lean formalization

The theorem is appended to
`GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw` so it reuses the
existing three-chart maps without another unbuilt-module import.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
