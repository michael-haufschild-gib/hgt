# Arbitrary reciprocal-observation Toeplitz and prefix core

- **ID:** projective-horizon-observation-matroid-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Classification:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper theorem:** `../../2-fully-proven/not_new_scientific_knowledge/projective-horizon-catalan-observation-matroid.md`
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonObservationMatroid.lean`

## Certified theorem surface

For arbitrary ordered finite row and column indices, Lean proves that the infinitesimal reciprocal
Jacobian of `Y=X^(-1)` is exactly the negative lower-Toeplitz section of the coefficient sequence of
`Y^2`:

```text
arbitraryReciprocalJacobian_apply
arbitraryReciprocalJacobian_eq_neg_toeplitz
```

For equally sized packets of missing-raw and observed-reciprocal indices, Lean defines the prefix
count and latent-information height and proves:

```text
indexedObservationPrefixCount_le_of_componentwise
indexedObservationHeight_nonnegative_of_componentwise
indexedObservationHeight_terminal
```

Thus componentwise dominance of the ordered packets forces nonnegative height at every static
resolution prefix, and every complete packet returns to height zero.  The four local observation
states and their exact height changes are certified by:

```text
ReciprocalObservationStep
reciprocalObservationStep
ReciprocalObservationStep.heightChange
reciprocalObservationStep_heightChange
```

## Formalization boundary

This module certifies the source-specific arbitrary-cut differential and the forward prefix law.
It does not reproduce the classical algebraic-matroid, skew-Schur, Catalan enumeration, or converse
order-statistic theories in Lean.  Those claims are proved on paper and identified there as parent
theory; expanding them would not increase the novel theorem surface.

## Verification

- Targeted direct compilation of `ProjectiveHorizonObservationMatroid.lean`: PASS.
- Targeted `.olean` generation: PASS.
- Scratch `#print axioms` audit: only standard `propext`, `Classical.choice`, and `Quot.sound` on
  the algebraic/counting theorems; the four-state height theorem is axiom-free.
- No full project build was run.

## RH impact audit

The formal theorems apply to every reciprocal finite jet, including zeta-derived jets, but contain
no zero-location, critical-line, Euler-product, or positivity input.  They provide no direct RH
implication.  A useful RH transfer would require a source-pure arithmetic marking on the observation
matroid.
