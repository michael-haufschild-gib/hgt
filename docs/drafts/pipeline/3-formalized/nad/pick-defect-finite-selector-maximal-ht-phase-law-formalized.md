# Pick-defect finite-selector maximal-HT phase law — formalized

- **ID:** `pick-defect-finite-selector-maximal-ht-phase-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `pick-defect-finite-selector-maximal-ht-phase-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/LocalNevanlinnaJetTriangular.lean` | the triangular jet maps of the positive/free Nevanlinna chart |
| `HTGeometry/ProjectiveNevanlinnaGenericity.lean` | polynomial-defect avoidance and the residual relation-free phase |
| `HTGeometry/NevanlinnaNoncriticalProjectiveCompactPatch.lean` | the noncritical projective compact patch |
| `HTGeometry/NevanlinnaPositiveCarrierCapstone.lean` | the positive-carrier capstone |
| `HTGeometry/MomentFiberPickSchurPhase.lean` | `FinitePickDefectPhaseInput`, the exclusive dichotomy, and the forcing of every selector excluding the free maximal-translation phase onto the singular, jet-deficient locus |
| `HTGeometry/CompleteCauchyGermClosure.lean` | the arbitrary-node complete-germ closure |
| `HTGeometry/StieltjesTransformPick.lean` | **`stieltjesTransform_im_nonneg`**, **`stieltjesTransform_im_pos`**, **`stieltjesTransform_differentiableOn`**, `stieltjesTransform_norm_le`, and the Poisson / conjugate-Poisson representations — every representing measure's Cauchy transform is a genuine Pick (Herglotz/Nevanlinna) function, equation `(6)` |

## Audited declarations

`HTGeometry.stieltjesTransform_im_pos`, `HTGeometry.stieltjesTransform_differentiableOn` and the
capstones of the other modules resolve and `#print axioms` reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Verification

```text
lake build GaloisForLFunctions.HTGeometry
```

## Boundary

The classical confluent Nevanlinna--Pick singular/free dichotomy and its `J`-inner transfer-matrix
parametrization `(8)`--`(9)` enter as the explicit `FinitePickDefectPhaseInput`, exactly as the
card's gate line records ("complete Lean theorem surface from explicit confluent-Pick input").  They
are not postulated as axioms.  The card's remaining gates are the independent specialist proof audit
and the primary-source audit for the confluent theorem in this normalization — both external.
