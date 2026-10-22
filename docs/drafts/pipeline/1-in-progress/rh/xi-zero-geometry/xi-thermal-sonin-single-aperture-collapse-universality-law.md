# Xi thermal–Sonin single-aperture collapse universality law

Status: paper proof complete; Lean source complete; exact audit deferred until terminal parent modules
receive final module builds.

## Lean sources

- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSoninEndpointCertificate`
- `riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one`
- `riemannHypothesis_iff_soninCoupledRelativeDeterminant_unitCollar`

## Survivor

Under any admissible rectangular source window, the complete endpoint certificate—thirty-one
thermal/Hausdorff/Bernstein/KMS/resolvent/projective/Born–Witten charts plus determinant collars for
every nondegenerate coupled-Sonin aperture—is exactly RH. More sharply, any single nondegenerate
Sonin aperture collar detects that entire simultaneous certificate.

Existing terminal capstones separately identify source abscissa with the enlarged certificate and
RH with one aperture collar. Their composition collapses the full all-aperture certificate to each
single aperture.

## Proof skeleton

Transport RH through the rectangular source abscissa equivalence and then through the enlarged
thermal–Sonin certificate equivalence. Reverse that result and compose it with the aperturewise
relative-determinant RH equivalence.

## Novelty audit

Pending post-formalization literature search.
