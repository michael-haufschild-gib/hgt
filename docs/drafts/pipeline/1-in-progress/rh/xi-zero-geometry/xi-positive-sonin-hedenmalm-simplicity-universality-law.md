# Xi positive-Sonin Hedenmalm simplicity universality law

- **ID:** xi-positive-sonin-hedenmalm-simplicity-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of the intrinsic positive-aperture determinant
  classification and the terminal Hedenmalm RH-simplicity classification
- **Statement:** At any plain positive Sonin aperture, its concrete determinant collar together
  with Xi simplicity is exactly the full Hedenmalm RH-simplicity certificate; equivalently this
  holds simultaneously at every positive aperture, with exact pointwise and synchronized failure
  duals.

## Goal

Remove the proof-carrying source-nondegeneracy artifact from the existing
Sonin--Hedenmalm interface. The resulting law is indexed by the intrinsic geometric domain
`a > 0`, not by an aperture bundled with a separate analytic nonvanishing proof.

## Gates

- [x] 0 → 1 in-progress: fresh terminal-pair scan exposed the shared RH carrier
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar`
- `primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis`
- `primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarPhase`
- `riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate`
- `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`
- `not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarFailurePhase`

## Proof

**[PROVED HERE]** Fix a plain positive aperture `a`. The positive-aperture determinant theorem
identifies its unit-collar envelope with RH; nondegeneracy is discharged internally by the
explicit prime-square residual. Conjoining this equivalence with `XiZerosSimple` and composing
with the Hedenmalm theorem gives the pointwise positive law. Replacing `XiZerosSimple` by its
eight-chart simplicity certificate yields the certificate-only form.

For the simultaneous form, exact prime--archimedean Hilbert reconstruction is equivalent both to
RH and to determinant collars at every positive aperture. Transitivity therefore identifies the
all-aperture phase with RH; conjoin simplicity and compose with the same Hedenmalm theorem.

Negating the pointwise equivalence and distributing failure over the conjunction gives: the full
Hedenmalm certificate fails exactly when the chosen positive-aperture collar fails or Xi has a
multiple zero. For synchronized failure, the existing theorem identifies non-RH with collar
failure at every positive aperture, so the same disjunction gives the all-aperture failure law.
No converse, compactness, or aperture witness choice remains open. ∎

## Strict gain over corpus endpoints

The earlier Sonin--Hedenmalm law accepts only `SoninCoupledNondegenerateAperture`, making callers
supply a proof-carrying nonzero source. The positive-aperture theorem later proved that
nondegeneracy is automatic, but no endpoint transports the entire RH-plus-simplicity and failure
classification across that equivalence. This law closes that interface pointwise and over the
whole positive aperture family.

## Lean formalization

- Main theorem:
  `soninPositiveApertureRelativeDeterminant_unitCollar_and_xiZerosSimple_iff_hendenmalmUniversalCertificate`
- Intrinsic family bridges:
  `riemannHypothesis_iff_allSoninPositiveApertureUnitCollarPhase` and
  `not_riemannHypothesis_iff_allSoninPositiveApertureUnitCollarFailurePhase`
- Companion laws: certificate-only pointwise and simultaneous positive forms, plus pointwise and
  synchronized failure forms with both raw simplicity and the eight-chart certificate
- Module:
  `GaloisForLFunctions.RHTower.XiPositiveSoninHedenmalmSimplicityUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/XiPositiveSoninHedenmalmSimplicityUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof arXiv searches found nearby work on complete/minimal systems in de Branges Sonine
spaces, spectral interpretations of zeta zeros, and Hilbert--Pólya operator models. No result
states the exact intrinsic positive-aperture Fredholm-collar equivalence with the enlarged
Hedenmalm RH-plus-simple-zero certificate, nor its synchronized all-aperture failure dual.
Novelty remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — fresh post-Law-421 terminal scan exposed the positive-aperture/Hedenmalm component.
- 2026-07-23 — full provider read separated a genuine domain repair from the already-saturated
  proof-carrying nondegenerate-aperture theorem.
- 2026-07-23 — dependency-closed pointwise, simultaneous, and failure proofs completed before
  Lean source or literature search.
- 2026-07-23 — exact-file Lean verification passed; eight interface laws wired into the RHTower
  umbrella.
- 2026-07-23 — post-proof literature audit found nearby Sonine and spectral-zero work but no exact
  collision.
