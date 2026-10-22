# Xi whole-corpus positive Sonin aperture collapse universality law

- **ID:** xi-whole-corpus-positive-sonin-aperture-collapse-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of whole-corpus Xi positive/failure phases and coupled
  Sonin positive-aperture nondegeneracy
- **Statement:** At every plain positive Sonin aperture, one relative determinant collar is
  exactly the complete Xi whole-corpus phase; quantifying over all positive apertures gives the
  same phase, and both pointwise and synchronized collar failures are exactly the complete
  whole-corpus failure phase.

## Goal

Eliminate the redundant proof-carrying nondegenerate-aperture interface from every whole-corpus
Xi/Sonin endpoint, not only from the local determinant theorem.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed warning-free
- [x] 3 → 4 novelty audit: completed; negative priority result

## Corpus inputs

- `riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate`
- `not_riemannHypothesis_iff_wholeCorpusFailurePhaseUniversalCertificate`
- `riemannHypothesis_iff_soninPositiveApertureRelativeDeterminant_unitCollar`
- `primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarPhase`
- `not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allSoninPositiveApertureUnitCollarFailurePhase`
- `primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis`

## Proof

**[PROVED HERE]** Fix all admissible parameters of the existing whole-corpus Xi certificate.
That certificate is equivalent to RH. For any `a : SoninPositiveAperture`, the positive-aperture
Sonin theorem identifies RH with the concrete relative-determinant collar at `a`; its
nondegeneracy witness is constructed internally from the prime-square residual. Transitivity
therefore identifies the complete whole-corpus certificate with the collar at every plain
positive aperture.

For the universal form, exact prime--archimedean source reconstruction is equivalent both to RH
and to collars at all positive Sonin apertures. Composing these equivalences with the whole-corpus
equivalence yields the all-positive-aperture classification.

The whole-corpus failure certificate is equivalent to `¬RH`. Applying logical negation to the
pointwise positive-aperture RH equivalence gives failure of the collar at any chosen positive
aperture. Applying negation to the reconstruction/RH equivalence and composing with the
synchronized positive-aperture failure theorem gives failure at every positive aperture. Thus
the pointwise and synchronized negative classifications hold with no proof-carrying aperture
subtype. No computation is used. ∎

## Strict gain over corpus endpoints

The whole-corpus theorem collapses to one nondegenerate coupled-Sonin aperture, but callers must
carry an explicit source-nondegeneracy proof. The later positive-aperture theorem removes that
proof only for local Sonin and reconstruction statements. Their closure removes the stale witness
from the full multi-family Xi phase and its negative phase, at one aperture and uniformly over
all apertures.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiWholeCorpusPositiveSoninApertureCollapseUniversalityLaw`
- Main theorem:
  `wholeCorpusPositivePhaseUniversalCertificate_iff_singlePositiveSoninAperture`
- Supporting theorems:
  `wholeCorpusPositivePhaseUniversalCertificate_iff_allPositiveSoninApertures`,
  `wholeCorpusFailurePhaseUniversalCertificate_iff_not_singlePositiveSoninAperture`, and
  `wholeCorpusFailurePhaseUniversalCertificate_iff_allPositiveSoninApertureFailures`.
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiWholeCorpusPositiveSoninApertureCollapseUniversalityLaw.lean`
- Result: passed warning-free.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Performed only after the dependency-closed Lean proof passed. Closest literature found treats
prolate operators and Sonin space in relation to the zeta zeros, or Hankel determinants in
orthogonal-polynomial and Dirichlet-series settings. No source located states the exact
positive-aperture relative-determinant collar equivalence with the complete multi-family Xi
certificate and its synchronized failure phase. This is a negative search result, not a priority
claim.

## Log

- 2026-07-23 — terminal theorem scan exposed the stale nondegenerate-aperture interface.
- 2026-07-23 — corpus research confirmed positive-aperture and whole-corpus collapses existed
  separately, with no proof-free whole-corpus connector.
- 2026-07-23 — dependency-closed proof completed before Lean source or literature search.
- 2026-07-23 — Lean source passed the required exact-file check warning-free and was wired into
  `GaloisForLFunctions/RHTower.lean`.
- 2026-07-23 — post-proof literature audit found Sonin/prolate and Hankel-determinant
  backgrounds, but not the proof-free whole-corpus aperture collapse.
