# Irregular Stokes universal contact covariance — publication closure (2026-08-03)

## Mathematical result
Universal law: every tangent formal reparametrization t ↦ t u(t), u(0)=1, preserves Laurent order of every difference f-g, hence preserves all threshold contact relations and the full contact hierarchy. Negative Airy Fourier reciprocal coordinate is exactly such a reparametrization, so coarea/contact/energy/Fourier phenomena are consequences; zero-loop gcd/sign/spectral arithmetic is collateral rigidity.

Key production theorems:
- FormalUniformizer.laurentAlgReparametrization_order
- FormalUniformizer.laurentAlgReparametrization_contactTop
- FormalUniformizer.laurentContactHierarchy_reparametrization
- Characteristic.airyTower_negativeFourier_contact_transport
- Characteristic.airyTower_exact_negativeFourier_resolution
- CertifiedFissionDatum.universal_contact_master_law

## Semantic closure
formal/GaloisForLFunctions/HTGeometry/ElementaryStokesGlobalPuiseuxRealization.lean:
- StageRealizesEdge
- pairPresentation_hasUncancelledHighestDifferenceStage (all 9 constructors)
- HighestDifferenceRealizesEdge
- stageRealizesEdge_gives_highestDifferenceRelation
- elementary support predicates and exact collected-polynomial support theorem
- globalPuiseux_realization_of_certificate now returns actual elementary Puiseux polynomials plus actual highest exponent and stage-free recovery of B_ij.

formal/GaloisForLFunctions/HTGeometry/ElementaryStokesRecognitionComplexity.lean:
- recognition capstone inherits actual polynomial semantics and stage-free exact edge reconstruction.

formal/GaloisForLFunctions/HTGeometry/StokesSignedDecoratedFiniteFiber.lean:
- signed diagonal decorations over ℤ, nonnegative off-diagonal edge
- exact signed localWeight
- finite compatible fission-tree fibre via injection to natural encoding
- negative local weight gives empty fibre.
Imported by formal/GaloisForLFunctions/HTGeometry.lean.

## Verification
Direct lake env lean and targeted lake build passed for:
- ElementaryStokesGlobalPuiseuxRealization
- ElementaryStokesRecognitionComplexity
- StokesSignedDecoratedFiniteFiber
and prior relevant Stokes modules.
Axiom audit: only propext, Classical.choice, Quot.sound. No project axiom/sorry/admit/opaque/unsafe.
Authoritative global lint is not globally green solely because unrelated concurrent RHTower modules are not reachable from their umbrella; no Stokes lint failure.

## Paper
Source: docs/drafts/manuscripts/airy-tower-stokes-rigidity/main.tex
Final artifact: output/pdf/airy-tower-stokes-rigidity.pdf
SHA256: 71b467c440dab61d37d7722a2ed24ec27ba13ad13955d56f5f5175006d057aed
17 pages, A4, no TeX warnings, all pages visually inspected.
Paper contains no mention of Lean, proof assistants, formal verification, toolchain, or declaration names. Lean stays internal.
Trace: docs/drafts/manuscripts/airy-tower-stokes-rigidity/CLAIM_TRACE.md
Literature audit: docs/drafts/manuscripts/airy-tower-stokes-rigidity/LITERATURE_AUDIT.md
Hostile review: docs/drafts/manuscripts/airy-tower-stokes-rigidity/HOSTILE_REVIEW.md
Internal hostile review passes Compositio/IMRN/Advances-level general-journal bar; external peer review remains.
Publication card: docs/drafts/pipeline/4-publication-ready/airy-tower-zero-loop-stokes-rigidity.md
Fourier source card: docs/drafts/pipeline/4-publication-ready/airy-negative-local-fourier-source.md

## Process
No commit/push. Shared worktree has unrelated concurrent changes; preserve them.