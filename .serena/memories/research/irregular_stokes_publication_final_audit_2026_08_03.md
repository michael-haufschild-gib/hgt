# Irregular/Stokes publication final audit — 2026-08-03

Route: Airy-tower zero-loop Stokes rigidity, extending `mem:research/irregular_stokes_universal_contact_covariance_2026_08_03`.

## Final mathematical package

Publication-ready manuscript proves: universal tangent formal-contact covariance; exact negative Airy Fourier coordinate and rank-one resolution; strict contact tomography and additive strict-negative-type energy tree; first-deviation sign law; zero-loop classification by divisor chains/ordered factorizations; exact elementary pair spectra; decorated finite fibres; necessary-and-sufficient arbitrary-size elementary Stokes–Cartan recognition with simultaneous finite Puiseux reconstruction and cubic unit-cost query bound.

Strongest theorem: elementary recognition from exact local pair spectrum plus rescaled acute-isosceles/ultrametric condition, with actual finite complex Puiseux polynomials, elementary-support proof, highest pairwise-difference witness, and direct edge recovery.

## Current literature boundary

Fresh primary-source audit added Hien–Sabbah (local Laplace transform), Mochizuki (Stokes shells/Fourier transforms), and Douçot–Hohl (topological Fourier algorithm for Stokes matrices). These reconstruct analytic transformed filtrations/matrices; no collision located with formal contact covariance, zero-loop arithmetic, exact pair spectra, finite fibres, or elementary recognition. Existing relevant comparisons include Hiroe, Boalch–Douçot–Rembado, Douçot 2025 graphs, Douçot 2026 enriched trees, and Douçot 2026 Fourier/Argyres–Douglas.

## Verification

Eight source modules passed sequential foreground `lake env lean <file>` checks from `formal/`: StokesPuiseuxSourceLaw, StokesPairPuiseuxSourceLaw, AiryTowerStokesRigidity, StokesUniversalContactLaw, StokesNegativeFourierResolution, ElementaryStokesGlobalPuiseuxRealization, ElementaryStokesRecognitionComplexity, StokesSignedDecoratedFiniteFiber.

Six targeted final `lake build <module>` audits passed: StokesPairPuiseuxSourceLaw, AiryTowerStokesRigidity, StokesUniversalContactLaw, StokesNegativeFourierResolution, ElementaryStokesRecognitionComplexity, StokesSignedDecoratedFiniteFiber. No full build run.

`/tmp/hgt_stokes_final_axioms.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` on all principal capstones. Relevant-source forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

Repository-wide `scripts/formal_tools.py lint` reports no Stokes error, but global exit remains nonzero because unrelated RHTower modules and `HTGeometry.TwoRecordResolvedConnection` are unwired. Do not claim global green lint.

## Artifacts

- Source: `docs/drafts/manuscripts/airy-tower-stokes-rigidity/main.tex`
- Final PDF: `output/pdf/airy-tower-stokes-rigidity.pdf`
- Claim trace: `docs/drafts/manuscripts/airy-tower-stokes-rigidity/CLAIM_TRACE.md`
- Literature audit: `docs/drafts/manuscripts/airy-tower-stokes-rigidity/LITERATURE_AUDIT.md`
- Hostile review: `docs/drafts/manuscripts/airy-tower-stokes-rigidity/HOSTILE_REVIEW.md`
- Stage-4 card: `docs/drafts/pipeline/4-publication-ready/airy-tower-zero-loop-stokes-rigidity.md`
- PDF SHA-256: `0e75a9848ff2195dfffcec539dab667fdc21a48d229012937102a08ae42108e2`

Tectonic compiled 17 A4 pages without warnings. Fresh rendering found and fixed two missing `\\qquad` backslashes. Every page was visually inspected; affected pages were re-rendered after final correction. Internal hostile review verdict: publishable at Compositio/IMRN/Advances range, subject to ordinary external peer review. This is internal review, not journal acceptance.
