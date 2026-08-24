# Enhanced epigraph foundation (2026-08-24)

- Honest frontier/dependency audit: `docs/reports/irregular-microlocal-rh-foundations.md` (ignored by git via `docs/reports/`). Current corpus has a finite cellular Stokes/microlocal shadow, not full irregular Riemann–Hilbert theory.
- New module: `formal/GaloisForLFunctions/HTGeometry/StokesEnhancedEpigraphConvolution.lean`, imported by `formal/GaloisForLFunctions/HTGeometry.lean`.
- Exact declarations: exponential epigraph/on-domain supports; fiberwise additive convolution; commutativity, associativity, zero-section units; domain-intersection phase-addition law; zero-phase idempotence; phase-order iff/injectivity/order embedding; continuous epigraph closedness and open-domain local closedness.
- Verification passed: direct `lake env lean GaloisForLFunctions/HTGeometry/StokesEnhancedEpigraphConvolution.lean`; targeted `lake build GaloisForLFunctions.HTGeometry.StokesEnhancedEpigraphConvolution`; `#print axioms` for every new theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
- Four Stage-2 cards live under `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/irregular-rh-foundations/`. They remain Stage 2 because one repo lint run found unrelated pre-existing unreachable modules; do not rerun unchanged lint or fix unrelated dirty files.
- Scratch files were removed.
- Next load-bearing layer: determine/construct sheaf-level constant-extension-by-zero and additive convolution over existing mathlib/Deninger APIs; if absent, add subanalytic/bordered-site infrastructure before enhanced quotient/ind-derived categories.
- No RH proof. No sheaf-level irregular RH correspondence yet.