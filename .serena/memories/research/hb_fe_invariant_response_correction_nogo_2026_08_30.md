# HB FE-invariant response correction no-go (2026-08-30)

Formalized `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFEInvariantResponseCorrectionNoGo` and card `docs/drafts/pipeline/3-formalized/hb-fe-invariant-response-correction-no-go.md`.

Core theorem: for any scalar correction K on `XiZeroCopy` satisfying K(reflect q)=K(q), exact response-corrected reflected BM current factors as K(q) times literal unsquared-source current. Therefore corrected current vanishes iff K(q)=0 or Re(q)=1/2. Everywhere-nonzero FE-invariant correction preserves exact critical-wall locus; universal cancellation iff RH. Premise-free route certificate: `d4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled`.

Positive survivor: existing division-free cross-pair correction cancels unconditionally but must break FE invariance at every off-critical fibre. Global FE invariance of that correction iff RH (`d4BMXiSecondHarmonicCrossPairResponseCorrection_feInvariant_iff_rh`). Remaining HB compensator must transport reflected-copy orientation data or leave scalar-response form; regularity/nonsingularity alone is insufficient.

Verification: source `lake env lean` PASS; targeted module build PASS; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint remains red only due unrelated shared-tree modules missing umbrellas.

Failed pivots before this result: compact Hardy producer no-go was invalid without bounded preimages and false RH need not give infinitely many off-wall nodes; L2 eigenstate route invalid because nonlinear source is inhomogeneous and Xi singularities are resonances rather than ordinary L2 residual eigenstates.