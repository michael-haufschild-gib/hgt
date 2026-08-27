# GTA Schur quartic spectral decay equivalence (2026-08-27)

## Result
Corpus-led GTA loop closed two unconditional Lean modules.

1. `GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticSpectralSplit`
   - `sourcePairPositiveQuarticCharge_le_normSq_sq`
   - `sourcePairPositiveQuarticCharge_le_normSq_mul_im_sq`
   - `finiteMatrixSchurPositiveQuarticSmallSpectrumCharge_le`
   - `finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le`
   - Dimension-free bound: if Schur nodes with `normSq > δ` satisfy `Im² ≤ η`, total charge is at most `2300*(δ+η)*matHSNormSq M`.

2. `GaloisForLFunctions.RHTower.HedenmalmThetaSchurQuarticSpectralDecayEquivalence`
   - Uniform HS ceiling for actual corrected theta stages.
   - Compact reciprocal zero-free window under RH.
   - `eventually_thetaSourceStageSchurDiagonal_im_sq_lt_of_rh` uniformly over every Schur packet.
   - `eventually_thetaSourceStageSchurPositiveQuarticCharge_lt_of_rh`.
   - Exact endpoint: `riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay`.

## Proof mechanism
Avoid labeled eigenvalue perturbation. Put all bounded nodes with `normSq ≥ δ` and `Im² ≥ η` in one compact spectral window. Inversion is continuous there. Under RH normalized Xi is zero-free on its compact inverse image; locally uniform determinant convergence makes late finite determinants zero-free there. Every nonzero Schur diagonal contributes its reciprocal determinant zero, contradiction. Combine transverse localization with dimension-free small/large spectral split.

## Verification
Both direct `lake env lean` checks and exact module builds pass. `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`. Global lint is blocked only by unrelated unwired concurrent module `GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution`.

## Pipeline
Cards moved to `docs/drafts/pipeline/2-fully-proven/finite-schur-quartic-spectral-split-tightness.md` and `.../theta-schur-quartic-spectral-decay-equivalence.md`. Novelty externally audited but remains UNVERIFIED.

## Open core
This equivalence is receiver classification, not RH proof: known RH-to-decay proof uses Xi zero-freeness. Live GTA burden is source-arithmetic derivation of cofinal charge smallness or transverse localization without Xi-zero input. Current approximation fibres, entrywise aggregation, and semidefinite cone approximation are terminal.