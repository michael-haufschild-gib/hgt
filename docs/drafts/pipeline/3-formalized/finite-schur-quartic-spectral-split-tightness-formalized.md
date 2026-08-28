# Finite Schur quartic spectral split tightness — Lean certificate

- **ID:** `GTA-PQ4-SC1-formalized`
- **Stage:** 3-formalized
- **Paper card:** `finite-schur-quartic-spectral-split-tightness.md`
- **Module:** `GaloisForLFunctions.HTGeometry.FiniteMatrixSchurPositiveQuarticSpectralSplit`

## Exact certified surface

`finiteMatrixSchurPositiveQuarticCharge_le_of_large_im_sq_le` proves the card's literal,
dimension-free `2300 * (δ + η) * matHSNormSq M` bound for every finite Schur packet. The supporting
small-spectrum estimate is `finiteMatrixSchurPositiveQuarticSmallSpectrumCharge_le`. No normality,
dimension bound, eigenvalue labeling, or additional source premise is introduced.

## Verification

On 2026-08-28, direct `lake env lean` elaboration and targeted `lake build` of the named module
completed successfully. The card records its earlier axiom audit as exactly `propext`,
`Classical.choice`, and `Quot.sound`; it was not redundantly rerun.

