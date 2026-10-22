# Theta Schur quartic spectral decay equivalence — Lean certificate

- **ID:** `GTA-PQ4-SC2-formalized`
- **Stage:** 3-formalized
- **Paper card:** `theta-schur-quartic-spectral-decay-equivalence.md`
- **Module:** `GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSchurQuarticSpectralDecayEquivalence`

## Exact certified surface

`riemannHypothesis_iff_thetaSourceSchurPositiveQuarticChargeUniformDecay` is the card's exact
equivalence: RH holds iff positive quartic charge tends uniformly to zero across every Schur packet
of every sufficiently late actual corrected theta stage. The module also closes the compact
reciprocal-window localization and dimension-free decay bridge used in the forward direction.

## Verification

On 2026-08-28, direct `lake env lean` elaboration and targeted `lake build` of the named module
completed successfully. The card's earlier standard-only axiom audit was retained without repeat.

