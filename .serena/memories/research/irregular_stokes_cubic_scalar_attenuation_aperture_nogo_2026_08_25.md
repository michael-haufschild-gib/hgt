# Cubic scalar-attenuation aperture no-go (2026-08-25)

Formalized next Route-P irregular-RH obstruction motivated by factor-2000 raw magnitude gap.
- Exact survivor law: if a complex-linear landing maps radial generalized mode `z` to `alpha` times mode `w`, aperture covariance defect at radius zero equals `alpha * 2*c*exp(-w*c)*(exp(-z*c)-exp(-w*c))`.
- Closed no-go: for every strict-right Xi zero copy, primitive prime/depth label, and vertical clock, there are no nonzero complex scalar `alpha` and linear map commuting with all radial translations that send primitive Burnol cubic conormal to `alpha` times the Xi conormal.
- Proof normalizes map by `alpha⁻¹`, reducing to existing unscaled aperture-character no-go. No boundedness, continuity, locality, positivity, or lower bound on `|alpha|` is used.
- Design consequence: required magnitude contraction cannot be constant scalar damping or any aperture-translation intertwiner. Viable microlocal landing must be nonstationary and retain polar--Gamma boundary work.

Module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicScalarAttenuationApertureNoGo.lean`.
Card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-cubic-scalar-attenuation-aperture-no-go.md`.
Direct check and direct olean emission passed. Both public declarations have only `[propext, Classical.choice, Quot.sound]`. Scratch and emitted olean removed; no target/umbrella build.

Corpus had unscaled no-go and unscaled defect, not arbitrary scalar classification/scaled formula. Primary search found general irregular RH/Stokes connection maps only; absence is inference.

Frontier map acquired unrelated concurrent modifications during final checks. This task did not edit it; preserve as external/user state.