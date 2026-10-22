# Formalization certificate: theta compact boundary-flux energy

- **ID:** `theta-compact-boundary-flux-energy-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `theta-compact-boundary-flux-energy.md`

## Lean module

```text
formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaCompactFluxEnergy.lean
```

Namespace `RHTower`; reachable from `GaloisForLFunctions.RHTower`.

## Formal theorem chain

| # | card statement | Lean declaration |
|---|---|---|
| — | the abstract compact divisor vector is a.e. `sqrt(M) rootG` | `thetaDivisorEigenvector_ae_rootG` |
| — | its monopole is one, its centered dipole is `-∫ rootH` | `pinnedMean_thetaDivisorEigenvector`, `pinnedCentered_thetaDivisorEigenvector` |
| — | the rank-two boundary form on the genuine eigenvector | `inner_pinnedBoundaryCLM_thetaDivisorEigenvector` |
| — | `E_q > 0` at every divisor copy | `thetaXiRootEnergy_pos` |
| `F_q = 2 M Im(z) E_q` | **the boundary flux law** | `thetaXiRankTwoBoundaryFlux_eq` |
| — | the same flux from the root primitive | `thetaXiRootFlux_eq`, `thetaXiRankTwoBoundaryFlux_eq_rootFlux` |
| — | eigenmode and flux law in one statement | `thetaXiRankTwoBoundaryFlux_eigenmode` |
| — | `Im(z^{-2}) = -2 Re(z) Im(z) / normSq(z)^2` | `xiZeroCopyReciprocalSquare_im_eq_spectral` |
| `(Re(z) F_q/(M E_q D_q^2))^2 = Im((z^{-1})^2)^2` | **the normalized observer identity** | `thetaXiNormalizedRankTwoBoundaryFluxTerm_eq` (and `thetaXiNormalizedRootFluxTerm_eq` for the root form) |
| summability | | `summable_thetaXiNormalizedRankTwoBoundaryFluxTerm`, `summable_thetaXiNormalizedRootFluxTerm` |
| equals `xiThermalOrientationEnergy` | | `thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_thermalOrientationEnergy`, `thetaXiNormalizedRootFluxEnergy_eq_thermalOrientationEnergy` |
| vanishes exactly under RH | | `thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_zero_iff_riemannHypothesis`, `thetaXiNormalizedRootFluxEnergy_eq_zero_iff_riemannHypothesis` |

Denominators are discharged by `thetaSource.mass_ne_zero`, `thetaXiRootEnergy_pos` and
`xiSpectralPoint_ne_zero`, exactly as the card's hostile audit requires; no RH premise enters.

## Verification

```bash
cd formal
lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaCompactFluxEnergy
```

Clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.
