# Formalization certificate: theta compact source-entropy boundary weld

- **ID:** `theta-compact-source-entropy-boundary-weld-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `theta-compact-source-entropy-boundary-weld.md`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/HedenmalmThetaCompactFluxEnergy.lean
formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceEntropyBoundaryWeld.lean
```

Namespace `RHTower`; reachable from `GaloisForLFunctions.RHTower`.

## Formal theorem chain

| # | card statement | Lean declaration |
|---|---|---|
| `S_q = 2 Im(z_q)` | reflected prime-source entropy is twice the transverse coordinate | `riemannReflectedSourceEntropy_xiZeroCopy_eq_two_spectralIm` |
| `F_q = M E_q S_q` | **the signed compact/source weld** | `thetaXiRankTwoBoundaryFlux_eq_sourceEntropy` |
| — | the weld is faithful before squaring | `thetaXiRankTwoBoundaryFlux_eq_zero_iff_sourceEntropy_eq_zero`, `thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero` |
| — | the normalized square is the source-entropy density term | `thetaXiNormalizedRankTwoBoundaryFluxTerm_eq_sourceEntropyDensity` |
| — | the two global energies agree | `thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_sourceEntropyOrientationEnergy` |
| — | **unsquared compact-boundary RH criterion** | `all_thetaXiRankTwoBoundaryFlux_eq_zero_iff_riemannHypothesis` |
| — | the same weld at global energy level | `thetaXiNormalizedRankTwoBoundaryFluxEnergy_eq_zero_iff_sourceEntropy_and_rh` |

Positivity of `thetaSource.mass` and of `thetaXiRootEnergy` is what makes the *signed* statement
survive; the sign is retained until the final squared density, as the card requires.

## Verification

```bash
cd formal
lake build GaloisForLFunctions.RHTower.HedenmalmThetaSourceEntropyBoundaryWeld
```

Clean.  `#print axioms` on every declaration in the table reports only `propext`,
`Classical.choice` and `Quot.sound`.
