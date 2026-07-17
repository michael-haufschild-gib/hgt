# Thermal CFT Gamma responses are hypertranscendental off the half-integral weight lattice

- **ID:** `thermal-cft-gamma-response-differential-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** A. Manenti, *Thermal CFTs in momentum space*, arXiv:1905.01355, equations (7.7)--(7.9)
- **Statement:** The complete frequency-dependent thermal CFT response, including its elementary exponential readout, and its Wigner--Smith logarithmic current are DA exactly when `1-2h` is integral and HT otherwise; an HT finite multi-sector product must contain a non-half-integral weight.

## Goal

Classify an actual finite-temperature quantum-field-theory response, also identified by the source as the holographic AdS black-hole phase, using the reflected-Gamma observability structure.  The selector should be the conformal weight lattice rather than temporal evolution.

## Gates

- [x] 0 → 1  in-progress: exact primary-source formula, corpus-first check, and reduction to existing reflection plus Veneziano theorems
- [x] 1 → 2  fully-proven: exact classification, exceptional sector, and source localization complete
- [x] 2 → 3  formalized: exact target, direct file, and standard-only axiom audit pass
- [ ] 3 → 4  publication-ready: standalone exposition

## Exact physics relation

For the light-cone Fourier transform in equation (7.8), the non-elementary frequency dependence is

`Gamma(h + i*kappa/(2*pi)) Gamma(h - i*kappa/(2*pi))`.

With `z = i*kappa/(2*pi)`, Euler reflection gives

`Gamma(h+z) Gamma(h-z) = gauge_h(z) * Gamma(h+z)/Gamma(1-h+z)`.

The ratio separation is `1-2h`.  The existing translated-Gamma classifier is therefore exact.
This symmetric law is now a direct specialization of the asymmetric parent theorem
`differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSeparation` at `a=b=h`.

The Gamma core is even under `kappa ↦ -kappa`, while the oriented exponential readout gives

`H(-kappa) = exp(-kappa) H(kappa)`.

Thus exact KMS detailed balance is the elementary orientation gauge of the same HT observable; the
Gamma source survives in either orientation but cancels from their ratio.

The same value function now has a second primary-source interpretation: under
`kappa=2*pi*xi` it is exactly the Gamma--Boltzmann core of the relativistic beta-decay Fermi
function.  `FermiCoulombGammaCore.lean` proves the calibration and its charge-reversal law.

## Positive exceptional statement

At `h=1/2`, the Gamma product is exactly the Euler reflection gauge; this explains the source's elementary `cosh` expression in equation (7.9).  More generally all half-integral/integral weights are DA, while generic weights are HT.

The meromorphic exponential factor satisfies `E_lambda' = lambda E_lambda`, so it is DA and
nonzero.  Restoring the exact `exp(±kappa/2)` readout from equation (7.8) therefore leaves the
weight boundary unchanged.  The finite-product source theorem localizes any HT multi-sector
response, including these exponential-dressed factors: at least one sector must have nonintegral
`1-2h`.  This is one-way only; HT factors may still cancel in a product.

Passing to the observable logarithmic response current preserves this selector exactly.  Restoring
the exponential readout adds the constant `lambda` to the Gamma current.  The Wigner--Smith current
is therefore DA precisely on the same integral `1-2h` lattice and HT everywhere else.

## Scope

The theorem classifies the complete frequency-dependent factor in equation (7.8), up to a nonzero
frequency-independent constant, and finite products of such factors.  It does not classify the
full interacting thermal spectral density, the OPE sum, or a bulk black-hole reconstruction.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary`

Observation module: `GaloisForLFunctions.HTGeometry.ThermalCFTWignerSmithObservability`

Parent module: `GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary`

- `gammaReflectionProductMero_eq_gauge_mul_reducedVeneziano`
- `differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight`
- `hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight`
- `differentialAlgebraicOver_thermalCFTFrequencyResponseMero_iff_integerWeight`
- `hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight`
- `thermalCFTFrequencyResponseValue_neg`
- `thermalCFTKMSResponseValue_neg`
- `gammaReflectionProductMero_half`
- `exists_nonintegerWeight_of_hypertranscendental_finset_product`
- `exists_nonintegerWeight_of_hypertranscendental_finset_response_product`
- `thermalCFTResponseWignerSmithLogClockMero_eq_gamma_add_const`
- `differentialAlgebraicOver_thermalCFTResponseWignerSmithLogClockMero_iff_integerWeight`
- `hypertranscendentalOver_thermalCFTResponseWignerSmithLogClockMero_iff_nonintegerWeight`

Verification:

- `lake build +GaloisForLFunctions.HTGeometry.ThermalCFTGammaResponseBoundary`
- `lake env lean GaloisForLFunctions/HTGeometry/ThermalCFTGammaResponseBoundary.lean`
- `#print axioms` for all five theorems: only `propext`, `Classical.choice`, `Quot.sound`

## Log

- 2026-07-17 — primary formula and holographic interpretation located; scratch proof of the exact DA/HT classification, `h=1/2` collapse, and finite-sector source localization passes.
- 2026-07-17 — promoted after serialized exact-module build, direct-file check, and standard-only axiom audit.
- 2026-07-17 — exponential-gauge DA hypothesis discharged; complete frequency response and dressed finite-sector localization verified by direct-file check.
- 2026-07-17 — symmetric reflection classification simplified to a specialization of the new
  arbitrary-shift opposite-Gamma parent theorem.
- 2026-07-17 — calibrated to the relativistic beta-decay Fermi Gamma core; exact
  weak-decay/thermal detailed-balance identity formalized.
- 2026-07-17 — added and exactly built the thermal-CFT Wigner--Smith observation module.  Its
  constant gauge law and exact DA/HT weight selector pass direct verification, standard-only axiom
  audit, and source scan.
