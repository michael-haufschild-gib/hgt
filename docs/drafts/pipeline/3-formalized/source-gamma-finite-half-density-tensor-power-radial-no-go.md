# Finite half-density tensor-power Gamma radial no-go

- **ID:** HD-TP
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO + SHARP CLASSIFICATION
- **Corpus basis:** `norm_bilateralHalfDensityCharacter`, `deningerHalfDensityMateGain_eq_norm_inv_sq`, `primeGammaTwoThreePrimeDependentGhost_norm_ratio`, finite Kunneth-power classification.

## Chain

`finite physical half-density tensor power -> exact two-prime Gamma radial ghost -> shared HB/FZZ-P/PW-B/RBH endpoint -> RH`.

## Result

For `t = 2 Re(rho)-1`, degree-`n` physical ratio is `(3/2)^(n*t/2)`. Two-prime Ward compatibility holds iff `n=4` or `t=0`. Thus:

- `n != 4`: universal compatibility is exactly RH, hence only a receiver;
- `n = 4`: compatibility holds unconditionally at every Xi divisor, hence cannot imply RH.

This kills every finite tensor-power radial normalization as independent producer. Survivor must impose source-natural phase/sign/cohomological compatibility beyond radial norm.

## Gates

- [x] Corpus search and exact proof chain
- [x] Paper proof
- [x] Lean proof
- [x] Targeted build/axiom/umbrella audit

## Lean audit

- Module: `GaloisForLFunctions.RHTower.SourceGammaFiniteHalfDensityTensorPowerRadialNoGo`
- Closed theorem: `sharedWardFiniteHalfDensityTensorPowerRadialGhostRouteKilled`
- Direct check and targeted module build pass; umbrella wired.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Corpus/literature audit through 2026-08 found no matching classification.
