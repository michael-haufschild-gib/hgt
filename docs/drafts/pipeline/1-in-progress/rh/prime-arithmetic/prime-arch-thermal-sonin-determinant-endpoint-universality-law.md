# Prime--arch thermal--Sonin determinant endpoint universality law

Status: Lean source written; exact audit pending.

## Lean-source inputs

- `RHTower/PrimeArchBernsteinPuritySourceEndpoint.lean`: rectangular prime--polar source endpoint iff subexponential endpoint Bernstein purity.
- `RHTower/SoninCoupledBernsteinMismatchRH.lean`: thin exponential collars imply zero exponential rate.
- `RHTower/SoninCoupledNormalizedDeterminantCollar.lean`: endpoint collar iff each concrete coupled-Sonin relative-determinant purity collar.
- `RHTower/XiPrimeArchThermalEndpointUniversalityLaw.lean`: source endpoint iff simultaneous realization of thirty-one thermal/Hausdorff/KMS charts.

## Universal law

For every admissible rectangular source and every nondegenerate coupled-Sonin aperture, the source
abscissa bound is equivalent to the concrete relative determinant's arbitrarily thin Bernstein-
purity collar.  Quantifying over all apertures and adjoining these collars to the existing thermal
certificate leaves the exact source classifier unchanged.

## Novelty audit

Pending post-formalization primary-source literature search.  Corpus search found no theorem
connecting the rectangular prime--polar endpoint certificate to all coupled-Sonin determinant
apertures.

## Verification

- Development command: pending `lake env lean GaloisForLFunctions/RHTower/PrimeArchThermalSoninDeterminantEndpointUniversalityLaw.lean`.
- Final module build, axiom audit, and lint: pending exhaustion pass.
