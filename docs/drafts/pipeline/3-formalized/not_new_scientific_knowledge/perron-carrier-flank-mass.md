# Coefficient-independent Perron carrier mass

- **ID:** perron-carrier-flank-mass-formal
- **Stage:** 3-formalized
- **Status:** `[PROVED, Lean]`
- **Date:** 2026-07-10
- **Paper theorem:** `docs/drafts/pipeline/2-fully-proven/new/perron-carrier-flank-mass.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronCarrierFlankMass.lean`

## Formal surface

### Kernel-free flank growth

- `perronEAt_left_flank_norm_le`
- `perronCarrierFlankWeight`
- `HasPerronCarrierFlankMassAt`
- `HasPerronCarrierFlankMass`
- `hasPerronBoundaryChargeAt_of_escape_of_carrierFlankMassAt`
- `HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge`
- `HasPerronCarrierFlankMass.hasVariableQuietFlankCoefficientBound`

### Hilbert-source producer

- `HasPerronCarrierFlankL2EnergyAt`
- `HasPerronCarrierFlankL2Energy`
- `HasPerronCarrierFlankL2EnergyAt.hasPerronCarrierFlankMassAt`
- `HasPerronCarrierFlankL2Energy.hasPerronCarrierFlankMass`
- `perronFlankL2Constant`

### Coefficient-independent horizontal escape

- `perronContourIntegrand_right_integrable`
- `HasPerronHorizontalEscapeAt`
- `HasVariablePerronHorizontalEscape`
- `perronStripKernelEnvelope`
- `perronEAt_strip_high_norm_le`
- `perronCarrierHorizontalWeight`
- `HasPerronCarrierHorizontalMassAt`
- `HasPerronCarrierHorizontalMass`
- `HasPerronCarrierHorizontalMassAt.hasPerronHorizontalEscapeAt`
- `HasPerronCarrierHorizontalMass.hasVariablePerronHorizontalEscape`

### Exact-support capstones

- `coefficient_index_le_exact_flank_radius_of_carrierFlankMass`
- `coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy`
- `coefficient_index_le_exact_flank_radius_of_carrierFlankMass_horizontalEscape`
- `coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy_horizontalEscape`
- `coefficient_index_le_exact_flank_radius_of_carrierMass`
- `coefficient_index_le_exact_flank_radius_of_carrierL2StripMass`

The strongest capstone consumes only coefficient-independent carrier data: geometric negative-line
`L²` energy and eventual finite weighted horizontal mass. Absolute convergence of the Dirichlet
series automatically supplies right-edge convergence.

## Verification

- [x] Target module elaborates.
- [x] Targeted Lake build passes (`8480/8480`); no umbrella build was run.
- [x] Principal theorem axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Generated API refreshed and `formal_tools.py lint --check-generated` passes.

## Remaining gate

Exact common-source cross-line coherence now constructs the geometric negative-line energy, but
`SoninPerronSupportTransfer.lean` proves that coherence plus weighted horizontal mass forces finite
Dirichlet support. `PerronMellinSeamResidue.lean` now constructs a defect-bearing seam law and proves
that its normalized Perron coordinates recover the infinite arithmetic tail. `[OPEN CORE]` Build
that seam for the target and constrain its coordinates using divisor or cocycle data.
