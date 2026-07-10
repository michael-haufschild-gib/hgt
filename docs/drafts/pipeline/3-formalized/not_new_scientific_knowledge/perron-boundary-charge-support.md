# Perron boundary charge support theorem

- **ID:** perron-boundary-charge-support-lean
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED HERE]`
- **Date:** 2026-07-10
- **Paper:** `../../2-fully-proven/new/perron-boundary-charge-support.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronBoundaryCharge.lean`
- **Statement:** A depth- and knot-dependent boundary exhaustion with normalized left charge
  discharges `HasVariableQuietFlankCoefficientBound`; under `H(M)<=C R^M`, every nonzero
  coefficient satisfies `n<=R`.

## Delivered declarations

- `perronContourIntegrand`
- `HasPerronBoundaryChargeAt`
- `perron_right_integral_norm_le_of_boundaryChargeAt`
- `HasVariablePerronBoundaryCharge`
- `HasVariablePerronBoundaryCharge.hasVariableQuietFlankCoefficientBound`
- `coefficient_index_le_exact_flank_radius_of_boundaryCharge`
- `exists_seq_atTop_tendsto_zero_of_continuous_integrableOn_Ioi`
- `HasPerronStripMassAt`
- `HasPerronStripMassAt.hasPerronBoundaryChargeAt`

The companion module `VariablePerronKink.lean` now also supplies
`perronSecondDiffAt_integral`, the exact variable-width coefficient integral used here.

## Scope

- `[PROVED]` No interior rectangle supremum appears in the formal interface.
- `[PROVED]` Each `(M,delta)` may choose its own height exhaustion.
- `[PROVED]` The boundary constraint composes all the way to exact arithmetic support.
- `[PROVED]` Continuous integrable horizontal charge selects actual quiet heights by unit-interval
  averaging, and `HasPerronStripMassAt` produces the boundary charge.
- `[PROVED]` `PerronCarrierFlankMass.lean` supplies the coefficient-independent continuation:
  negative-line `L2` energy and weighted horizontal carrier mass discharge the boundary Props.
- `[OPEN CORE]` Prove those two masses for the target source-built carrier.

## Verification

- Target source compile: PASS.
- Target module build: PASS (`8479/8479`); no umbrella build was run.
- Scratch `#check`: PASS for the six principal boundary, support, and strip-mass theorems.
- Scratch `#print axioms`: each principal theorem uses only
  `{propext, Classical.choice, Quot.sound}`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 -> 1: boundary-only Prop isolated.
- [x] 1 -> 2: Cauchy boundary inequality and coefficient composition proved.
- [x] 2 -> 3: formalized, target-built, and axiom-audited.
- [x] Coefficient-independent mass producer formalized in the successor module.
- [ ] 3 -> 4: requires target-carrier mass proofs and paper integration.
