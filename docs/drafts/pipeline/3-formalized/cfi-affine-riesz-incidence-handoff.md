# CFI affine-Riesz incidence handoff

## Status

Formalized 2026-08-29. Frontier map was not edited.

Lean module:
`formal/GaloisForLFunctions/RHTower/CoupledFloorMobiusAffineRieszHandoff.lean`.

## Discharged proof chain

`coupledErrorVector = lower incidence - upper incidence`

→ undo common critical clock at `t = log X`

→ exact Suzuki coupled error

→ critical affine quotient plus Gamma completion

→ square-root Riesz transport

→ exact `suzukiCompletedRieszCriticalJetApprox`

→ one positive cofinal schedule tracking `mobiusDivisorSquareRootAbelMoment`

→ normalized incidence boundedness iff `MobiusDivisorSquareRootAbelBounded`

→ RH.

This discharges CFI's missing `LAND` gate. The previously formalized
`coupledFloorMobiusCriticalBoundary_singularCancellation` supplies its `ORD` gate. CFI is therefore
closed as a coefficient-faithful interface into CCM-FU; remaining boundedness is exactly the
existing RH-equivalent CCM-FU receiver, not an unlanded CFI premise.

## New closed theorems

- `exp_mul_tsum_coupledFloorMobiusIncidence_eq_coupledError`: exact integer-clock recovery from the
  literal unsplit lower-minus-upper incidence.
- `coupledFloorMobiusAffineRieszReadout_eq_suzukiCompletedRieszCriticalJetApprox`: exact finite
  CFI-to-CCM-FU landing.
- `exists_coupledFloorMobiusAffineRieszCofinalSchedule`: unconditional positive moving schedule
  with pointwise error `< 1/(N+1)` against the literal Möbius-divisor source.
- `coupledFloorMobiusAffineRieszCofinalBounded_iff_mobiusDivisor`: no boundedness is gained or lost
  by the handoff.
- `exists_coupledFloorMobiusAffineRieszHandoff_iff_rh`: closed capstone giving one unconditional
  coefficient-faithful schedule whose normalized boundedness is equivalent to RH.

## Novelty audit

Corpus searches used `scripts/formal_tools.py research`. Existing files contained the incidence,
finite Suzuki jets, cofinal schedules, and Möbius-divisor RH endpoint separately, but no theorem
identified the literal incidence with the completed Riesz jet or transferred the endpoint to it.

Literature audit through 2026-08-29 covered Suzuki's screw-function papers
(arXiv:2206.03682, arXiv:2209.04658), Matsumoto--Suzuki (arXiv:2409.00888), and Suzuki's 2025
Chebyshev-conjecture paper. They contain shifted screw/Laplace and prime-explicit Riesz structures,
but no complementary floor-Möbius incidence, affine critical handoff, or boundedness equivalence of
this form.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/CoupledFloorMobiusAffineRieszHandoff.lean`: passed
  before final build.
- `lake build GaloisForLFunctions.RHTower.CoupledFloorMobiusAffineRieszHandoff`: passed.
- `#print axioms` for all five theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- New module is imported by `GaloisForLFunctions.RHTower`.
- Repository lint still fails only on unrelated unreachable modules and unrelated proof debt in
  `HTGeometry/LocallyCyclicTranslationStabilizer.lean`.
- Build exposed and the session repaired one missing transitive import in
  `CCMRestrictedWeilSourceAlignedArbitraryAccuracy.lean`.

