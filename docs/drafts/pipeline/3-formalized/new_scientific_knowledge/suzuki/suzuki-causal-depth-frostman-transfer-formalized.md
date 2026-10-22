# Suzuki causal depth fusion is an exact Frostman transfer — formalization certificate

- **Stage:** 3 — formalized in Lean 4
- **Paper theorem:**
  `./suzuki-causal-depth-frostman-transfer.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalDepthFrostmanTransfer.lean`
- **Umbrella import:**
  `formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean`
- **RH used:** no
- **Computation used:** no

## Formal theorem surface

The module proves unconditionally:

- `suzukiCriticalApertureDepthFusionRadius_pos` and
  `suzukiCriticalApertureDepthFusionRadius_lt_one`: exact source radius lies in `(0,1)`;
- `suzukiCriticalApertureDepthRatio_eq_radius_mul_phase`: complex quarter-shift ratio is positive
  radius times the half-prime-log clock;
- `suzukiCriticalApertureBoundaryAtom_zero_eq_endpoint_mul_phase`: depth-zero forcing has the same
  source phase;
- `suzukiCriticalApertureDepthFusedAtom_eq_mobius`: causal depth sum is the exact disk resolvent;
- `normSq_suzukiCriticalApertureDepthFusedAtom_eq`: explicit Poisson denominator;
- `normSq_suzukiCriticalApertureDepthFusedAtom_eq_zero_mul_frostmanProfile`: exact normalized
  Suzuki--CCM Frostman identity;
- `suzukiCriticalEntryWallEndpointAmplitude_zero_pos`,
  `normSq_suzukiCriticalApertureDepthFusedAtom_zero_pos`, and
  `normSq_suzukiCriticalApertureDepthFusedAtom_div_zero_eq_frostmanProfile`: strict central
  positivity and the literal normalized ratio form;
- `suzukiCriticalApertureDepthFrostmanProfile_floor_le` and
  `suzukiCriticalApertureDepthFrostmanProfile_le_one`: sharp corpus profile bounds;
- `suzukiCriticalApertureDepthFrostmanProfile_eq_one_iff_phase`: cap equality is exact prime-phase
  recurrence;
- `suzukiCriticalApertureDepthFrostmanPairProfile_eq_two_iff`: two distinct primes have joint cap
  only at height zero;
- `suzukiCriticalApertureDepthFrostmanSeparation_nonneg` and
  `suzukiCriticalApertureDepthFrostmanSeparation_eq_zero_iff`: translation-invariant faithful
  height separator.

## Scope

This module proves the first exact non-flat diagonal transfer exposed after the S62 height-flat
obstruction.  It does not identify the concrete restricted-Weil rectangular trace, construct the
cross-prime/archimedean correction, prove the Ward remainder lower bound, or prove RH.

## Verification

- direct `lake env lean` source check passed;
- targeted `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed `9477/9477`;
- capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden declaration and whitespace scans are clean;
- repository lint reaches this module and remains red only on 21 unrelated unreachable modules.
