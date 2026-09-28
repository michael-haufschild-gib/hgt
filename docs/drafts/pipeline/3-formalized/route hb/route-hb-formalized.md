# Route HB literal-realization cards — Lean certificate

- **ID:** `route-hb-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proofs:** the seven cards in this folder
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

All modules are in `formal/GaloisForLFunctions/RHTower/` and wired into the `RHTower` umbrella.
Axiom audit of every capstone below: `[propext, Classical.choice, Quot.sound]`.

| Card | Module | Capstones |
|-|-|-|
| `hb-canonical-qnm-self-source-zero` | `ThetaCuspHawkingBMCanonicalQNMSelfSourceZero` | `D4BMOriginalCanonicalAction.canonicalQNMValue_eq_zero_of_physicalSelfSourceCoefficient_eq_zero` |
| `hb-qnm-left-source-affine-collision-obstruction` | same | `canonicalQNMValue_zero_ne_unitLeftSource_of_physicalSelfSourceCoefficient_eq_zero`, `not_canonicalQNMValue_eq_zero_iff_unitLeftSource_eq_zero`, `hbXiPeierlsMinusLeftSource_eq_zero_iff` |
| `hb-onshell-cleared-native-l2-no-go` | `ThetaCuspHawkingBMOnShellClearedNativeL2NoGo` | `D4BMJointSource.not_memLp_clearedReducedCoefficient_onShell`, `_physicalRate`, `_cuspPhysicalRate`, `onShellHorizonProfile_one` |
| `hb-literal-causal-source-polarization` | `ThetaCuspHawkingBMCausalSourcePolarization` | `D4BMOriginalCausalPotential.originalPotential_amplitude`, `twoLegPotential_wave`, `twoLeg{Potential,Forcing}_eq_polarization`, `_diag`, `_symm`, `twoLegPotential_boundary`, `twoLegPotential_before_onset` |
| `hb-literal-finite-cutoff-two-leg-current` | `ThetaCuspHawkingBMFiniteCutoffTwoLegCurrent` | `D4BMPhysicalModeAction.contactRenormalizedCurrent_transport`, `twoLegCurrent_transport`, `twoLegCurrent_swap` |
| `hb-literal-time-lift-stream-realization` | `ThetaCuspHawkingBMTimeLiftStreamJet` | `D4BMPhysicalLiftCurrent.ofField_timeLiftStream`, `timeLiftStream_contDiffAt`, `metricIngoingCurrent_timeLiftStream`, `metricIngoingCurrent_timeLiftStream_add_contact` |
| `hb-retarded-compact-weak-realization` | `ThetaCuspHawkingBMRetardedCompactWeakRealization` | `D4BMRetardedCompactWeakRealization.eventPotential_weak_wave`, `eventPotential_sub_correctedFutureField_weak` |

## What the corpus already had

The literal HB objects and their identities: `outerDensity_decomposition`, the canonical cutoff /
radial value / QNM limits, `physicalSelfSourceCoefficient_zero_iff_xi`,
`hbXiPeierls{Plus,Minus}LeftSource_eq`, `reducedCoefficient_frequency_horizon`,
`clearedOnset_source_rate`, `not_memLp_two_restrict_Iio_of_atBot_norm_ge_one`,
`fullNullResponse_native`, `originalPotential_wave`, `physicalProjectedModeAction_transport`,
`lift_action_current`, `ofField_ingoing_comp`, `metricIngoingCurrent_eq`,
`originalPotential_smooth`, `complete_original_weak_wave`, `weakWaveTest_regular`.

## What was built

Beyond the card statements: the amplitude homogeneity of every radial source coefficient; the
two-jets of one-coordinate and angular-block fields (`ofField_coord`, `ofField_angular`) and
smoothness of the radial lift profile; a general smooth cutoff in finite-dimensional spaces
(`exists_contDiff_cutoff`); compact integration by parts in one and two equal directions; the
hyperbolic angular transposition for arbitrary smooth fields; the compact weak transposition of
`weakWaveTest` against every smooth field; germ locality of the weak test and field operators.
