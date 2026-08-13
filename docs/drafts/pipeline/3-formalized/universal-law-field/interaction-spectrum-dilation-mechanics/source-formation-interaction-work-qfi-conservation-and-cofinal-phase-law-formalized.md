# Source-formation interaction work and cofinal phase law — fully formalized

- **Paper source:** `docs/drafts/pipeline/3-formalized/universal-law-field/interaction-spectrum-dilation-mechanics/source-formation-interaction-work-qfi-conservation-and-cofinal-phase-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-FORMALIZED] [EXACT PAPER SURFACE] [NO SORRY] [NO ADDED AXIOMS]

## Biased-Walsh basis and passive filtration

Module `GaloisForLFunctions.HTGeometry.BiasedWalshInteractionMechanics` certifies:

- `biasedWalsh_orthonormal`, `biasedWalsh_weighted_dual_kernel`;
- `biasedWalsh_reconstruction`, `biasedWalsh_parseval`;
- `biasedWalshCoefficient_projection`, `biasedWalshProjection_normSq_le`;
- `biasedWalshNormSq_sub_projection_eq_hiddenWork`;
- `biasedWalshHiddenWork_eq_add_projectionBand`;
- `biasedWalshCoefficient_parity`;
- `biasedWalshPureStateQFI_eq_four_mul_variance`.

These close the paper's exact finite basis, reconstruction, Parseval, contraction, hidden-tail,
band-composition, multiplicative-parity coefficient, and covariance-form pure-state QFI claims.

## Interaction work, QFI, and cofinal phase

Module `GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics` certifies:

- `directParityInteractionSq_eq_interactionWorkWeight`: source parity generates product
  interaction work.
- `sq_biasedWalshCoefficient_parity_eq_interactionWorkWeight`: literal biased-Walsh parity
  coefficient energy is that exact work law.
- `sum_interactionWorkWeight_eq_one`: total work conservation.
- `sum_interactionWorkWeight_of_mem_eq`, `sum_interactionWorkWeight_of_subset_eq`: all prescribed
  interaction marginals.
- `meanInteractionDegree_eq_sum`, `interactionDegreeVariance_eq_sum`: exact Poisson-binomial mean
  and variance.
- `visibleInteractionWork_add_hiddenInteractionWork`: exact visible/hidden partition.
- `hiddenInteractionWork_nonneg`, `visibleInteractionWork_le_one`: passivity.
- `natCast_succ_mul_hiddenInteractionWork_le_mean`: finite Markov properness bound.
- `visibleInteractionWork_le_variance_div_gap_sq`: exact finite Chebyshev wrapper.
- `tendsto_visibleInteractionWork_zero_of_mean_tendsto_atTop`: abstract fixed-degree escape.
- `biasedWalshPureStateQFI_parity_eq_fullInteractionQFI` and
  `biasedWalshPureStateQFI_parityProjection_eq_visibleInteractionQFI`: genuine QFI realization.
- `biasedWalshPureStateQFI_parity_sub_projection_eq_four_mul_hiddenWork`: exact work--information
  conservation for the realized pure-state QFI.
- `interactionActivation_injective_on_lower_half`: marked lower chamber reconstructs Bernoulli source.
- `prime_rpow_le_interactionActivation_le`: prime activation is uniformly comparable with
  `p^(-sigma)`.
- `summable_primeInteractionActivation_iff`: global formation phase changes exactly at `sigma=1`.
- `primeFormation_uniform_tight`: uniform tightness over every finite prime aperture for `sigma>1`.
- `tendsto_primeApertureMean_atTop`, `tendsto_primeApertureVisibleInteractionWork_zero`: cofinal
  escape for every `0<sigma<=1`.
- `tendsto_criticalPrimeApertureEmptyWork_zero`,
  `tendsto_criticalPrimeApertureFullInteractionQFI_four`, and
  `tendsto_criticalPrimeApertureVisibleInteractionQFI_zero`: exact critical limits.
- `primeInteractionFormationPhase_reflection_iff`: reciprocal reflection preserves that phase
  exactly at the fixed point `sigma=1`.

The unproved source-native comparison needed to turn the phase classifier into an RH executor is
not a theorem of this card. It is preserved as separate Stage-1 research card
`source-native-reflection-comparison-and-rh-selection-interface.md`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/BiasedWalshInteractionMechanics.lean` passed;
- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveInteractionSpectrumMechanics.lean`
  passed;
- targeted builds passed for both modules (8,657 and 8,659 cached jobs respectively);
- `lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean` passed;
- capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reports no error in either module; global exit remains nonzero only because concurrent
  unrelated RHTower/HTGeometry modules are not yet wired into their theorem-area umbrellas.
