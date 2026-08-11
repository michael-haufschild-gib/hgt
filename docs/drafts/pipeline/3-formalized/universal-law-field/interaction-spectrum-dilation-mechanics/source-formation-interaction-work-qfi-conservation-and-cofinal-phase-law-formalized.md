# Source-formation interaction work and cofinal phase law — formalized core

- **Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/interaction-spectrum-dilation-mechanics/source-formation-interaction-work-qfi-conservation-and-cofinal-phase-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-PROVED CORE] [NO SORRY] [NO ADDED AXIOMS]

## Certified declarations

- `directParityInteractionSq_eq_interactionWorkWeight`: source parity generates product
  interaction work.
- `sum_interactionWorkWeight_eq_one`: total work conservation.
- `sum_interactionWorkWeight_of_mem_eq`: work marginals reconstruct every activation coordinate.
- `meanInteractionDegree_eq_sum`: mean interaction degree equals total local activation.
- `visibleInteractionWork_add_hiddenInteractionWork`: exact visible/hidden partition.
- `hiddenInteractionWork_nonneg`, `visibleInteractionWork_le_one`: passivity.
- `natCast_succ_mul_hiddenInteractionWork_le_mean`: finite Markov properness bound.
- `fullInteractionQFI_sub_visibleInteractionQFI`: lost coherent QFI is four times hidden work.
- `interactionActivation_injective_on_lower_half`: marked lower chamber reconstructs Bernoulli source.
- `prime_rpow_le_interactionActivation_le`: prime activation is uniformly comparable with
  `p^(-sigma)`.
- `summable_primeInteractionActivation_iff`: global formation phase changes exactly at `sigma=1`.
- `primeInteractionFormationPhase_reflection_iff`: reciprocal reflection preserves that phase
  exactly at the fixed point `sigma=1`.

The paper's explicit Chebyshev fixed-degree escape limit and critical limiting QFI remain outside
this formalized core and stay unchecked on the Stage-2 gate.

## Verification

- direct foreground elaboration passed;
- leaf build passed: 2,350 jobs;
- ULF umbrella build passed;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
