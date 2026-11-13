# Critical wall motion and the logarithmic boundary trace

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; identify a nonzero boundary readout of the actual critical state.
- **Status:** No proof or contribution claimed. Polar identification open.

## Corpus connection

The exact arithmetic translation law gives `E(T_hF-F)=a(exp(8h)-1)W(F,F)`, hence a strictly positive right derivative `8aW(F,F)` at zero. The weak equation removes the cross term.

`exists_causal_coordinates_of_criticalHalfLineGroundState` places the reflected actual state in the range of the logarithmic causal convolution. `logarithmicHalfLineGreenOperator_normalized_boundary_limit` gives a normalized trace `sqrt(log(1/x))·u(x)` for actual Green solutions with locally bounded L² forcing. These statements concern compatible logarithmic form geometry, but do not yet identify the critical state's forcing.

The exact decomposition `gammaHardyPhaseRate_eq_log_reference` isolates the logarithmic symbol from an integrable bounded convolution remainder. `SignedWindowCriticality.eq_zero_of_isWindowSolution` already excludes smooth compact-window extremals with exponential-polynomial forcing; it does not give this half-line state's trace or its magnitude.

## Question

Does a canonical Green representative of the actual critical L² class have a normalized logarithmic boundary trace whose squared magnitude equals its wall-energy derivative? The principal Gamma-symbol normalization must be checked before fixing the trace constant. A positive answer would replace mere endpoint support by a nonzero quantitative boundary invariant.

The statement must use a canonical representative or an essential trace. `IsCriticalHalfLineGroundState` assumes measurability and integral conditions, so null-set changes on the negative half-line can destroy a literal pointwise limit.

## Missing mathematical inputs

1. Express the actual critical weak equation as the logarithmic Green equation, with its literal arithmetic forcing.
2. Prove the required forcing regularity from the actual state; do not add it as a premise.
3. Relate normalized boundary trace to the first translation-energy increment, controlling all lower-order arithmetic and weighted terms.
4. Determine whether this readout is the polar source pairing or a distinct boundary channel. Existing L² cyclicity alone does not identify it.

Sources: `ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateHasCausalCoordinates.lean`, `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicFormHasItsActualInverse.lean`, `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues.lean`, and `CausalReflection/CriticalCausalEnergyTranslation.lean`.
