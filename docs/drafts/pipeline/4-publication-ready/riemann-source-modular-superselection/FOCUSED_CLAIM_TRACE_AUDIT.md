# Focused internal claim trace

Manuscript: **No local observation selects a completion phase**

Audit date: 2026-08-01.

This file is internal. Formal verification is used only as a truth guard and is
not a novelty or significance claim. The manuscript contains no reference to
proof software or formalization.

## Universal support-separation law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Arbitrary-support splice agrees on the observed support | `coordinateSupportSplice_agrees` | `formal/GaloisForLFunctions/HTGeometry/TailQuotientSeparationLaw.lean` |
| Its modification support is contained in the observed support | `setOf_coordinateSupportSplice_ne_tail_subset` | same |
| Every erased-support cylinder surjects onto every quotient phase | `coordinateSupportCylinder_surjective_quotient` | same |
| Every quotient reporter determined on one erased support is constant | `coordinateSupport_quotientReporter_constant` | same |
| Family form for an arbitrary collection of observation supports | `observationSupportFamilyCylinder_surjective_quotient` | same |
| Every fibre of a finite-modification quotient is dense in product topology | `finiteModificationQuotient_fiber_dense` | same |
| Coinduced quotient topology is indiscrete | `finiteModificationQuotient_coinduced_eq_indiscrete` | same |
| One-point continuity of a separated-valued pullback forces constancy | `continuousAt_pullback_finiteModificationQuotientReporter_constant` | same |

Direct check: `lake env lean GaloisForLFunctions/HTGeometry/TailQuotientSeparationLaw.lean` passed.
Exact-module final build passed. Promoted declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Exact quotient and operator realizations

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| No finite-horizon reporter selects recurrence-corona phase | `finiteHorizon_recurrenceCoronaReporter_constant`; `nonconstant_recurrenceCoronaReporter_not_determinedBy` | `formal/GaloisForLFunctions/RHTower/AsymptoticCompletionSeparationLaw.lean` |
| No finite-coordinate reporter selects a Hadamard tail-reduced-product phase | `finiteCoordinate_tailHadamardReporter_constant` | `formal/GaloisForLFunctions/HTGeometry/TailHadamardFiniteObservationSeparationLaw.lean` |
| No finite-depth reporter selects a Sonin singular-grade phase | `finiteCoordinate_singularGradeReporter_constant` | `formal/GaloisForLFunctions/RHTower/SingularGradeFiniteObservationSeparationLaw.lean` |
| Fixed Fourier bands lose the escaping Sonin packet | `tendsto_norm_evenFourierCutoff_soninPacketEven` | `formal/GaloisForLFunctions/RHTower/SoninPacketFourierEscape.lean` |
| A lagging moving band loses the packet while an outrunning band captures it | `tendsto_norm_evenFourierCutoff_soninPacketEven_gap`; `tendsto_norm_sub_evenFourierCutoff_soninPacketEven_gap` | `formal/GaloisForLFunctions/RHTower/SoninPacketBandGapLimits.lean` |
| One finite diagonal unitary record is compatible with an asymptotically forgetting CPTP future and nearby unitary futures of every admissible positive temporal rank | `finiteQuantumObservation_futureFan` | `formal/GaloisForLFunctions/HTGeometry/OperationalQuantumRecurrenceFutureFanLaw.lean` |

All four promoted realization modules passed direct foreground checks.

## Exact Riemann source-clock reconstruction

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| One-sided crease derivatives exist and recover every von Mangoldt atom | `ccmFirstClockArithmeticTrace_entry_oneSided`; `ccmFirstClockArithmeticTrace_entry_recovers_vonMangoldt` | `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockCreaseCurrent.lean` |
| Rectangular diagonal Xi-Weil coefficient is real | `xiRectangularWeilLogCoefficient_im_eq_zero` | `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularObservablePoleTomography.lean` |
| On every sufficiently late logarithmic sample it equals a finite prime-polar source plus explicit Gamma correction | `xiRectangularWeilLogCoefficient_re_eq_primePolarSource_add_gammaCorrection` | `formal/GaloisForLFunctions/RHTower/XiGuinandWeilRectangularGammaPolarSourceLaw.lean` |
| Full coefficient series agrees on its initial half-plane with a canonical cutoff-free continuation | `LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation` | `formal/GaloisForLFunctions/RHTower/CCM/CCMRectangularFullObservableDivisorTomography.lean` |
| Continuation poles on `Re s > 1` are exactly shifted strict-right Xi zeros | `meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff` | same |
| Normalized trailing coefficient recovers analytic multiplicity | `normalizedFullObservableResidue_eq_xiRightMultiplicity` | same |
| Functional-equation reflection supplies strict-left copies and polar subtraction leaves exactly critical divisor | `ccmFirstClockXiRationalDivisor_eq_two_right_add_critical`; `ccmFirstClockPolarSubtractedSource_eq_critical` | `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitaryPolarSourceAtlas.lean` |
| Polar-subtracted clock has unique continuous Bohr-almost-periodic asymptote | `ccmFirstClockPolarSubtractedSource_sub_screw_tendsto_zero`; `ccmFirstClockPolarSubtractedSource_asymptote_unique` | same |
| Nonzero Bohr coefficients recover exact critical-line absolute multiplicity | `bohrCoefficient_two_mul_xiLineScrewSeries_eq_multiplicity`; `two_mul_xiLineScrewSeries_recovers_multiplicity` | same |
| Complete crease-pole-frequency reconstruction is bundled unconditionally | `ccmFirstClockCreasePolarFrequencyAtlas` | same |

`CCMUnitaryPolarSourceAtlas.lean` passed direct foreground checking. Its
capstone declaration has only the standard logical axioms listed above.

## RH boundary and positive inverse law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| RH iff the unsubtracted scaled source admits a continuous Bohr-almost-periodic asymptote | `ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_iff_rh` | `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean` |
| Under RH, the exact screw model is an asymptote with the stated uniform error | `ccmFirstClockMovingDenominatorError_bounds_of_rh`; `ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh` | same |
| Every such asymptote is unique and equals the explicit critical screw | `ccmFirstClockAsymptoticBohrModel_eq_explicitScrew` | `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrTorelli.lean` |
| Its coefficient at nonzero frequency is `-N(|lambda|)/lambda^2` | `bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_multiplicity` | same |
| Multiplication by `-lambda^2` recovers exact absolute divisor multiplicity | `ccmFirstClockAsymptoticBohrModel_recovers_absoluteMultiplicity` | same |
| Every value in the compact relation-hull interval is relatively densely approximated by the source | `exists_eventual_window_ccmFirstClockScaledPublishedSource_near_of_rh` | `formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean` |
| Full absolute endpoint occurs exactly under even-total integral-relation parity | `ccmFirstClockAsymptoticHullMax_eq_absoluteBound_iff_parity_of_rh` | same |

Both promoted Bohr modules passed direct foreground checks. Axiom audit found
only `propext`, `Classical.choice`, and `Quot.sound`.

## Explicit exclusions

- No assertion that strict-right polar sector is empty.
- No assertion that asymptote in RH criterion exists.
- No claim that support-splice argument is technically novel.
- No claim that Hedenmalm dense radicals, Wold--Poisson transport,
  Sonin--Calkin seams, or four-unit Ward positivity are corollaries of generic
  support theorem.
- No simplicity or rational-independence assumption.
- No theorem in paper claims zero exclusion or RH.
