# Calibration-spectrum reconstruction and ancestry law — Lean formalization record

- **ID:** ULF-CSM-1-LEAN
- **Source theorem:** ULF-CSM-1
- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL FINITE CORE]`
  `[RECONSTRUCTIVE CHALLENGE SPECTRUM] [SOURCE ANCESTRY]`
  `[FOURTH-ORGAN STIFFNESS PREDICTION] [NO RH PREMISE] [NO COMPUTATIONAL PROOF]`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.CalibrationSpectrumMechanics`
- **Umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

Lean certifies one mechanism spanning generation, positive envelope, coherent phase, observation,
adaptive challenge, and infinitesimal response:

1. unit calibrators as a structure carrying modulus-one proof;
2. calibration response and nonnegative phase residual;
3. coherent-phase ground attainment and universal ground lower bound;
4. exact reconstruction of envelope, real coherent coordinate, and imaginary coherent coordinate
   from the four calibrators `1,-1,i,-i`;
5. exact positive-kernel transport of the full response spectrum;
6. marked-spectrum nonnegativity and exact ground response equal to marked variation;
7. adaptive-calibration/observer exchange equal to positive observer loss;
8. exact nonnegative source-marked ancestry of every one-stage defect;
9. exact ancestry of observer loss and serial conservation into inherited source residual plus
   observer-created phase frustration;
10. conservative refinement as vertical translation of the entire spectrum;
11. stationary minimizing phase and second-response stiffness equal to coherent modulus;
12. exact conservation of local stiffness as observed stiffness plus observer loss.

The capstone `calibrationSpectrumMechanics_capstone` packages ground attainment, serial ancestry,
and stiffness conservation in one theorem.

## Main declarations

- `UnitCalibrator`
- `calibrationResponse`
- `phaseResidual`
- `phaseResidual_nonneg`
- `calibrationResponse_coherentCalibrator`
- `calibrationResponse_ground_le`
- `calibrationResponse_four_reconstruct_envelope`
- `calibrationResponse_four_reconstruct_re`
- `calibrationResponse_four_reconstruct_im`
- `applyReal_calibrationResponse`
- `markedCalibrationSpectrum`
- `markedCalibrationSpectrum_observerTransport`
- `markedCalibration_ground_exchange`
- `markedVariationDefect_sourceAncestry`
- `positiveObserverLoss_ancestry`
- `markedVariationDefect_serialAncestry`
- `markedCalibrationSpectrum_refinement`
- `phaseCosineResponse_hasDerivAt_min`
- `phaseCosineVelocity_hasDerivAt_min`
- `responseStiffness_conservation`
- `eq_ofReal_norm_of_re_eq_norm`
- `weighted_triangle_eq_iff`
- `positiveObserverLoss_eq_zero_iff`
- `calibrationSpectrumMechanics_capstone`

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/CalibrationSpectrumMechanics.lean`: pass.
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`: pass, 11,613 jobs.
- Axiom audit of reconstruction, transport, exchange, ancestry, refinement, stiffness, and capstone:
  `propext`, `Classical.choice`, `Quot.sound` only.
- Target module has no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
- Repository lint reaches the module without target errors.  Its global nonzero exit is caused by
  unrelated unwired RHTower/HTGeometry modules and concurrently stale generated indexes.

## Exact boundary

Lean proves lower bound plus canonical attainment instead of introducing a separate compact-circle
minimum API; together these are exactly the minimum theorem.  The common-phase equality
classification of the exchange defect is now certified as well:
`weighted_triangle_eq_iff` and `positiveObserverLoss_eq_zero_iff` say the observer loss vanishes
exactly when one calibrator aligns every positively weighted coherent output.

No route object, arithmetic realization, Xi specialization, RH statement, or global calibration
section occurs.  A later selection theorem must construct a pre-zero source realization of this
mechanism and prove its ancestry survives the required cofinal observer exits.
