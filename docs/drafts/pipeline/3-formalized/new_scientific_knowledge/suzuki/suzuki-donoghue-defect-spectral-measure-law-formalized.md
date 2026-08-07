# Suzuki--Donoghue defect spectral-measure law — Lean certificate

- **ID:** `suzuki-donoghue-defect-spectral-measure-law-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-donoghue-defect-spectral-measure-law.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/HyperbolicModulus.lean`
- `formal/GaloisForLFunctions/HTGeometry/LabelledAtomicMeasure.lean`
- `formal/GaloisForLFunctions/HTGeometry/PoissonBoundaryPositivity.lean`
- `formal/GaloisForLFunctions/HTGeometry/PositiveOperatorInner.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiCrossResolventInstantiation.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueInterlacing.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueSpectralMeasure.lean`
- `formal/GaloisForLFunctions/RHTower/SuzukiProjectiveDefectBoundary.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.HTGeometry.HyperbolicModulus`:

```text
GaloisForLFunctions.HTGeometry.cos_quarterPeriod_eq_zero
GaloisForLFunctions.HTGeometry.freeCentre_odd_not_even
GaloisForLFunctions.HTGeometry.freeClockWeight_eq_coth
GaloisForLFunctions.HTGeometry.freeEvenPencil_eq_zero_iff
GaloisForLFunctions.HTGeometry.freeEvenSpectrum_strictMono
GaloisForLFunctions.HTGeometry.freeMeasure_singleton
GaloisForLFunctions.HTGeometry.freeOddPencil_eq_zero_iff
GaloisForLFunctions.HTGeometry.freeSpectra_interlace
GaloisForLFunctions.HTGeometry.integral_exp_mul_symm
GaloisForLFunctions.HTGeometry.integral_exp_two_mul
GaloisForLFunctions.HTGeometry.integral_one_symm
GaloisForLFunctions.HTGeometry.normSq_freeDeficiencyTransform
GaloisForLFunctions.HTGeometry.normSq_sinh_sub_mul_I
GaloisForLFunctions.HTGeometry.normSq_sinh_sub_mul_I_of_cos_eq_zero
GaloisForLFunctions.HTGeometry.quarterPeriod_weight_const
GaloisForLFunctions.HTGeometry.sinh_add_sinh_conj
GaloisForLFunctions.HTGeometry.sinh_sub_sinh_conj
```

`GaloisForLFunctions.HTGeometry.LabelledAtomicMeasure`:

```text
GaloisForLFunctions.HTGeometry.labelledMeasure_singleton
```

`GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity`:

```text
GaloisForLFunctions.HTGeometry.measure_compl_eq_zero_of_rat_Icc
GaloisForLFunctions.HTGeometry.measure_eq_zero_of_isOpen_of_rat_Icc
```

`GaloisForLFunctions.HTGeometry.PositiveOperatorInner`:

```text
GaloisForLFunctions.HTGeometry.inner_normalize_sq
GaloisForLFunctions.HTGeometry.tInner_eq_inner_of_apply
GaloisForLFunctions.HTGeometry.tInner_normalize_sq
GaloisForLFunctions.HTGeometry.tInner_smul_smul
```

`GaloisForLFunctions.RHTower.SuzukiCrossResolventInstantiation`:

```text
RHTower.inner_spectralResolvent
```

`GaloisForLFunctions.RHTower.SuzukiDonoghueInterlacing`:

```text
GaloisForLFunctions.RHTower.cauchySum_eq_zero_at_center
GaloisForLFunctions.RHTower.cauchySum_nevanlinna_ne_zero_of_im_ne_zero
GaloisForLFunctions.RHTower.deriv_donoghuePurePoint_pos
GaloisForLFunctions.RHTower.donoghuePurePoint_eq_cauchySum
GaloisForLFunctions.RHTower.donoghuePurePoint_eq_cauchySum_of_symmetric
GaloisForLFunctions.RHTower.donoghueResolvent_eq_kernelSum
GaloisForLFunctions.RHTower.donoghueTransform_of_orthonormalEigenbasis
GaloisForLFunctions.RHTower.existsUnique_zero_in_atomGap
GaloisForLFunctions.RHTower.freeReflection
GaloisForLFunctions.RHTower.freeReflection_ne
GaloisForLFunctions.RHTower.freeSpectrum_cauchy_eq_zero_at_center
GaloisForLFunctions.RHTower.freeSpectrum_moment_eq_zero
GaloisForLFunctions.RHTower.freeSpectrum_reflection
GaloisForLFunctions.RHTower.hasDerivAt_donoghuePurePoint
GaloisForLFunctions.RHTower.nevanlinnaWeight
GaloisForLFunctions.RHTower.nevanlinnaWeight_pos
GaloisForLFunctions.RHTower.oddSpectrum_fixedPoint_iff
GaloisForLFunctions.RHTower.pencil_common_zero_iff
GaloisForLFunctions.RHTower.spectralMass_nonneg
GaloisForLFunctions.RHTower.strictMonoOn_donoghuePurePoint
GaloisForLFunctions.RHTower.sum_eq_zero_of_symmetric_odd
GaloisForLFunctions.RHTower.sum_moment_eq_zero_of_symmetric
GaloisForLFunctions.RHTower.sum_spectralMass_eq_normSq
GaloisForLFunctions.RHTower.suzukiHerglotz_eq_zero_iff
GaloisForLFunctions.RHTower.tsum_cauchy_eq_zero_at_center
GaloisForLFunctions.RHTower.tsum_eq_zero_of_symmetric_odd
GaloisForLFunctions.RHTower.tsum_moment_eq_zero_of_symmetric
```

`GaloisForLFunctions.RHTower.SuzukiDonoghueSpectralMeasure`:

```text
GaloisForLFunctions.RHTower.suzukiDonoghueKernel_eq_mobius
GaloisForLFunctions.RHTower.suzukiDonoghueKernel_eq_nevanlinna
GaloisForLFunctions.RHTower.suzukiHerglotz_eq_twoAngleDonoghueQuotient
GaloisForLFunctions.RHTower.suzukiHerglotz_neg_of_parity
GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_phase_residue_at_one
GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_residue_at_one
```

`GaloisForLFunctions.RHTower.SuzukiProjectiveDefectBoundary`:

```text
GaloisForLFunctions.RHTower.SuzukiParityPair
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 59 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.

## Open gates carried by the paper card

- specialist novelty review
- cofinal tightness/intrinsic shift selector
- persistent infinite-atom non-clock theorem
- Xi divisor identification
- RH

These are research frontier items, not formalization debt.
