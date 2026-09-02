# All-scale integral conformal-trace rigidity — Lean certificate

- **ID:** `ULF-ICTR-1`
- **Stage:** 3-formalized
- **Paper proof:** `../../2-fully-proven/universal-law-field/completion-index-transgression-mechanics/all-scale-integral-conformal-trace-rigidity-law.md`
- **Module:** `GaloisForLFunctions.HTGeometry.AllScaleIntegralConformalTraceRigidity`

Certified declarations:

- `allScaleConformalDeterminant_succ`
- `allScaleConformalCurvature_isEquivalent`
- `allScaleConformalCurvature_eventually_pos_and_tendsto_zero`
- `allScaleIntegralConformalTrace_iff_zero_on_unit_interval`
- `stripIntegralConformalFormation_iff_grade_zero`
- `hyperbolicFormationTrace_eq`
- `hyperbolicFormationSupertrace_eq`
- `hyperbolicFormationDeterminant_eq`
- `hyperbolicFormationMinkowskiConservation`
- `hyperbolicFormationContrast_eq_tanh`
- `hyperbolicFormationVisibility_eq_inv_cosh`
- `allScaleIntegralConformalSupertrace_iff_zero_on_unit_interval`
- `stripIntegralConformalSupertrace_iff_grade_zero`

The capstone is closed: within the critical strip, integrality at every natural formation scale
of either the paired trace or parity supertrace is equivalent to neutral horizontal grade.  The
same even/odd doublet obeys the exact determinant/Minkowski conservation law and recovers contrast
and visibility as `tanh` and inverse `cosh` quotients.

Verification on 2026-09-02:

- scratch-first `lake env lean /tmp/all_scale_checks.lean` — PASS
- `lake env lean GaloisForLFunctions/HTGeometry/AllScaleIntegralConformalTraceRigidity.lean` — PASS
- targeted `lake build GaloisForLFunctions.HTGeometry.AllScaleIntegralConformalTraceRigidity` — PASS
- `/tmp` `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
- wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`
- no full or umbrella build run
