# Admission-relative exactness, singular promotion, finite-horizon mirage -- Lean certification

- **ID:** ULF-OPM-7
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/admission-relative-exactness-singular-promotion-and-finite-horizon-mirage-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveAdmissionRelativePromotion`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [SINGULAR-PROMOTION SELECTOR] [NOT RH]

## Certified declarations

- `AlgebraicallyExact`, `AdmissiblyExact`;
- `admissiblyExact_implies_algebraicallyExact`;
- `admissionPromotion_trichotomy`;
- `promotionForwardDifference`, `promotionConstantOne`, `countingCalibration`;
- `countingCalibration_forwardDifference`;
- `constantOne_algebraicallyExact`;
- `forwardDifference_one_primitive_formula`;
- `UpperAdmittedCalibration`;
- `no_upperAdmitted_constantOne_primitive`;
- `constantOne_not_admissiblyExact`;
- `cappedCountingCalibration` and its admission/local-difference theorems;
- `every_finiteHorizon_has_upperAdmitted_primitive`;
- `constitutiveAdmissionRelativePromotionMechanism_closed`.

## Exact content

Residuals split into admitted-exact, algebraically exact but admission-singular, and algebraically
nonexact cases. For the integer forward-difference law, the constant-one residual has the counting
primitive algebraically. Every primitive equals `b(0)+n`, so no primitive is upper-bounded. Yet the
capped counting calibration is upper-bounded and solves the residual exactly on every prescribed
finite horizon.

Thus every finite observer can see an admitted repair while global admission rejects all repairs.
This certifies singular promotion as a distinct mechanism selected by legal primitives, not by
algebraic obstruction alone.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveAdmissionRelativePromotion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveAdmissionRelativePromotion
```

The `/tmp` axiom audit reports only standard `propext`, `Classical.choice`, and `Quot.sound` on the
printed significant declarations (with `Classical.choice` absent from the primitive-classification
lemma). No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or computational certificate is used.
