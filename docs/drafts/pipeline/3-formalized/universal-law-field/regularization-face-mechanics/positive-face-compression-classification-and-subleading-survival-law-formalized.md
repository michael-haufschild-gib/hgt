# Positive-face compression classification and subleading-survival law — formalized

- **ID:** `ulf-rfm-positive-face-compression-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper source:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/regularization-face-mechanics/positive-face-compression-classification-and-subleading-survival-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.PositiveFaceCompression`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-AUDITED] [UMBRELLA-WIRED] [NOT RH]`

## Certified statements

| Paper clause | Lean declaration |
|---|---|
| positive pencil energy and pointwise-bounded observer | `positiveFacePencilEnergy`, `PositiveFacePencilPointwiseBounded` |
| pointwise bounded iff leading composite vanishes | `positiveFacePencil_pointwiseBounded_iff_comp_eq_zero` |
| exact subleading survival on the face | `positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero` |
| simultaneous-family common-kernel classification | `positiveFacePencil_family_pointwiseBounded_iff` |
| injective leading feature admits only zero carrier | `positiveFacePencil_injective_leading_forces_zero_carrier` |
| explicit divergent diagonal source and finite second face | `diagonalPositivePencil_firstRay_unbounded`, `diagonalPositivePencil_secondFace` |
| bundled fourth-branch witness | `positiveFaceCompression_fourthBranch` |

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/PositiveFaceCompression.lean
lake build GaloisForLFunctions.HTGeometry.PositiveFaceCompression
lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint
```

All commands passed in the foreground. Leaf build completed 8,655 jobs; umbrella build completed
11,861 jobs. Umbrella warnings came from pre-existing replayed modules; the new module emitted no
warning. Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
all five audited capstones. No `sorry`, `admit`, added axiom, `opaque`, or `unsafe` declaration is
present.

## Exact interpretation

Lean proves the frozen three-branch regularization conjecture false: a divergent positive pencil
can remain finite and retain nonzero subleading information by compression to a proper leading
kernel. It also proves the sharp boundary—injective leading features admit no nonzero fixed face.
This is a classical bridge and a field-search correction, not an RH theorem.

## Log

- 2026-08-13 — direct elaboration, leaf build, axiom audit, lint, umbrella elaboration, and final
  umbrella build passed; Stage-3 certificate created.
