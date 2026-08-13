# Positive-face compression classification and subleading-survival law — formalized

- **ID:** `ulf-rfm-positive-face-compression-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper source:** `docs/drafts/pipeline/3-formalized/universal-law-field/regularization-face-mechanics/positive-face-compression-classification-and-subleading-survival-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.PositiveFaceCompression`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-AUDITED] [UMBRELLA-WIRED] [NOT RH]`

## Certified statements

| Paper clause | Lean declaration |
|---|---|
| positive pencil energy and pointwise-bounded observer | `positiveFacePencilEnergy`, `PositiveFacePencilPointwiseBounded` |
| pointwise bounded iff leading composite vanishes | `positiveFacePencil_pointwiseBounded_iff_comp_eq_zero` |
| carrier formulation `ran J ⊆ ker B` | `positiveFacePencil_pointwiseBounded_iff_range_le_ker` |
| exact subleading survival on the face | `positiveFacePencilEnergy_eq_subleading_of_comp_eq_zero` |
| retained energy is nonzero iff the subleading composite is nonzero | `positiveFacePencilEnergy_nonzero_iff_subleading_comp_ne_zero` |
| heterogeneous simultaneous-family/common-analysis-kernel classification | `positiveFacePencil_heterogeneous_family_pointwiseBounded_iff` |
| unchanged heterogeneous subleading family | `positiveFacePencil_heterogeneous_family_energy_eq_subleading` |
| analysis-map kernel and formation-Laplacian radical | `ker_positiveFaceAnalysisMapL2`, `ker_positiveFaceFormationLaplacian` |
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

All commands passed in the foreground. The 2026-08-13 closure audit generalized the module from
real scalar maps to every nontrivially normed field, hence both real and complex Hilbert spaces,
and added the exact range, heterogeneous analysis-map, and formation-Laplacian clauses. Direct
Lean checking is warning-free; the targeted leaf build completed 8,655 jobs. Scratch
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for every new capstone
and the Sonin finite-prime Calkin boundary theorem. No `sorry`, `admit`, added axiom, `opaque`, or
`unsafe` declaration is present.

## Exact interpretation

Lean proves the frozen three-branch regularization conjecture false: a divergent positive pencil
can remain finite and retain nonzero subleading information by compression to a proper leading
kernel. It also proves the sharp boundary—injective leading features admit no nonzero fixed face.
This is a classical bridge and a field-search correction, not an RH theorem.

## Log

- 2026-08-13 — direct elaboration, leaf build, axiom audit, lint, umbrella elaboration, and final
  umbrella build passed; Stage-3 certificate created.
- 2026-08-13 — exact paper surface closed: real/complex scope, `ran J ⊆ ker B`, nonzero
  subleading survival, heterogeneous direct-sum analysis, and
  `ker (Σ Bᵢ*Bᵢ) = ⋂ ker Bᵢ`; direct Lean, targeted build, and axiom audit passed.
