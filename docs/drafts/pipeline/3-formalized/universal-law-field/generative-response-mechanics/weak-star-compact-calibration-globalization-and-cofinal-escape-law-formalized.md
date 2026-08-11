# Weak-star compact calibration globalization and cofinal escape law — Lean certification

- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/generative-response-mechanics/weak-star-compact-calibration-globalization-and-cofinal-escape-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.CompactCalibrationGlobalization`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[FORMALIZED] [UMBRELLA BUILD PASSED] [NO SORRY] [NO ADDED AXIOMS]`

## Certified declarations

- `weakNormingFace`
- `isClosed_weakNormingFace`
- `weakNormingFace_nonempty`
- `weakNormingFace_subset_closedBall`
- `global_common_normer_of_finite`
- `common_normer_iff_finset`
- `finite_witness_of_no_common_normer`

The proof uses mathlib's weak-star Banach--Alaoglu theorem, Hahn--Banach norming functional, and
compact finite-intersection theorem. No finite-dimensionality or countability assumption is used.

## Audit commands

```text
lake env lean GaloisForLFunctions/HTGeometry/CompactCalibrationGlobalization.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint
```

Final foreground umbrella build passes with 11,615 jobs. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Universal-law lint passes; no Lean process remains running.
