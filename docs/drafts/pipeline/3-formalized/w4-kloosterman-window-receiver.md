# W4 — a window receiver from the Kloosterman family

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every nonzero Kloosterman parameter over an odd prime field determines a pure `CurveDatum (Fin 2)` whose traces recover all extension-field Kloosterman sums and whose window forms are nonnegative.

## Proof mechanism

Choose the Hasse–Davenport eigenpairs for every quadratic twist of the parameter. The existing Artin–Schreier–Stepanov estimate bounds the power sums of their squares. Finite spectral rigidity bounds each squared modulus by `p`; determinant `p` forces equality. Normalize by `√p` and use the reciprocal conjugate pair as a curve datum. The existing window theorem supplies the receiver.

## Scope

This is a concrete family-to-receiver calibration using the corpus's independently proved Stepanov estimate. It does not supply a new monodromy weight proof, a non-fibred arithmetic base, or purity for ζ.

## Formalization

`ArithmeticKunnethTheory/WeightFamilies/KloostermanCurveReceiver.lean`:

- `exists_pure_kloosterman_pair`: determinant and twist estimate force both moduli to equal `√p`.
- `conjugatePairDatum`, `conjugatePairDatum_pure`: the normalized reciprocal conjugate pair.
- `exists_kloosterman_curve_receiver`: identifies every extension-field trace and proves nonnegativity of every finite window form.

Checked with `lake --old env lean`.
