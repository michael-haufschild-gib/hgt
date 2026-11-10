# Counts on exceptional logarithmic prime windows

- **ID:** A72
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, assemblies table.
- **Statement:** For every `0 ≤ δ < 1`, RH is equivalent to the existence of `C ≥ 0` such that arbitrarily late windows `|log p−T| ≤ 32 log(T+2)`, after independently omitting at most `C exp(δT)` primes, admit natural-number counts `K_p(m)` with `K_p(m)/m² → planeDefect p (1,1)`.

## Proof

[PROVED HERE] A limit of the nonnegative numbers `K_p(m)/m²` is nonnegative. Since the defect equals `2c_B(0)+2c_B(log p)`, these counts give the lower prime-trace bound `2c_B(log p) ≥ −2c_B(0)`. The exceptional logarithmic-window criterion gives RH. Conversely, RH makes every prime defect nonnegative; `K_p(m)=⌊m² planeDefect p (1,1)⌋₊` has the required limit, with empty exceptional sets.

## Formalization

- Module: `SurfaceOfSpecZ/ScaleLocality/CountsOnExceptionalLogarithmicWindows.lean`.
- Theorem: `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.riemannHypothesis_iff_effectiveCounts_logarithmic_windows_off_finset`.
- Direct `lake --old env lean GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/CountsOnExceptionalLogarithmicWindows.lean`: passed.
- Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions/SurfaceOfSpecZ.lean`.

This is a count criterion; it does not construct the counts independently of the defect.
