# A concrete named transcendental (Liouville constant), transcendental over ℚ

- **ID:** named-transcendental
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean; built because absent from this toolchain
- **Statement:** This mathlib provides Liouville's construction but only `Transcendental ℤ` and no positivity. Built: `transcendental_int_to_rat` (ℤ→ℚ transcendence via IsFractionRing.isAlgebraic_iff), `liouvilleConst := liouvilleNumber 10`, `liouvilleConst_transcendental : Transcendental ℚ liouvilleConst`, `liouvilleConst_pos : 0 < liouvilleConst`.
- **Lean:** `GaloisForLFunctions.{transcendental_int_to_rat, liouvilleConst, liouvilleConst_transcendental, liouvilleConst_pos}` in `formal/GaloisForLFunctions/HTGeometry/NamedTranscendental.lean`. Axiom-clean.
- **Use:** makes the shifted-value independence unconditional at a named number — `shifted_values_mult_independent_liouville` (no hypotheses).

## Log
- 2026-07-07 — created (a named transcendental was not in this mathlib; built per standing order).
