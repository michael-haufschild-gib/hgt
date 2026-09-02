# Finite permutation Frobenius--Verschiebung trace blindness — Lean certificate

- **ID:** `ULF-FVBLIND-1`
- **Stage:** 3-formalized
- **Paper proof:** `../../2-fully-proven/universal-law-field/completion-index-transgression-mechanics/finite-permutation-frobenius-verschiebung-trace-blindness.md`
- **Module:** `GaloisForLFunctions.HTGeometry.FinitePermutationFVTraceBlindness`

Certified declarations:

- `finitePermutationFVSquaredSupertrace`
- `finitePermutation_inverseSquare_trace_eq`
- `finitePermutationFVSquaredSupertrace_eq`

The capstone proves that every raw finite permutation Frobenius--Verschiebung squared supertrace is
exactly `(1-q^2)` times the number of squared-Frobenius fixed points.  It is integral and finite-orbit
determined, hence contains no analytic grade parameter.

Verification on 2026-09-02:

- scratch-first `lake env lean /tmp/finite_fv_trace_checks.lean` — PASS
- `lake env lean GaloisForLFunctions/HTGeometry/FinitePermutationFVTraceBlindness.lean` — PASS
- targeted `lake build GaloisForLFunctions.HTGeometry.FinitePermutationFVTraceBlindness` — PASS
- `/tmp` `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
- wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`
- no full or umbrella build run
