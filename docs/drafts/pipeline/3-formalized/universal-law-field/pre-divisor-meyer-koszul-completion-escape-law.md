# Pre-divisor Meyer--Koszul completion-escape law — Lean certificate

- **ID:** `ULF-MKCE-1`
- **Stage:** 3-formalized
- **Paper proof:** `../../2-fully-proven/universal-law-field/completion-index-transgression-mechanics/pre-divisor-meyer-koszul-completion-escape-law.md`
- **Module:** `GaloisForLFunctions.HTGeometry.PreDivisorMeyerKoszulCompletionEscape`

Certified declarations:

- `RHTower.deningerMeyerHalfDensityL2PrimeKoszulCoordinateAt`
- `RHTower.deningerMeyerStrongLogPrimeKoszulCoordinateAt`
- `RHTower.deningerMeyerHalfDensityL2LM_primeKoszulCoordinateAt`
- `RHTower.deningerMeyerHalfDensityStrongRange`
- `RHTower.deningerMeyerPrimeKoszulInverseDomainAt`
- `RHTower.deningerMeyerHalfDensityStrongRange_le_inverseDomainAt`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscapeAt`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff`
- `RHTower.DeningerMeyerHalfDensityL2ResolventPreservesStrongSourceAt`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_preserves`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscapeAt_eq_bot_iff_source_surjective`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscapeAt_ne_bot_of_offLine`
- `RHTower.deningerMeyerPrimeKoszulCompletionEscape_law`

Capstone is closed and unconditional: for every Xi divisor and every prime, off-line position
forces nonzero completion escape, while escape vanishing forces critical-line position.  Under
analytic invertibility, escape vanishing is exactly source-preserving inversion.

Verification on 2026-09-02:

- scratch-first `lake env lean /tmp/predivisor_meyer_escape_checks.lean` — PASS
- direct module `lake env lean GaloisForLFunctions/HTGeometry/PreDivisorMeyerKoszulCompletionEscape.lean` — PASS
- targeted `lake build GaloisForLFunctions.HTGeometry.PreDivisorMeyerKoszulCompletionEscape` — PASS
- `/tmp` `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
- wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`
- no full or umbrella build run
