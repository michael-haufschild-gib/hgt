# APD conjecture loop (250 contributions)

- **ID:** apd-250-contributions-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop card)
- **Source:** `formal/GaloisForLFunctions/ArithmeticPositiveDuality/README.md` §8–§10
- **Statement:** Answer the open APD topics with unconditional Lean theorems, one conjecture at a
  time; log every success and failure in `logs/apd-250-2026-10-25.md`.

## Goal
Each item: positive side, spectral side, gap, integer; inserted or intrinsic charge; depth scaling;
battery behaviour (README §10).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  (per conjecture)
- [ ] 2 → 3  (per conjecture)

## Current conjecture
**C13–C16 (what the successor sees of the dilation spectrum).**
- C13: the autocorrelation of any nonzero `H ∈ C_c(ℝ)` is the dilation part of a positive-definite
  state on `Aff(ℚ)` with non-constant successor (vector state of the real `ax + b` group).
- C14: in every unitary representation of `Aff(ℚ)`, translates of an archimedean dilation
  eigenvector form a blind family; distinct frequencies never mix; vectors orthogonal to a
  frequency with continuous dilation orbit never mix with it.
- C15: the GNS Hilbert space (completion of the pre-Hilbert space) and its representation.
- C16: `|φ(x ↦ x + b) − φ(x ↦ x + b')| ≤ 2ν_c(ℝ)`, `ν_c` the continuous part of the dilation
  spectral measure; box averages give the atoms as eigenvectors.

## Done
- C1–C5 (P18–P22), C6–C8 (P23–P25), C9 atomic blindness (P26), C10 Kronecker decomposition,
  C11 Kakutani wall, C12 Weil's correlation carries no successor.

## Next
- Classification of the extensions of Weil's correlation, indexed by the critical zeros.
- Singular continuous dilation spectra: seen or blind?

## Log
- 2026-10-25 — created; C1 opened.
- 2026-10-26 — C1–C5 formalized; C6–C8 drafted.
- 2026-10-26 — C6–C12 formalized; C13–C16 opened.
