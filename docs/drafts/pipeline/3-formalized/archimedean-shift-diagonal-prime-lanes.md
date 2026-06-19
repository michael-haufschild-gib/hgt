# Archimedean shift as diagonal prime-lane dilation

- **ID:** archimedean-shift-diagonal-prime-lanes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/archimedean-prime-cross-term.md` and `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Statement:** In the Bohr coordinate `x_p=p^{-s}`, the additive shift `s |-> s+1` acts as the prime-lane dilation `x_p |-> p^{-1} x_p`, simultaneously for every prime.

## Goal
This banks the exact coordinate identity tying the archimedean additive shift to the diagonal of the prime lanes. It does not formalize Gamma factors, completed Tannakian categories, the functional equation, or positivity/RH claims.

## Paper Proof
For each prime `p`,
`p^{-(s+1)} = p^{-s-1} = p^{-s} p^{-1}` by the complex-power subtraction identity for the nonzero base `p`.
Applying this identity for every prime gives the coordinatewise function equality.

## Gates
- [x] 0 -> 1  in-progress: exact coordinate identity extracted from the archimedean/prime-lane cards.
- [x] 1 -> 2  fully-proven: paper proof above, using the complex-power subtraction identity.
- [x] 2 -> 3  formalized: Lean theorems `primeDiagonal_shift_apply` and `primeDiagonal_shift` in `formal/GaloisForLFunctions/ArchimedeanLane.lean`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal coordinate lemma for the archimedean-lane note.

## Log
- 2026-06-19 — Leaner split this exact shift identity from the broader archimedean-prime cards. The parent cards remain in `2-fully-proven` because their Gamma/FE/cocycle and positivity layers are not fully Lean-formalized.

