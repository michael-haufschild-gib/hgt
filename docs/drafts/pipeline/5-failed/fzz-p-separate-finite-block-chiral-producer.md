# FZZ-P separate finite-block chiral producer

- **ID:** FZZ-P-HC2-NG
- **Stage:** 5-failed
- **Type:** REDUNDANT-BURDEN NO-GO WITH POSITIVE SURVIVOR
- **Route:** Construct a second source-side finite-block interaction to realize the Hermitian chiral
  coefficient isolated by FZZ-P-HC1.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityGradeHermitianization`

## Failed premise

After classifying Hermitian reporters, it appeared that FZZ-P still lacked a source-native
`i sigma_y`-type interaction and required a new finite-block dynamical construction.

## Exact obstruction to the premise

The theorem `fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral` proves on every state

`2 Im(C_beta(u)) = -Q(beta) Re(H_chiral(u))`.

Thus the literal source-grade crossing already is the unique Hermitian chiral reporter, up to the
nonzero scalar `-Q(beta)/2` at positive scale.  A separate finite-block producer would duplicate an
existing source mechanism rather than close a proof gap.

## Strongest positive survivor

The survivor is stronger than an eigenpair identity:

- positive/negative grade chambers equal the opposite Hermitian chiral chambers for every state;
- grade and Hermitian zero walls coincide;
- an arbitrary Hermitian reporter is antiunitary-blind iff its chiral coefficient is zero or the
  state lies on that common zero wall.

Paper proof and Lean formalization are complete in
`../3-formalized/fzz-p-grade-hermitianization.md`.

## Remaining route burden

Do not spend further effort inventing a second `2×2` source-side chiral reporter.  The live FZZ-P
burden is genuinely beyond this block: derive from interacting FZZ/GFZZ dynamics that parity-Mellin
divisor modes land in, or obey matching across, the source-defined chiral chamber.  The existing
endpoint shows that universal reflected-crossing matching is equivalent to RH.

## Log

- 2026-08-28 — Premise retired after exact universal Hermitianization theorem; positive survivor
  formalized before retirement.
