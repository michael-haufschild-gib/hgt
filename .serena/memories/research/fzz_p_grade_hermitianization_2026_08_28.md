# FZZ-P grade Hermitianization — 2026-08-28

## New theorem

For every real `beta` and `u : ℂ×ℂ`,

`2 * Im(fzz grade crossing beta u) = -fzzKreinQAt beta * Re(unit chiral Hermitian reporter u)`.

At positive beta, grade and Hermitian chiral chambers have exactly opposite signs and identical
zero wall.  Arbitrary Hermitian antiunitary odd part is `2c` times unit chiral reporter, yielding:

`H(a,b,c,d)(u)=H(a,b,c,d)(conj u) ↔ c=0 ∨ Im(grade crossing beta u)=0`.

## Route consequence

Separate finite-block chiral producer is redundant: literal FZZ source grade already realizes unique
Hermitian chiral reporter.  Remaining route core is full interacting FZZ/GFZZ divisor
incidence/landing, not finite-block source orientation.

## Files

- `formal/GaloisForLFunctions/RHTower/FZZCigarParityGradeHermitianization.lean`
- `docs/drafts/pipeline/3-formalized/fzz-p-grade-hermitianization.md`
- `docs/drafts/pipeline/5-failed/fzz-p-separate-finite-block-chiral-producer.md`
- umbrella import in `formal/GaloisForLFunctions/RHTower.lean`

## Verification

- direct Lean passed
- targeted module build passed
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- literature/corpus searches found no exact collision
- frontier map untouched
