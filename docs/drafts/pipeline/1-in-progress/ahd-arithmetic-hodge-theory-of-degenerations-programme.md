# Arithmetic Hodge Theory of Degenerations (AHD) — programme card

- **ID:** AHD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7
- **Statement:** RH as a structure theorem for the degeneration of the scaling surface along the
  resolution axis; positivity carried through the critical curve by a count, an inherited
  polarization or an integer with a structural bound; one global gluing; calibrations.

## Goal
Develop the field of §2.7: answer its questions by Lean theorems, build its tools. Folder
`formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/`, umbrella
`ArithmeticHodgeTheoryOfDegenerations.lean`, README there.

## Plan
1. Zero side of the complete family: translation law of Weil summands; packet Dirichlet
   polynomials.
2. Conductor Dirichlet polynomials: Möbius splitting, horizon term `[e=1]N^s/s`, constant term
   `ζ(1−s)J_s(e)`, remainder `O(|s| σ_{Re s}(e) N^{Re s−1})`.
3. Zero ledger of fixed packets: rank one at the pole, weight `m_ρ/(ρ(1−ρ))`, positive per
   reflection quadruple.
4. Zero ledger of horizon blocks: Weil summand of the synthesized test.
5. Critical-multiple calculus.
6. Count: prime atoms in the jump measure; creation potential.
7. Gluing index theorem; calibration (ledger is configuration-general).

## Open
see README §9.
