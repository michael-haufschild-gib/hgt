# Growing Windows of Spec ℤ (GWZ) — programme card

- **ID:** GWZ
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0311/obstacles-summary.md §2.7 (also §2.4, §2.5.1, §2.6.1)
- **Statement:** the exact theory of growing windows: two-collar forms, kicks, canonical systems
  (Schur–Levinson on the lattice), ground states, zero modes and margins along the window tower.

## Goal
Answer the §2.7 questions by Lean theorems. Folder `formal/GaloisForLFunctions/GrowingWindowsOfSpecZ/`,
umbrella `GrowingWindowsOfSpecZ.lean` (wire into `MainTheorems.lean`), README there.
WTZ, DZG, CWS, ACT, F1/F2 cards are owned by other agents: import, never edit.

## Plan
1. Two-collar calculus on `weilQuad`: interior tests, collar locality of the kick, two-collar form
   (EReal infimum), kick law, stage criterion, `σ_A`-invariance, sector splitting by the collar
   reflection `R u = −A − ℓ − u`.
2. Abstract corner reduction (variational Schur complement, no inverses) for a symmetric bilinear
   form positive definite on an interior subspace, with an involution swapping two corners.
3. Lattice canonical system: Weil sequence of a bump, Toeplitz form, predictors, prediction errors,
   Schur parameters, Levinson law, kick law (newest datum enters `β_m` with coefficient 1),
   locality in the primes, RH ⇔ all lattice parameters in the open interval.
4. Degeneration: one-dimensional palindromic kernel at a first critical lattice length, both
   corners nonzero; continuum zero modes of definite `σ_A`-parity.
5. Margins: `E_m = E_0∏(1 − γ_k²)`; soft vs exact.

## Status
- README first draft written.

## Open
See README §7.
