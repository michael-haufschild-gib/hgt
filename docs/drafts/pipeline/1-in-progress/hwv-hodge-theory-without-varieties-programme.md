# Hodge theory without varieties over ℤ (HWV) — programme card

- **ID:** hwv-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7
- **Statement:** Build the arithmetic Kähler package on the divisibility–successor complex: links,
  Lefschetz operator, base point, local HR, transport, selection, calibration; prove each part or
  its exact boundary.

## Goal
A fourth producer type (exact local-to-global positivity with nondegeneracy) for Weil's form on
`v₁^⊥`. Lean folder `formal/GaloisForLFunctions/HodgeTheoryWithoutVarieties/` (16 modules), umbrella
`HodgeTheoryWithoutVarieties.lean` (wired into `MainTheorems.lean`), README there.

## Gates
- [x] 0 → 1  in-progress: README, questions fixed
- [x] 1 → 2  paper proofs of the pillars (all pillars are proved directly in Lean)
- [x] 2 → 3  formalized: 16 modules, each checked with `lake --old env lean`

## Status of the six review questions (answers in README §5)
- Links: stars (exact lower horizons); simplicial links split into towers.
- Lefschetz operator: trichotomy; overlap flow HL on HR locus ⇔ RH.
- Shell degree: RAPT repayment per conductor; exact shell balance on the coherent sector (zero in
  the mean); uniform joint payment open (Σ-3).
- Base point/path: exact transport; criterion ⇔ RH.
- Function-field model: commensurable degree lattice; Künneth gives gaps, not Weil positivity.
- Liouville: Liouville = HL; ⇔ RH along the overlap flow.

## Open (README §8)
- Top coprime stratum (successor/archimedean coupling of coprime atoms), level-independent.
- Local HR on shallow stars (d ≲ c).
- Quadratic invariant of the nerve refining the Mertens Euler characteristic.
- Successor and shell strata; layered Künneth for the complete family.

## Log
- 2026-11-01 — created; README first draft.
- 2026-11-01 — 11 modules formalized; README v2 with answers and pillars.
- 2026-11-01 — +5 modules: renormalized recursion, gcd stratification, shell balance, layers of a
  prime, sign gauge on deep stars.
