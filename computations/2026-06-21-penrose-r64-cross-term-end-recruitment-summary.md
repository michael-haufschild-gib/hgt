# R64 — cross-term endpoint recruitment

**Verdict:** DEAD END / existing archimedean-prime cross-term warning.

## Setup
- Seed RandomNode: `Metal ions, cofactors, lipids, or post-translational modifications can reshape the landscape and change apparent allosteric mechanisms`.
- STEP 1 cold list + STEP 2 rng `4`: topic `Prion-like conformational templating`.
- STEP 3 cold list + STEP 4 rng `5`: NODE `Fibril ends are usually the main sites of monomer recruitment and conversion`.
- Standing-order target pick: file rng `3` -> `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng `9` -> archimedean-prime cross-term.
- STEP 5 constraint: activity can live at the interface/end, not in the aggregate bulk.
- STEP 8 selected transfer by Levenshtein: `same bulk prime mass can have different weld conversion` (`47`).
- STEP 9 method rng `16` = minimal counterexample.
- STEP 11 method rng `2` = attack as false.

## Computation
Archive script: `computations/2026-06-21-penrose-r64-cross-term-end-recruitment.py`.

NODE validation:
- fixed aggregate mass `100`;
- recruitment rate scaled with number of fibril ends: `0.800` at 2 ends, `40.000` at 100 ends.

Target minimal counterexample:
- fixed `|A|=|P|=4`;
- relative phase changed `Re(A conj(P))` and `Delta`:
  - phase `0.00π`: cross `16.0000`, `Delta=-0.6931`;
  - phase `0.75π`: cross `-11.3137`, `Delta=0.2674`;
  - phase `0.99π`: cross `-15.9921`, `Delta=3.4605`.

## Attack-as-false
The scalar-bulk claim is false: `|A|` and `|P|` do not determine the weld. But this is exactly the existing cross-term/phase-carrier point.

## Reading
The action is at the Source A / Source B interface, not in scalar bulk amplitude. Correct but not new.
