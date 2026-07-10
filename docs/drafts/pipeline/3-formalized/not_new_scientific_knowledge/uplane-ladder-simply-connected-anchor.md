# U-plane ladder on simply connected slit-plane regions

- **ID:** uplane-ladder-simply-connected-anchor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../rh-monodromy-weight-mismatch/105-constraint-front-plan.md §W5
- **Statement:** For any open simply connected preconnected region `U ⊆ slitPlane` with one nonzero
  `xiDescent` base value, independent dyadic roots, a coherent dyadic Kummer tower, and zero-freeness
  of `xiDescent` on `U` are equivalent; if `U` contains the positive real anchor `(9:ℂ)/4`, the base
  nonvanishing hypothesis is discharged.

## Goal

Turns the conservation program's u-plane anchoring option into a reusable formal interface.  The
local box bookkeeping can now consume a global slit-plane-region statement: roots and coherent tower
data are equivalent to zero-freeness on the chosen region, with the far-field u-plane anchor certified
once.  This is infrastructure for OC3(c), not a native C5 theorem.

## Lean Surface

- File: `formal/GaloisForLFunctions/RHTower/UPlaneLadder.lean`.
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`.
- Generic preconnected-domain layer:
  `nonvanishing_of_exists_roots_all_two_powers_preconnected`,
  `coherentTower_of_exists_roots_all_two_powers_preconnected`,
  `coherentTower_iff_exists_roots_all_two_powers_preconnected`.
- `xiDescent` region layer:
  `xiDescent_root_of_nonvanishing_on`,
  `xiDescent_twoPower_root_of_nonvanishing_on`,
  `xiDescent_coherentTower_iff_nonvanishing_on`,
  `xiDescent_coherentTower_iff_roots_all_two_powers_on`,
  `xiDescent_roots_all_two_powers_iff_nonvanishing_on`.
- Far-anchor layer:
  `xiDescent_far_anchor_mem_slitPlane`,
  `xiDescent_far_anchor_ne_zero`,
  `xiDescent_coherentTower_iff_nonvanishing_on_far_anchor`,
  `xiDescent_coherentTower_iff_roots_all_two_powers_on_far_anchor`,
  `xiDescent_roots_all_two_powers_iff_nonvanishing_on_far_anchor`,
  `xiDescent_coherentTower_of_RH_on_far_anchor`,
  `xiDescent_roots_all_two_powers_of_RH_on_far_anchor`.

## Gates
- [x] 0 → 1  in-progress: W5 interface extracted from the constraint-front plan
- [x] 1 → 2  fully-proven: proof carried directly in Lean, no open dependency
- [x] 2 → 3  formalized: module and umbrella compile; axiom set `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready

## Verification

- `lake env lean GaloisForLFunctions/RHTower/UPlaneLadder.lean`
- `lake env lean GaloisForLFunctions/RHTower.lean`
- `lake build GaloisForLFunctions.RHTower`
- `/tmp/uplane_ladder_axioms.lean` with `#print axioms` for the W5 capstones:
  `[propext, Classical.choice, Quot.sound]`
- `scripts/formal_tools.py index`
- `scripts/formal_tools.py lint --check-generated`

## Log

- 2026-07-06 — created directly in `3-formalized/not-new` after formalizing W5; generated indexes
  refreshed and lint passed.
