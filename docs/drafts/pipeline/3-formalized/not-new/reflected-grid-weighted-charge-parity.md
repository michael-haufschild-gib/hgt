# Reflected Grid Weighted Charge Parity

- **ID:** reflected-grid-weighted-charge-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** A swap-invariant weight on the reflected saddle/grid collision carrier has even total charge whenever the fixed diagonal weights are even; equivalently, its level-two deck reduction is trivial.

## Goal

Upgrade unit collision-count parity to physical weighted charge. The unit carrier has a square fixed-point obstruction, but a real reflection charge is weighted; if the square fixed point carries even weight, the obstruction disappears.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, follows the `ReflectedGridParity` square-fixed-point classification
- [x] 1 → 2  fully-proven: split the divisor antidiagonal into fixed and nonfixed parts; pair the nonfixed part by factor swap; consume even fixed weights
- [x] 2 → 3  formalized: Lean theorems `RHTower.reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed`, `RHTower.reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_even_fixed`, and `RHTower.reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `q` be the collision weight. Split `reflectedGridCollisions C` into the diagonal and non-diagonal parts. The non-diagonal part has a fixed-point-free involution `(n,m)↦(m,n)`, and `q` is invariant on its orbits. The diagonal contribution is even by hypothesis; in the square case the diagonal is the singleton `(r,r)`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedGridCharge.lean`; umbrella import and generated API/overview updated.
