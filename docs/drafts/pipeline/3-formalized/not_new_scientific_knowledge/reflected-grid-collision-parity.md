# Reflected Grid Collision Parity

- **ID:** reflected-grid-collision-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** At normalized height `T=2πC`, a reflected saddle hits integer grid point `m` exactly when `(k+1)m=C`; the ordered collision carrier has odd cardinality exactly when `C` is a positive square, and otherwise its unit event list supplies `LedgerFluxPaired`.

## Goal

Move the R7 saddle-lattice parity question from a vague charge metaphor to a sharp finite arithmetic carrier. The reflection on the saddle/grid collision carrier is the divisor-antidiagonal swap; all nonfixed collisions pair, and the only possible unpaired charge is the square fixed point.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, follows the `ReflectedSaddleLattice` interface
- [x] 1 → 2  fully-proven: factor-swap involution on `Nat.divisorsAntidiagonal`, singleton square fixed locus, parity partition
- [x] 2 → 3  formalized: Lean theorems `RHTower.reflectedGridCollision_iff_saddle_grid`, `RHTower.reflectedGridCollisions_odd_iff_pos_square`, `RHTower.reflectedGridCollisionFluxPaired_of_no_pos_square`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Normalize the height as `T=2πC`, so `T/(2π(k+1))=m` is equivalent to `(k+1)m=C`. The finite collision carrier is `C.divisorsAntidiagonal`; its reflection is `(n,m)↦(m,n)`. The nonfixed part carries a fixed-point-free involution, while the fixed part is the singleton `(r,r)` exactly when `C=r²` with `r>0`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedGridParity.lean`; umbrella import and generated API/overview updated.
