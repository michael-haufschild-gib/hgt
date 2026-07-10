# Reflected Grid Ratio Center

- **ID:** reflected-grid-ratio-center
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** The canonical ratio center `n/(n+m)` on reflected grid collisions is carried by factor-swap to `1-center`, lies in the open strip, sends diagonal fixed collisions to `1/2`, and for `N ≥ 1` gives completed-carrier reflected charge parity with the finite-order side condition discharged.

## Goal

Discharge the geometric center-assignment hypotheses left by `ReflectedGridCompletedCharge.lean` using the divisor-antidiagonal collision data itself, then discharge finite local order for `completedGN N` at those real ratio centers when `N ≥ 1`. This reduces the completed reflected-grid charge bridge to the physical carrier reduction and any remaining off-grid event accounting.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, consumes reflected grid collisions and the completed-carrier center-swap theorem
- [x] 1 → 2  fully-proven: ratio-center swap, strip, diagonal fixed-point geometry, and real-axis nonvanishing of `completedGN N` for `N ≥ 1`
- [x] 2 → 3  formalized: Lean theorems `RHTower.reflectedGridRatioCenter_swap`, `RHTower.reflectedGridRatioCenter_strip`, `RHTower.reflectedGridRatioCenter_diag`, `RHTower.completedGN_orderAt_ofReal_ne_top`, `RHTower.reflectedGridCompletedCharge_finite_of_ratio_center`, `RHTower.reflectedGridCompletedCharge_even_of_ratio_center_of_one_le`, and `RHTower.reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center_of_one_le`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Define the real ratio center of a collision `(n,m)` as `n/(n+m)` and coerce it to the complex plane. Positivity of both divisor-antidiagonal factors gives `0<center<1`; algebra gives the swap law `m/(m+n)=1-n/(n+m)`; and the diagonal case gives `n/(n+n)=1/2`. On real strip points, the Dirichlet block is a positive real sum for `N ≥ 1`, `zetaChi` has positive real value, and the archimedean factor is nonzero, so `completedGN N` is nonzero and the local order is zero. Feeding those facts into `reflectedGridCompletedCharge_even_of_center_swap` yields the canonical-center parity theorem without a finite-order hypothesis beyond `N ≥ 1`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedGridCenter.lean`; umbrella import and generated API/overview updated.
