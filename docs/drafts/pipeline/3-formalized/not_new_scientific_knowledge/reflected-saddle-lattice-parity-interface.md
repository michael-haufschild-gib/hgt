# Reflected Saddle Lattice Parity Interface

- **ID:** reflected-saddle-lattice-parity-interface
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** For the negative Fourier reflected phase `-2π(k+1)x + T log x`, the stationary point is exactly `T/(2π(k+1))`, the curvature is `-T/x²` and independent of `k`, and an even finite saddle-mode count supplies `LedgerFluxPaired` for the unit event list.

## Goal

Name the constraint geometry behind the reflected AFE block in Lean and expose the exact parity interface consumed by the event ledger. This does not prove the physical saddle-mode count is even; it isolates the remaining charge-bridge burden as that evenness or an equivalent boundary datum.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, R7 reflected-block route note
- [x] 1 → 2  fully-proven: calculus proof of the saddle and curvature identities plus finite event-list parity
- [x] 2 → 3  formalized: Lean theorems `RHTower.reflectedPhaseDeriv_eq_zero_iff`, `RHTower.reflectedPhaseSecond_independent`, `RHTower.reflectedSaddleFluxPaired_of_even`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Differentiate the reflected phase directly. The equation `-2π(k+1) + T/x = 0` has the unique positive solution `x = T/(2π(k+1))`, and differentiating once more removes the Fourier mode entirely. A finite cutoff set of saddles in an interval carries one unit event per mode; if its cardinality is even, the existing consecutive-pairing construction gives `LedgerFluxPaired`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedSaddleLattice.lean`; umbrella import and generated API/overview updated.
