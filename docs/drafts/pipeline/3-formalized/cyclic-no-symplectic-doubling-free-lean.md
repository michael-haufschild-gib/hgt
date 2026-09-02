# Doubling is free for symplectic self-adjointness; quadratic symbols are symmetric

- **ID:** SYMP-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** no-go closure of `5-failed/arithmetic-symplectic-descent.md`
- **Statement:** (i) any nondegenerate symmetric `K`-self-adjoint form on `V` doubles to a
  nondegenerate alternating `K ⊕ K`-self-adjoint form on `V × V`; (ii) a `{±1}`-valued skew
  pairing is symmetric. The complementary cyclic no-go (invariant forms on a cyclic module are
  symmetric; no symplectic self-adjoint structure on a cyclic space) is the corpus's
  `RHTower.SymplecticCyclicObstruction` (2026-07-11); a duplicate proved this pass was removed.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.HTGeometry.SymplecticDoublingFree` | `doubledForm`, `doubledForm_apply`, `doubledForm_isAlt`, `doubledForm_nondegenerate`, `doubledForm_selfAdjoint`, `exists_symplectic_selfAdjoint_doubled`, `symm_of_skew_units` |

Axioms: `propext, Classical.choice, Quot.sound` (subsets thereof).

## Log
- 2026-09-02 — created at stage 3; cyclic part deduplicated against `SymplecticCyclicObstruction`.
