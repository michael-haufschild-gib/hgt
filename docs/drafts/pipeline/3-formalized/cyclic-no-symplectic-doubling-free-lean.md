# No symplectic self-adjoint structure on a cyclic space; doubling is free; quadratic symbols are symmetric

- **ID:** SYMP-LEAN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** no-go closure of `5-failed/arithmetic-symplectic-descent.md`
- **Statement:** (i) on a nonzero space with a cyclic vector for `K`, every `K`-self-adjoint
  bilinear form is symmetric and no nondegenerate alternating one exists; equivalently a
  symplectically self-adjoint endomorphism has no cyclic vector; (ii) any nondegenerate
  symmetric `K`-self-adjoint form on `V` doubles to a nondegenerate alternating
  `K ⊕ K`-self-adjoint form on `V × V`; (iii) a `{±1}`-valued skew pairing is symmetric.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.HTGeometry.CyclicNoSymplecticSelfAdjoint` | `bilin_pow_comm`, `bilin_aeval_comm`, `IsCyclicVector`, `bilin_symm_of_cyclic`, `bilin_eq_zero_of_isAlt_of_cyclic`, `not_symplectic_selfAdjoint_of_cyclic`, `not_isCyclicVector_of_symplectic_selfAdjoint`, `doubledForm`, `doubledForm_isAlt`, `doubledForm_nondegenerate`, `doubledForm_selfAdjoint`, `exists_symplectic_selfAdjoint_doubled`, `symm_of_skew_units` |

Consumer: sharpens `RHTower.SymplecticMultiplicity` (Kramers doubles Jordan blocks, not only
multiplicities). Axioms: `propext, Classical.choice, Quot.sound`.

## Log
- 2026-09-02 — created at stage 3.
