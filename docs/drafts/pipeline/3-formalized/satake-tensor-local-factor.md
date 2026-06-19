# Satake tensor local factor

- **ID:** satake-tensor-local-factor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/g4-over-fq-deligne-katz.md` §1, `../2-fully-proven/c6-specialization-functors.md` §2, and the function-field `⊗`/tensor-of-sheaves recovery; Lean file `formal/GaloisForLFunctions/SatakeTensor.lean`
- **Statement:** For finite Satake parameter lists `alpha` and `beta`, the tensor product has pairwise-product parameters `alpha_i beta_j`; the diagonal Kronecker product has those entries, and the local factor is the double product over all pairwise products.

## Goal
This banks the exact finite diagonal Satake algebra behind the `⊗` part of the G4/C6 function-field recovery. It does not formalize automorphic Rankin-Selberg theory, tensor products of sheaves, Deligne-Katz monodromy, diagonalizability for arbitrary operators, analytic continuation, or global functoriality.

## Paper Proof
Let `A = diag(alpha_i)` and `B = diag(beta_j)`. The Kronecker product satisfies
```
(A ⊗ B)_{(i,j),(i',j')} = A_{i,i'} B_{j,j'}.
```
Since `A` and `B` are diagonal, this entry is zero unless `i=i'` and `j=j'`; on the diagonal it is
`alpha_i beta_j`. Hence
```
A ⊗ B = diag((i,j) -> alpha_i beta_j).
```
Thus the tensor-product Satake parameters are exactly the pairwise products.

For the finite local factor
```
L_x(alpha) = prod_i (1 - alpha_i x)^{-1},
```
substituting the pairwise-product parameters gives
```
L_x(alpha tensor beta)
  = prod_(i,j) (1 - alpha_i beta_j x)^{-1}
  = prod_i prod_j (1 - alpha_i beta_j x)^{-1}.
```
The last equality is just the finite-product Fubini/reindexing identity.

## Gates
- [x] 0 -> 1  in-progress: exact finite Satake tensor-product skeleton extracted from the G4/C6 `⊗` recovery.
- [x] 1 -> 2  fully-proven: paper proof above, by diagonal Kronecker multiplication and finite-product reindexing.
- [x] 2 -> 3  formalized: Lean definitions/theorems `satakeTensorParameters`, `satakeLocalFactor`, `satakeTensor_diagonal`, and `satakeLocalFactor_tensor`; names checked by scratch file; `#print axioms` reports only standard mathlib axioms.
- [ ] 3 -> 4  publication-ready: cite as the finite local Satake tensor certificate inside the function-field G4/C6 recovery note.

## Log
- 2026-06-19 — Leaner split this exact finite Satake tensor/local-factor lemma from the broader function-field `⊗` recovery. The parent cards remain in `2-fully-proven` because the sheaf-level tensor functor, Deligne-Katz monodromy, global Rankin-Selberg/functoriality, and analytic layers are not fully Lean-formalized.
