# Function-field local-factor FE algebra

- **ID:** function-field-local-factor-fe-algebra
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/c6-specialization-functors.md` and the function-field FE ledger anchors
- **Statement:** If a Frobenius-eigenvalue multiset is closed under `omega -> q/omega`, then elementary symmetric coefficients satisfy the `q`-weighted FE relation and the local factor product is invariant under the same substitution.

## Goal
This banks the algebraic finite-multiset core of the function-field local-factor functional equation. It does not formalize purity, Weil II, Grothendieck cohomology, point counts, or the C6 functor construction.

## Paper Proof
For any finite multiset `S`, elementary symmetric functions are homogeneous under scaling:
`e_k(cS)=c^k e_k(S)`, since every `k`-fold product picks up one factor `c` from each selected element.

If `S` is closed under `omega -> q/omega`, then
`S = (S^{-1})` scaled by `q`. Homogeneity gives
`e_k(S)=q^k e_k(S^{-1})`, the coefficient-level `q`-weighted palindrome.

For the polynomial local factor, closure under the same multiset map gives
`prod_{omega in S} (1 - omega T) = prod_{omega in S} (1 - (q/omega) T)` by substituting the equal multiset.

## Gates
- [x] 0 -> 1  in-progress: finite-multiset FE algebra extracted.
- [x] 1 -> 2  fully-proven: paper proof above, using multiset closure and homogeneity of elementary symmetric functions.
- [x] 2 -> 3  formalized: Lean theorems `multiset_esymm_map_mul`, `functionField_esymm_FE`, and `functionField_localFactor_FE` in `formal/GaloisForLFunctions/FunctionFieldFE.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the algebraic FE lemma in the function-field border note.

## Log
- 2026-06-19 — Leaner split this exact local-factor FE algebra from the broader function-field/C6 material. The parent cards remain in `2-fully-proven` because their geometric imports and functor-level claims are not fully Lean-formalized.
