# Function-field degree-collapse core

- **ID:** function-field-degree-collapse-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/function-field-holonomicity-degeneration.md` §1
- **Statement:** If every function-field place multiplier is a power of one base and there is a degree-one place, then the relation lattice is the kernel of the finite-support degree map and the quotient has rank one.

## Goal
This banks the exact algebraic core of the function-field corank collapse. It does not formalize the G3 holonomicity implication, Lipshitz/Weil rationality imports, or the broader directed-sup corank comparison.

## Paper Proof
Let `V` be the place set with degree map `deg : V -> Z`. The finite-support degree map is
`m |-> sum_v m_v deg(v)`. The relation lattice for multipliers `q^{-deg(v)}` is exactly the kernel of this degree map: a finite product of powers has total exponent zero exactly when the displayed degree sum is zero.

If a degree-one place `v0` exists, then the degree map is surjective: any integer `z` is the degree of the finitely supported divisor `z[v0]`. By the first isomorphism theorem, the quotient of the finite-support lattice by the relation lattice is isomorphic to `Z`, hence has `Z`-rank one. This is the formal `corank(Lambda_ff)=1` computation.

## Gates
- [x] 0 -> 1  in-progress: degree-collapse core extracted from the broader function-field degeneration card.
- [x] 1 -> 2  fully-proven: paper proof above, by the kernel computation and first isomorphism theorem.
- [x] 2 -> 3  formalized: Lean theorems `ffDegreeMap_apply`, `ffRelationLattice_mem_iff`, `ffDegreeMap_surjective`, `ffDegreeMap_range_eq_top`, and `ffRelationLattice_corank_eq_one` in `formal/GaloisForLFunctions/RHTower/FunctionFieldDegeneration.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the algebraic collapse lemma in the function-field degeneration note.

## Log
- 2026-06-19 — Leaner split this exact degree-collapse core from `function-field-holonomicity-degeneration`. The parent card remains in `2-fully-proven` because the holonomicity/Weil rationality imports and the full #119 comparison are not fully Lean-formalized.
