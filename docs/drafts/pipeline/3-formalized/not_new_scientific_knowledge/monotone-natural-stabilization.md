# Monotone natural stabilization

- **ID:** monotone-natural-stabilization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/holonomicity-limit-nonclosure.md` §2 corollary
- **Statement:** A monotone bounded sequence of natural numbers is eventually constant.

## Goal
This banks the integer-valued stabilization step used after the directed-sup corank identity in the holonomicity-limit card. It does not formalize the directed-sup corank identity, G3 holonomicity implication, or the comparison-functor non-reconstruction theorem.

## Paper Proof
Let `c_n` be monotone nondecreasing and bounded above by `B`. Since the values lie in `Nat`, argue by
induction on `B`. If `B=0`, every `c_n=0`, so the sequence is constant. For `B+1`, either some `N` satisfies
`c_N=B+1`; then monotonicity and the upper bound force `c_n=B+1=c_N` for all `n>=N`. Otherwise no value is
`B+1`, so every `c_n<=B`, and the induction hypothesis gives eventual constancy.

## Gates
- [x] 0 -> 1  in-progress: exact integer-valued stabilization step extracted from the corank-tower argument.
- [x] 1 -> 2  fully-proven: paper proof above, by induction on a natural-number upper bound.
- [x] 2 -> 3  formalized: Lean theorem `monotoneNat_eventually_constant_of_bddAbove` in `formal/GaloisForLFunctions/HTGeometry/HolonomicityLimit.lean`; name checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal certificate for the stabilization corollary.

## Log
- 2026-06-19 — Leaner split this exact stabilization lemma from `holonomicity-limit-nonclosure`. The parent card remains in `2-fully-proven` because the directed-sup corank identity, G3 implication, and comparison-functor theorem are not fully Lean-formalized.

