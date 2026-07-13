# Two-prime gluing witness

- **ID:** two-prime-gluing-witness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/c3-gluing-invariants-bridge.md` part (a)
- **Statement:** Two explicit pairs of `2 x 2` rational matrices have identical per-prime conjugacy data but are not jointly simultaneously conjugate, as witnessed by the word trace.

## Goal
This banks the concrete finite witness that joint gluing data is strictly finer than per-prime data. It does not formalize the Procesi/Artin invariant-theory generation or the reduction of native C3 content to C5-star.

## Paper Proof
Let
`A2=[[1,1],[0,1]]`, `A3=[[1,0],[1,1]]`, `H=diag(2,1)`, and
`B2=A2`, `B3=H A3 H^{-1}=[[1,0],[1/2,1]]`.

The per-prime classes agree because `B2=A2` and `B3` is conjugate to `A3`. But
`tr(A2 A3)=3`, while `tr(B2 B3)=5/2`.

If a single simultaneous conjugacy carried `(A2,A3)` to `(B2,B3)`, then cyclicity of trace would force
`tr(A2 A3)=tr(B2 B3)`, contradicting `3 != 5/2`. Hence the joint class is strictly finer than the pair of per-prime classes.

## Gates
- [x] 0 -> 1  in-progress: explicit two-prime matrix witness extracted.
- [x] 1 -> 2  fully-proven: paper proof above, using matrix multiplication and trace cyclicity.
- [x] 2 -> 3  formalized: Lean theorem `gluing_per_prime_same_but_joint_distinct` and supporting theorems in `formal/GaloisForLFunctions/RHTower/GluingWitness.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the concrete witness in the C3 gluing note.

## Log
- 2026-06-19 — Leaner split the exact finite gluing witness from `c3-gluing-invariants-bridge`. The parent card remains in `2-fully-proven` because the character-variety import and C5-star reduction are not fully Lean-formalized.
