# Rank-one diagonal kernel splitting

- **ID:** rank-one-diagonal-kernel-splitting
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multi-q-shafarevich-gluing-group.md` R1
- **Statement:** In a joint eigenbasis, the kernel of the product of two diagonal scalar multipliers is the sum of the two individual kernels, in the explicit coordinatewise decomposition form used for the rank-one `Ш` vanishing computation.

## Goal
This banks the exact semisimple linear-algebra core behind the rank-one abelian vanishing step for the multi-`q` Shafarevich gluing group. It does not formalize nonabelian `H^1`, character varieties, Procesi/Artin invariant theory, or the C5-star coboundary-regularity layer.

## Paper Proof
Let diagonal operators act coordinatewise by scalars `a_i` and `b_i`. Suppose `a_i b_i x_i = 0` for every
coordinate `i`. Define
`y_i = x_i` and `z_i = 0` when `a_i = 0`, and define `y_i = 0` and `z_i = x_i` when `a_i != 0`.
Then `x=y+z`, `a_i y_i=0` for all `i`, and if `a_i != 0`, the equation `a_i b_i x_i=0` forces
`b_i x_i=0`, so `b_i z_i=0`; if `a_i=0`, then `z_i=0`. Thus every vector in `ker(AB)` lies in
`ker(A)+ker(B)`.

Conversely, if `x=y+z` with `a_i y_i=0` and `b_i z_i=0`, then
`a_i b_i x_i = b_i(a_i y_i)+a_i(b_i z_i)=0` coordinatewise. Hence `ker(AB)=ker(A)+ker(B)` in this diagonal
setting.

## Gates
- [x] 0 -> 1  in-progress: exact joint-eigenbasis kernel statement extracted from the Shafarevich gluing R1 computation.
- [x] 1 -> 2  fully-proven: paper proof above, using coordinatewise splitting and cancellation in a field.
- [x] 2 -> 3  formalized: Lean theorem `diagonalKer_mul_eq_sum_ker` in `formal/GaloisForLFunctions/ShafarevichGluing.lean`; name checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the formal certificate for the rank-one semisimple vanishing lemma.

## Log
- 2026-06-19 — Leaner split this exact diagonal-kernel lemma from `multi-q-shafarevich-gluing-group`. The parent card remains in `2-fully-proven` because nonabelian `H^1`, character-variety/Procesi input, and C5-star regularity are not fully Lean-formalized.

