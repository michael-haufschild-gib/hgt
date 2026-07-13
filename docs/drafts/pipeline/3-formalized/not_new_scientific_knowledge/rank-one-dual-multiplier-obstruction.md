# Rank-one dual multiplier obstruction

- **ID:** rank-one-dual-multiplier-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/orthogonality-meta-theorem.md` section 1
- **Statement:** In a rank-one multiplier system, the dual multiplier is the inverse multiplier. A multiplier
  is equal to its dual exactly when its square is one, so any multiplier with square not equal to one cannot
  be self-dual.

## Goal
This banks the exact group-algebra core of the polarization lemma. It does not formalize the Tannakian
category, the Source-B invariant scope, Weil positivity, the functional-equation polarization, or RH.

## Paper Proof
Let `g` be a rank-one multiplier and let its dual multiplier be `g_dual`. The rank-one pairing condition is
`g * g_dual = 1`, hence `g_dual = g^{-1}`. Therefore self-duality is the equation `g^{-1} = g`. Multiplying
by `g` gives `g^2 = 1`; conversely, if `g^2 = 1`, then `g^{-1} = g`. Thus a multiplier with `g^2 != 1` cannot
be self-dual.

## Gates
- [x] 0 -> 1  in-progress: rank-one multiplier algebra extracted from the polarization lemma.
- [x] 1 -> 2  fully-proven: paper proof above by the group inverse law.
- [x] 2 -> 3  formalized: Lean definition/theorems `rankOneDualMultiplier`,
  `rankOneDualMultiplier_mul`, `rankOneDualMultiplier_mul_left`,
  `rankOne_selfDualMultiplier_iff_sq_eq_one`, and `rankOne_noSelfDualMultiplier_of_sq_ne_one` in
  `formal/GaloisForLFunctions/HTGeometry/RankOneDuality.lean`; scratch `#check`/`#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the finite algebraic certificate for the rank-one obstruction in
  the orthogonality meta-theorem.

## Log
- 2026-06-19 - Leaner split this exact rank-one group algebra from `orthogonality-meta-theorem` section 1.
  The parent card remains in `2-fully-proven` because its categorical Source-B theorem, Weil-positivity
  import wrapper, and function-field polarization assembly are not fully Lean-formalized.
