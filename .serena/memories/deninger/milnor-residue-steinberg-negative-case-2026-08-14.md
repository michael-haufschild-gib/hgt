# Milnor residue: the `v(a) < 0` Steinberg case in positive degree — state and diagnostics

Date: 2026-08-14. Companion to `deninger/milnor-residue-programme-2026-08-14`.

## Already proved and in the tree (all green, axioms `propext, Classical.choice, Quot.sound`)

`HTGeometry/MilnorKResidueSteinberg.lean`
- `mulSymbol_class`, `mulSymbol_comp_class`, `mulSymbol_one_eq_zero`,
  `mulSymbol_add_self_neg_one`, `mulSymbol_neg_one_add_self_apply`,
  `zsmul_mulSymbol_neg_one_eq_zero`, **`zsmul_map_mulSymbol_neg_one_eq_zero`**,
  `exists_add_self_sq_sub_sign`, `neg_one_pow_eq_one_or`,
  `mulSymbol_comp_steinberg`, `mulSymbol_comp_neg_self`, `mulSymbol_comp_neg_one_anticomm`,
  `resStepHom_eq_zero`, `resStepHom_zero_apply_of_val_zero`,
  `resStepHom_succ_apply_of_val_zero`, **`resStepHom_steinberg_of_nonneg`**,
  `residueUnit_eq_neg_of_neg`, **`resStepHom_steinberg_of_neg_zero`**.

## The one remaining case: `resStepHom_steinberg_of_neg_succ` (degree `m+1`, `v(a) < 0`)

Paper proof (verified by hand). Write `α = D.val' a`, `t = (-1)^m`, `c = t*α`,
`E_j = mulSymbol (-1) j`, `B_j = mulSymbol b̄ j`, `A_j = mulSymbol ā j`, `x = p.1`, `y = p.2`.
Facts: `ā = -b̄` so `A_j = E_j + B_j`; `A_{j+1} ∘ B_j = 0`; hence `B_{j+1}(B_j z) = -E_{j+1}(B_j z)`;
anticommutativity `E_{j+1}(B_j z) = -B_{j+1}(E_j z)`; `hc : c * c = (d+d) + c` where
`d` comes from `exists_add_self_sq_sub_sign α (neg_one_pow_eq_one_or m)`.
After expansion the `ξ` component is
`(c + c) • B_{m+1}(E_m y) + (d + d) • E_{m+1} x + ((-d) + (-d)) • E_{m+1}(E_m y)`,
killed by `zsmul_map_mulSymbol_neg_one_eq_zero` (first term) and
`zsmul_mulSymbol_neg_one_eq_zero` (other two). The base component is `A_{m+2}(B_{m+1} x) = 0`.

## Lean diagnostics from the failed attempt (do not repeat these)

1. `eq_neg_of_add_eq_zero_left/right` argument order: from `h0 : E + B = 0`, the working step to
   `B = -E` is `(neg_eq_of_add_eq_zero_right h0).symm`. `rw [add_comm]` on that goal fails with a
   *motive is not type correct* error (it abstracts `mulSymbol (-1) (j+1)`, whose codomain index
   then becomes a metavariable).
2. The working `simp only` set for the expansion is
   `[AddMonoidHom.add_apply, map_add, map_zsmul, hp1, hp2, hBB m p.2, hanti m p.2, neg_mul,
     smul_add, smul_smul, neg_smul, hc]`
   with `hp1 : (-1)^(m+1) = -(-1)^m`, `hp2 : (-1)^(m+1+1) = (-1)^m`.
3. **`abel_nf` is the wrong finisher here**: it pushes the `zsmul`s *inside* the `mulSymbol`
   applications (goal becomes `mulSymbol (-1) (m+1) (-1 • c • p.1)`) and rewrites `-1` as `-1 • 1`,
   so neither even-multiple lemma matches afterwards. Next attempt should instead state the
   post-`simp` identity explicitly as a `have ... : <LHS> = (c+c) • … + (d+d) • … + ((-d)+(-d)) • …`
   proved by `abel`, then rewrite the three terms to `0`.
4. The `p` in the goal has type `MilnorKDeg k (m+1) × MilnorKDeg k (m+1-1)`; always `cases n` before
   `AddMonoidHom.ext`, then `show … ((p.1, p.2) : MilnorKDeg k (m+1) × MilnorKDeg k m) …` to get a
   syntactically usable pair.

A working copy of the failed attempt is not kept; the file in the tree is the last green version.
