# Degree of the minimal polynomial of a uniformizer (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **49**.
Continues [[research/uniformizer_power_basis_2026_08_06]].

## `MinpolyDegreeUniformizer.lean`

**`natDegree_minpoly_eq_ramificationIndex`** — given a monic relation `g` of degree `e` satisfied by
a uniformizer `x`, `(minpoly A x).natDegree = e`.

- `≤` — `minpoly.min` + `Polynomial.natDegree_le_natDegree`.
- `≥` — if the degree were `< e`, `Polynomial.aeval_eq_sum_range` turns `minpoly.aeval` into a
  vanishing `Fin e`-indexed combination of powers, and `linearIndependent_pow` (module 48) forces
  the leading coefficient to be `0`, contradicting monicity.

This is the last identification the different needed: the tame computation
(`span_eval_derivative_of_monic_uniformizer_root`, module 41) applies to a monic polynomial of
degree exactly `e`, and the minimal polynomial is one.

## Lean notes (v4.32.2)

- **`push_neg` is deprecated** — use `push Not at h`.  It fails the warning-free gate.
- `Fin.sum_univ_eq_sum_range` needs the summand function supplied **explicitly**
  (`(fun j => …) e`); higher-order unification will not find it.
- `Finset.range_subset.mpr` did not resolve to the expected `≤` form here; proving the inclusion by
  `intro j hj; simp only [Finset.mem_range] at hj ⊢; omega` is robust.

## Remaining for Theorem A

1. Assemble `differentIdeal A B = (maximalIdeal B)^(e−1)` from modules 41 + 47 + 49.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
