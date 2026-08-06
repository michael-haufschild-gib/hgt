# Tame different exponent for an arbitrary monic polynomial (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **36**.
Continues [[research/eigenvolume_hypothesis_sharpness_2026_08_06]].

## `TameMonicDifferentExponent.lean`

- **`eq_eisensteinPoly_of_monic`** — every monic `g` equals
  `eisensteinPoly g.natDegree (fun i => g.coeff i)`, via
  `Polynomial.as_sum_range_C_mul_X_pow` + `Finset.sum_range_succ` + `Monic.coeff_natDegree`.
- **`addVal_eval_derivative_monic`**, `..._succ`, **`span_eval_derivative_monic`** — the exact tame
  different exponent `deg − 1` for **any** monic polynomial whose sub-leading coefficients have
  `addVal ≥ deg`.

## Why this is the right generalisation

The old statements were about the *constructed* shape `eisensteinPoly e c`.  Freeing them means the
result now applies to a polynomial that **arises** (e.g. as the minimal polynomial of a
uniformizer) rather than one written down.

The coefficient hypothesis `(deg : ℕ∞) ≤ addVal B (g.coeff i)` is **not** an artificial
strengthening of "Eisenstein": for a totally ramified extension `B/A` of index `e`, Eisenstein
means `v_A(c_i) ≥ 1`, which upstairs reads `v_B(c_i) ≥ e`.  Plain `v_B(c_i) ≥ 1` would be too weak —
the tail bound `v_B(c_i) + (i−1) ≥ i` does not exceed `e−1` for small `i`.

## What still separates this from the general tame statement

Only **monogenicity** of the extension (`B = A[x]` for a uniformizer `x`), which for complete DVRs
is standard but needs Hensel/completeness in Lean.  The polynomial *shape* is no longer a
restriction.

## Remaining for Theorem A

1. Monogenicity ⇒ the general tame different exponent.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
4. Corollary B: MMP.
