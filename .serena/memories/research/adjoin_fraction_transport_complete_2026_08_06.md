# Fraction-field transport complete (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Extension of module 46,
`AdjoinFractionTransport.lean`.  See [[research/adjoin_fraction_transport_2026_08_06]].

## Added

**`adjoin_fraction_eq_top`** — for `IsFractionRing B L`, `x : B` with
`IsAlgebraic K (algebraMap B L x)` and `Algebra.adjoin A {x} = ⊤`:

    Algebra.adjoin K {algebraMap B L x} = ⊤

Route: `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` identifies the subalgebra with
the intermediate field `K⟮x⟯`, which is closed under division; `IsFractionRing.div_surjective`
writes any `z : L` as a ratio of images of `B`, both in the adjoin by
`range_le_adjoin_of_adjoin_eq_top`.

## Both inputs of mathlib's `conductor_mul_differentIdeal` are now available

    conductor A x * differentIdeal A B = span {aeval x (derivative (minpoly A x))}

- `conductor A x = ⊤` — `conductor_eq_top_of_uniformizer` (module 45).
- `Algebra.adjoin K {algebraMap B L x} = ⊤` — this module.

So the conclusion reads `differentIdeal A B = span {f'(x)}`, and with the tame computation
(`span_eval_derivative_of_monic_uniformizer_root`, module 41) the different is
`(maximalIdeal B)^(e−1)`.  **Assembling that is the next step** — it needs the Dedekind/
`IsIntegralClosure` instance bundle that `conductor_mul_differentIdeal` carries, plus identifying
`minpoly` with the monic relation.

## mathlib-version notes

- `IntermediateField.adjoin_simple_toSubalgebra_of_integral` is **deprecated** (2025-11-24) in
  favour of `..._of_isAlgebraic`; using the old name would fail the warning-free gate.
- Correct import path: `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`.

## Remaining for Theorem A

1. Assemble the different statement (instance bundle + `minpoly` identification).
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
