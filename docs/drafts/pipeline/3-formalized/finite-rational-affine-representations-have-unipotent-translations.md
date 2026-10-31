# Finite rational affine representations have unipotent translations

- **ID:** RATIONAL-AFFINE-TRANSLATION-UNIPOTENCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For every complex `d`-dimensional matrix representation `ρ` of `Aff(ℚ)` and every `b∈ℚ`, `(ρ(T_b)−I)^d=0`. No unitarity or continuity is required.

## Dependency-closed paper proof

The translation law gives `ρ(T_b)^k=ρ(T_(kb))`. The [finite affine trace law](../3-formalized/finite-rational-affine-unitary-representations-kill-translations.md) therefore gives `tr(ρ(T_b)^k)=d` for every nonnegative integer `k`.

Take a Schur triangularization `ρ(T_b)=UTU*`. Its diagonal entries have the same power sums as `d` copies of `1`. Power-sum Torelli identifies these multisets, so every diagonal entry of `T` equals `1`. The matrix `T−I` is strictly upper triangular; its `d`th power vanishes. Unitary conjugation gives `(ρ(T_b)−I)^d=0`.

The corpus supplies `exists_schur_triangulation`, `trace_pow_eq_sum_diag`, `powerSum_torelli`, and `StrictlyLowering.pow_eq_zero_of_strictlyUpper`. This is an algebraic strengthening of unitary rigidity, with no novelty claim.

## Scope

Finite-dimensional nonunitary components can carry only unipotent translation transport. The theorem does not construct such a component from a finite-index kernel, bound its mixed coefficients, or close O5.

## Lean certificate

Module: `GaloisForLFunctions/BiarithmeticGeometry/Affine/FiniteTranslationUnipotence.lean`.

- `finite_rational_affine_translation_pow`
- `finite_rational_affine_translation_unipotent`

Direct leaf check passed with `lake --old env lean`. Both transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Imported by the BiarithmeticGeometry umbrella.
