# Frobenius torsion law: integral faithful Arakelov coordinates refute RH

- **ID:** F1-LEAN-TORSION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `5-failed/f1-frobenius-integrality-torsion-law.md` Theorems A, C
- **Statement:** if every Arakelov coordinate `w(ρ) = 1 − 1/ρ` of a zero of ξ is an algebraic
  integer and every Galois conjugate of such a coordinate is again the coordinate of a zero,
  then RH fails; with the chamber's contractive packets this is contradictory. If `p^ρ` is
  algebraic for one integer `p ≥ 2` and `ρ` is nonreal, `ρ` and `w(ρ)` are transcendental.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.FrobeniusTorsionLaw` | `exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one`, `exists_middle_totative`, `one_le_norm_one_sub_exp`, `exp_mem_rootSet_minpoly`, `norm_le_one_of_arakelovW_eq`, `xiZeros_infinite`, `XiArakelovFaithful`, `XiArakelovUnitary`, `xi_zero_re_eq_half_of_riemannHypothesis`, `xiArakelovUnitary_of_riemannHypothesis`, `not_xiArakelovIntegral_faithful_unitary`, `not_riemannHypothesis_of_xiArakelovIntegral_faithful`, `not_xiArakelovIntegral_contractive_faithful`, `not_isAlgebraic_of_nat_cpow_isAlgebraic`, `not_isAlgebraic_arakelovW_of_nat_cpow_isAlgebraic` |

Inputs: mathlib `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` (Kronecker),
`Polynomial.cyclotomic_eq_minpoly_rat`, `Complex.isPrimitiveRoot_iff`,
`Set.Infinite.exists_accPt_of_subset_isCompact`; corpus `XiArakelovCoordinatesIntegral`,
`XiArakelovConjugateRootsContractive`, `riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_conjugateRootsContractive`,
`arakelovW_injective`, `arakelovW_norm_one_iff_critical`, `isAlgebraic_rho_of_arakelovW`,
`gelfondSchneider_holds`, `exists_odd_order_line_zero_gt`, `xi_one_sub`. Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-02 — created at stage 3.
