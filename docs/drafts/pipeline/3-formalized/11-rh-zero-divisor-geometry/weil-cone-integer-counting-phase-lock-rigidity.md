# Integer counting (a.e. phase lock) forces Λ and RH, with no continuation assumed

- **ID:** weil-cone-integer-counting
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** krein-producer-loops L303 (paper), L307 (Lean)
- **Statement:** If a full-cone Weil-positive `lam` has boundary measure `μ_lam` with integer mass on `(a,b]` for all `a < b` in a set of full Lebesgue measure, and no mass on `(−1,1)`, then `lam(n) = Λ(n)` for `n ≥ 2` and RH holds.

## Goal
Closes the phase-locked producer door without any analytic-continuation or boundary-regularity hypothesis.
- Along the line, `π·μ_lam((0,t])` is the argument of `E = s(s−1)Γ_ℝ(s)exp(Σ lam(n)n^{−s}/log n)`, up to an additive constant.
- So "the completed exponential has constant phase mod π a.e. on the critical line" is exactly integer counting a.e.
- An integer-frequency object whose phase is locked to ζ's archimedean factor and that has no zeros in `σ > ½` therefore exists iff RH, and it is then `ζ`.
- Natural boundaries give no escape. The fractional lock `Γ_ℝ^k` gives atoms in `(1/k)ℕ`, i.e. the twin door RTE_k.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (L303 paper proof)
- [x] 2 → 3  formalized: `RHTower.WeilSpectral.vonMangoldt_and_riemannHypothesis_of_integer_counting`. Built with `lake build --old`; axioms `propext, Classical.choice, Quot.sound`.
- [ ] 3 → 4  (no stage 4 by directive)

## Approach (as formalized, module `RHTower/WeilBoundaryIntegerCountingRigidity`)
1. `exists_isolating_interval`: integer counting on a full-measure (hence dense) set makes every point isolated, with `μ(I∖{x}) = 0` and `μ{x} ∈ ℕ`.
   - Shrinking intervals `(x ± 1/(n+1))`.
   - Naturals in `[μ{x}, μ{x}+½)` coincide.
   - Continuity from above.
2. `atoms_countable_and_compl_null`: by Lindelöf (`isOpen_iUnion_countable`), the non-atoms are null and the atoms are countable.
3. `weilFunction_conj` and `weilContinuation_conj`: `Φ(s̄) = conj Φ(s)` on `Re s > ½`, by the identity theorem from `Re s > 1`. Then `boundaryMeasure_singleton_neg` gives atom symmetry via atom extraction.
4. Reindex the positive atoms along `Encodable.decode₂`. Then `W_lam(f⋆f̃) = Σ_j m_j(|f̂(t_j)|² + |f̂(−t_j)|²)`, and `converse_explicit_formula` (MUST-642) concludes.

Reusable lemmas:
- `boundaryMeasure_Ioo_ne_top`: local finiteness.
- `lintegral_inv_one_add_sq_lt_top`.
- `tsum_decode₂_eq`, `summable_decode₂_iff`.
- `boundaryMeasure_singleton_neg`: atom symmetry, new to the corpus.

## Log
- 2026-10-03 — L303 paper proof; Lean module built (495 lines, standard axioms); umbrella `RHTower.lean` wired after `WeilFullConeAtomExtraction`.
- 2026-10-03 — Fractional companion `exists_realRooted_twin_of_fractional_counting` (MUST-670, module `RHTower/WeilBoundaryFractionalCountingTwin`, 455 lines, standard axioms). Counting in `(1/k)ℤ` a.e. ⇒ `G^k` extends to an entire symmetric function whose zeros all lie on the line (a real-rooted twin in `V_k`). Door 2 is exactly RTE_k, formally.
