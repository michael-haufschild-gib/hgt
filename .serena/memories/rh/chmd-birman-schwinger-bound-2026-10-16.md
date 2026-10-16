# CHMD: Birman–Schwinger upper bound (2026-10-16) — primitive bound states ≤ 2·#off-line zeros

RH goal ACTIVE. Contribution 7 of this lane. STATUS row MUST-1553.
Card: docs/drafts/pipeline/3-formalized/chmd-birman-schwinger-bound-2026-10-16.md.
Module `RHTower/CHMDBirmanSchwingerBound` (ns RHTower.CHMDPolar), 31 declarations, standard axioms, wired.

## Theorems (unconditional)
- `offLineZeros := {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1/2}`; `zeroDefect f ρ := paperFT f (γ_ρ) − paperFT f (conj γ_ρ)`
  (= 0 on-line via `ZeroSide.gammaOf_of_re_eq_half`); `defectWeight f ρ := (m_ρ/2)‖zeroDefect‖²`.
- `neg_defectWeight_le_re_Wsummand : −defectWeight f ρ ≤ Re (Wsummand f f ρ)` (from `Complex.normSq_sub`).
- `re_W_add_defect_nonneg (hfin) (hf : C²) (hfc) : 0 ≤ Re (W f f) + Σ_{ρ ∈ offLineFinset hfin} defectWeight f ρ`
  (uses corpus `WeilConditional.summable_Wsummand`, `Complex.re_tsum`, `tsum_eq_sum`).
- `rieszLift_sum`; `weilForm_rieszLift_sum_le` (negative definite on span of Riesz lifts of orthonormal primitive
  eigenvectors above 1/2, via `Orthonormal.inner_sum`).
- `weilBilin` with `weilForm p = weilBilin p p`, `abs_weilBilin_le`, `abs_weilForm_sub_le` (Lipschitz of the quadratic form).
- `exists_compactTests_negative_definite`: negative definiteness persists under perturbation to compact tests.
- `card_le_two_mul_offLine_of_negative_definite`: rank argument with `L : (Fin k → ℝ) →ₗ (offLineFinset → ℂ)`,
  `LinearMap.finrank_le_finrank_of_injective`, `Module.finrank_pi_fintype`, `Complex.finrank_real_complex`.
- **`orthonormal_primitive_bound_states_le (hfin) (he : Orthonormal) (hμ : ∀ i, 1/2 < μ i) (hprim) (heig) : k ≤ 2 * offLineZeros.ncard`**.

## Picture
With MUST-1551/1552: bound states above 1/2 exist iff off-line zeros exist, and their total multiplicity is ≤ 2·#off-line zeros.
Upper half of Birman–Schwinger. Next: lower half (deep zero ⇒ negative-definite subspace; corpus
`IsolatedDeepZeroWeilDetection.Wsummand_modulatedTest_deep_pair`), sharpen factor 2 by parity, drop finiteness.

## Lean traps
- `open Classical in` must precede the docstring of a `def` that needs `DecidablePred`.
- `congrArg (fun t => m * t) h` may already be beta-reduced: `simp only at h` then errors ("no progress"); state the `have` explicitly.
- `map_smul'` for `fun c ρ => Σ (c i : ℂ) * a i ρ`: `simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Finset.smul_sum, Complex.real_smul, mul_assoc]`.
- `integral_finset_sum` deprecated → `integral_finsetSum`.
- Sources of `Σ cᵢ • qᵢ`: `show sourceMap (Σ …) = Σ cᵢ • sourceMap (qᵢ)` + `map_sum`/`map_smul`; coeFn of Lp sums by `Finset.induction_on` with `Lp.coeFn_add/smul/zero`.
