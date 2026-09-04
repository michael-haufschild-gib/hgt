# The large-rapidity boost bound and the quantitative two-prime cross term

**Stage:** 3 (formalized), 2026-09-04.  Closes MUST-173.  Two new modules
(`SemilocalBoostEntryBound`, `SemilocalTruncationDefectBound`), wired into `RHTower.lean`, axioms
`[propext, Classical.choice, Quot.sound]`, lint clean.  Continues
`semilocal-two-mode-bilinear-response-lean.md`.

**Theorem 1 — separable expansion** (`RHTower.MeixnerPollaczek.normalization_mul_boostMatrixEntry_eq_sepRow`).
With `σ = sech t`, `τ = tanh t`, `M_{mn}(t) = ∫ p_m p_n e^{its} dμ`:

    c_n M_{mn}(t) = (cosh t)^{-1/2} c_m Σ_{k ≤ min(m,n)} binom(m,k) σ^{2k} (iτ)^{m+n−2k} (k+½)_{n−k}/(n−k)!.

Mechanism: `z + iτ = σ² z + iτ(1 − iτz)` (`sech² + tanh² = 1`), so the row polynomial
`(z + iτ)^m` is a binomial sum in the basis `z^k (1 − iτz)^{m−k}`, and the row function
`(z+iτ)^m (1−iτz)^{-m-1/2}` becomes `Σ_k binom(m,k) σ^{2k} (iτ)^{m−k} z^k (1−iτz)^{-k-1/2}`; the
Taylor coefficients of the shifted binomials are read off and identified with the corpus's
`normalization_mul_boostMatrixEntry_eq` by power-series uniqueness.  The earlier candidate
"(C_k/C_m)(k+½)_{m−k}/(m−k)!" is exactly `binom(m,k)`.

**Theorem 2 — boost bound** (`norm_boostMatrixEntry_le`).  For `t > 0`,

    |M_{mn}(t)| ≤ (cosh t)^{-1/2} c_m c_n (tanh t)^{m+n} exp(2mn/sinh² t).

Proof: every term of the expansion has modulus `C_m C_n τ^{m+n} binom(m,k) binom(n,k) (σ/τ)^{2k}/C_k`
(`(k+½)_{n−k}/(n−k)! = C_n binom(n,k)/C_k`), and `binom(m,k)binom(n,k)/C_k ≤ (2mn)^k/k!`
(`binom ≤ n^k/k!`, `1/C_k = 4^k k!²/(2k)!`, `2^k k! ≤ (2k)!`), so the sum is `≤ exp(2mn σ²/τ²)`
and `σ²/τ² = 1/sinh² t`.  Equality at `(0,0)`; numerically the bound is within 1–8 % for
`m, n ≤ 20` at `t = log 211` and never exceeded (`boost_entry_bound.py`).  The sharp form without
the exponential is false at small `t`, and the naive coefficient majorant of the kernel is
exponential; the factorization `1 − wz − iτ(w+z) = (1−iτw)(1−iτz) − σ² wz` is what makes the
large-rapidity structure visible.

**Theorem 3 — the truncation defect** (`SemilocalTruncationDefectBound`).  With
`E(δ; i, j) = (cosh δ)^{-1/2} c_i c_j exp(2ij/sinh² δ)` and `T(δ)_{ij} = 2 Re M_{ij}(δ)`
(`cosineModeTangent_apply_eq`):
* `|T(δ)_{ij}| ≤ 2E(δ; i,j)`, `|m_j(δ)| ≤ E(δ; j,j)`;
* `D_n = tr(T(δ₁)T(δ₂))` satisfies `|D_n| ≤ 4 Σ_{i,j≤n} E₁E₂` and the exact row increment
  `D_{n+1} − D_n = 2 Σ_{i≤n} T₁(i,n+1)T₂(i,n+1) + T₁(n+1,n+1)T₂(n+1,n+1)` (`truncationDefect_succ_sub`,
  block decomposition with `Fin.sum_univ_castSucc`), hence
  `|D_{n+1} − D_n| ≤ 8 Σ_{i≤n+1} E₁(i,n+1) E₂(i,n+1)` (`abs_truncationDefect_succ_sub_le`).

**Theorem 4 — the two-prime cross term at the squared-radius level**
(`abs_bilinearSquaredRadiusJet_sub_beat_le`).  For `δ₁, δ₂ > 0` and every degree `m+1`,

    |∂₁∂₂ a²_{m+1} − [beat-mode squared-radius jet]| ≤ r²_{m+1} · ( 2(E₊(m+2) + E₊(m+1))
        + 8 Σ_{i≤m+2} E₁(i,m+2)E₂(i,m+2) + 8 Σ_{i≤m+1} E₁(i,m+1)E₂(i,m+1)
        + 4 (E₁(m+2)+E₁(m+1)) (E₂(m+2)+E₂(m+1)) ),

`E₊ = E(δ₁+δ₂; ·,·)`, `E_a(j) = E(δ_a; j,j)`.  Every term carries `(cosh δ)^{-1/2}` factors: for
`δ_a = log p_a` (`cosh(log p) ≥ p/2`, `Σ_{i≤n} c_i² ≤ 2√(2n+1)`, `exp(2ij/sinh²) ≤ exp(8n²/(p−1/p)²)`)
the error is `O(ε √n)`, `ε = (p₁p₂)^{-1/2}`, against a beat-mode jet of size `O(1)·r²/√n`: the
two-prime cross term of the semilocal residual **is** the first-order beat-mode response, with an
explicit relative error `O(ε n)` for `n ≪ p`.  This is the theorem behind report §3.5.

| module | content |
|---|---|
| `SemilocalBoostEntryBound` | `sech_sq_add_tanh_sq`, `add_I_tanh_eq`, `sepCoeff`, `rowPolyFactor_eq_sum`, `boostRowClosed_eq_sum`, `shiftedBinomialCoeff`, `hasSum_shiftedBinomial`, `sepRowCoeff`, `hasSum_sepRow`, `normalization_mul_boostMatrixEntry_eq_sepRow`, `norm_rowConstant`, `rising_shift_eq`, `cbin_inv_eq`, `choose_mul_choose_div_cbin_le`, `norm_sepRowCoeff_le`, **`norm_boostMatrixEntry_le`** |
| `SemilocalTruncationDefectBound` | `cosineModeTangent_apply_eq/symm/castSucc`, `entryBound`, `abs_cosineModeTangent_le`, `abs_cosineDiagonalMoment_le`, `truncationDefect`, `abs_truncationDefect_le`, `truncationDefect_succ_sub`, `abs_truncationDefect_succ_sub_le`, `bilinearSquaredRadiusJet_sub_beat_eq`, **`abs_bilinearSquaredRadiusJet_sub_beat_le`** |

**Numerical pre-certification:** `computations/routej-semilocal-scale/boost_entry_bound.py` (+ log):
separable formula vs quadrature to `10⁻³²`, row identity to `10⁻³⁰`, bound never exceeded over
`t ∈ {0.3, 1, 2, log 211}`, `m, n ≤ 150`.
