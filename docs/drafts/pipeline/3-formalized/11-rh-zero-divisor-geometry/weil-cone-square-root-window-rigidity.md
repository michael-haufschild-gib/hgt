# Square-root window rigidity: Λ is isolated in the Weil cone at the √x scale

- **ID:** weil-sqrt-window-rigidity
- **Stage:** 3-formalized (paper and Lean 2026-10-01, MC loop cycles 219–221)
- **Type:** THEOREM (Lean, standard axioms)
- **Statement.**
  - **Setting.** `Λ` is Weil-positive (equivalently RH) and `lam` is a full-cone producer. For a test `K = f⋆f̃`, the normalized window sum is `S_lam(y) = Σ_{n≥2} lam(n)n^{−½}K(log n − y)`, i.e. `x^{−½}Σ lam(n)ψ(n/x)`.
  - **Claim.** If `(1/Y)∫_{R₀}^{Y}|S_lam(y) − S_Λ(y)|dy → 0` for every test and every large `R₀`, then `lam = Λ` on `n ≥ 2`.
  - **Two-producer form.** If two producers have Cesàro-`L¹`-vanishing differences of translated Weil functionals, their boundary measures have the same atoms.
- **Lean.** All modules wired, axioms `[propext, Classical.choice, Quot.sound]`.
  - `RHTower/WeilConeWindowRigidity`: `eq_vonMangoldt_of_window`, `boundaryMeasure_real_singleton_eq_of_cesaro`, `weilFullFunctional_transl_sub_eq`.
  - `RHTower/WeilFullConeAtomExtraction`: `tendsto_mul_re_weilContinuation_atom`, `boundaryMeasure_vonMangoldt_real_singleton` (`μ_Λ{a} = ord_{½+ia}ξ`).
  - `HTGeometry/CharFunWienerLemma`: `tendsto_oneSided_mean_charFun_mul` and Wiener's lemma `tendsto_mean_normSq_charFun`.
  - Companions: `WeilFullConeSquareRootPNT` (MUST-652), `WeilFullConePNTErrorWiener` (MUST-654).

## Proof
1. `W_lam(K_y) = charFun ν_f(y)`, with `ν_f = |f̂|²μ_lam` (Bochner).
2. The one-sided Cesàro mean of `charFun ν(y)e^{−iay}` tends to `ν({a})`. So Cesàro-`L¹` closeness of `W_lam(K_y)` and `W_lam'(K_y)` gives `ν_f{a} = ν'_f{a}`.
3. `ν_f{a} = |f̂(a)|²μ{a}`. Taking `f` a mollifier with `|f̂(a)| ≥ ½` gives `μ_lam{a} = μ_lam'{a}`.
4. Past the support of `K`, `W_lam(K_y) − W_lam'(K_y) = S_lam'(y) − S_lam(y)`: the pole and archimedean parts cancel exactly.
5. **Atoms of Λ.** `b·Re Φ(½+b+ia) → μ{a}` (dominated convergence with `2/(1+(r−a)²)`). For Λ, `Φ_Λ = ξ'/ξ` on `Re s > ½` (identity theorem under RH), and the residue law gives `μ_Λ{a} = ord_{½+ia}ξ`.
6. Under RH every zero copy is critical. Every deficit weight is `(1 − μ_lam{γ}/m_γ)⁺ = 0`, so `D(T) ≡ 0` and the deficit law (MUST-645) gives `lam = Λ`.

## Phase-4 verdict
- **SURVIVES**, new to the corpus.
  - The hypothesis is window cancellation at the exact `√x` scale in Cesàro-`L¹`, with no condition on individual coefficients. The corpus log-square rigidity needs `Σw²/(log n)^K < ∞`; the two hypotheses are incomparable for `K > 0`.
  - HF L192 had the one-system Wiener reading (super-regularity ⟺ no atoms). The relative form, combined with the deficit law to obtain uniqueness, is new.
- **Reading.** Under RH, any second producer differs from Λ by `≫ √x` (Cesàro mean) in some smoothed window. Producers cannot be `o(√x)`-perturbations of Λ: the uniqueness question is pushed to the full `√x` scale.
- **Limit.** The hypothesis requires all tests and Cesàro decay. Whether `O(√x)`-closeness with a small constant suffices is open; it would need a quantitative deficit law at the critical scale.
