# Window-gluing doubling factor stops at `√2` and top-octave cancellation governs `< 2^{3/8}`

- **ID:** window-gluing-doubling-factor-root-two
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1511/obstacles-summary.md` §2.4 · `formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean`
- **Statement:** (1) **Universal finite-matrix `√2` doubling law (`reweightedDoublingLaw_sqrt_two`, `doublingLaw_sqrt_two`):** For every bounded contact weight `ω : ℕ → ℝ` (`|ω(k)| ≤ B`, `0 ≤ B`) and every block-size schedule `ρ : ℕ → ℕ`, `ReweightedDoublingLaw ω ρ (Real.sqrt 2)` holds directly from the finite block-matrix calculus (`abs_sum_floorGraph_le`, `sum_vonMangoldt_div_sqrt_le`, `hermNegIndex_reweightedNeutral_shift_eq_zero`), specializing at `ω ≡ 1` to `DoublingLaw ρ (Real.sqrt 2)` with no zero-free input and no polynomial upper bound on `ρ`. (2) **Sharp `√2` barrier across gluing-indistinguishable sub-Euler models (`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`, `not_reweightedDoublingLaw_of_le_two_rpow_three_eighths_subEulerGluingWeight`, `sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`, `gluing_indistinguishable_obstruction_package`):** For every finite certified cutoff `Q₀ : ℕ` and every `ρ : ℕ → ℕ` with `∀ K ≥ 1, 1 ≤ ρ(K)`, `subEulerGluingWeight Q₀ : ℕ → {0, 1}` satisfies exact prime-power constancy `ω(p^r) = ω(p)` (`r ≥ 1`), entrywise equality with `neutralWindow Q R J` for all `Q ≤ Q₀`, and entrywise equality `windowMatrix (reweightedNeutral ω Q) D D = primeFreeMiddle D` on every dyadic middle `(D, 2D]`, yet admits no doubling law with any factor `λ < √2` (in particular none `≤ 2^{3/8}` or `< 2^{3/8}`), and `sInf {λ | 1 < λ ∧ ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ λ} = √2`. (3) **Unconditional single-step top-octave jump and `< 2^{3/8}` characterization on `neutralWindow` (`neutralWindow_doubling_topOctave_decomposition`, `eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`, `topOctave_jump_of_doublingLaw_lt_sqrt_two`, `exists_doublingLaw_lt_two_rpow_three_eighths_iff`, `riemannZeta_ne_zero_of_doublingLaw`, `zero_free_below_seven_eighths_of_doublingLaw`):** On `(R, (6K + 1)R]`, gluing `(R, (3K + 1)R]` and `(2R, (6K + 2)R]` across `(2R, (3K + 1)R]` is blind to the fresh prime octave `3K + 2 ≤ k ≤ 6K + 1`, producing the un-updated matrix `neutralWindow (3K + 1) R (6KR)`, which unconditionally satisfies `2 ≤ hermNegIndex (neutralWindow (3K + 1) R (6KR) + a I)` for all `R ≥ 6`, `a ≤ (1/2000) √K − 40000`, and sufficiently large `K`; thus any `DoublingLaw ρ λ` with `1 < λ < √2` (`ρ(K) ≥ 6`) forces a nonzero real vector `v` with `∑_{k = 3K+2}^{6K+1} v ⬝ᵥ (windowMatrix (floorGraph k) R (6KR) *ᵥ v) < −((1/4000) √K) (v ⬝ᵥ v)`, and along `K¹⁰ ≤ ρ(K) ≤ K^A`, `(∃ λ ∈ (1, 2^{3/8}), DoublingLaw ρ λ) ↔ zetaZeroWidth < 3/8`, implying `riemannZeta s ≠ 0` on `Re s > 1/2 + log₂ λ < 7/8`.

## Goal
Determine unconditionally whether the finite-matrix window-gluing calculus yields a doubling law with factor `λ < 2^{3/8}` (or `λ < √2`), prove the universal `√2` window-gluing law directly from the matrix entries, establish the sharp `√2` obstruction on gluing-indistinguishable sub-Euler models, and formalize the exact top-octave prime cancellation and `< 2^{3/8}` equivalence on `neutralWindow`.

## Gates
- [x] 0 → 1  in-progress: exact formulation of reweighted window-gluing class, wide-overlap top-octave decomposition, and `√2` candidate vs sub-Euler countermodel
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete dependency-closed paper proof
- [x] 2 → 3  formalized: Lean modules `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing` and `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWindowGluingDoublingFactorStopsAtRootTwo`

## No-go closure
- **Exact killing mechanisms:**
  1. *Single-step top-octave blindness of wide-overlap gluing (`windowMatrix_reweightedNeutral_leftHalf_eq`, `windowMatrix_reweightedNeutral_rightHalf_eq`, `neutralWindow_doubling_topOctave_decomposition`, `eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`):* In `(R, (6K + 1)R] = E₁ ∪ M ∪ E₂` (`E₁ = (R, 2R]`, `M = (2R, (3K + 1)R]`, `E₂ = ((3K + 1)R, (6K + 1)R]`), every floor map `floorGraph k` with `3K + 2 ≤ k ≤ 6K + 1` vanishes identically on `(R, (3K + 1)R]`, on `(2R, (6K + 2)R] ⊇ M ∪ E₂`, on `M`, and on the couplings between `M` and `E₁, E₂`. Without updating by the fresh prime octave `[3K + 2, 6K + 1]`, the glued matrix is `neutralWindow (3K + 1) R (6KR)`, which unconditionally acquires `hermNegIndex ≥ 2` up to `(1/2000) √K − 40000` for every `R ≥ 6` and all sufficiently large `K`.
  2. *All-scale sub-Euler indistinguishability at `λ = √2` (`subEulerGluingWeight`, `two_le_hermNegIndex_subEulerGluingWeight`, `not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`):* For any certified cutoff `Q₀`, `subEulerGluingWeight Q₀ : ℕ → {0, 1}` activates prime powers `p^r` iff `p ≤ Q₀` or `p ∈ (256^m, 3 · 256^m]` (`m ≥ 1`), preserving `0 ≤ ω ≤ 1`, `ω(p^r) = ω(p)`, entrywise equality with `neutralWindow` up to `Q₀`, and `primeFreeMiddle D` at every `D`, while creating two orthogonal negative cluster modes on `{1} ∪ [N, 6N)` and `{7} ∪ [7N, 24N)` (`N = 256^m`, `K_m = 8 · 256^m`) up to shift `(1/60) √K_m − (subEulerCrossConst + 20000)` at every block size `R ≥ 1`. This rules out every `ReweightedDoublingLaw (subEulerGluingWeight Q₀) ρ λ` with `λ < √2`.
- **Strongest positive survivors:**
  1. *Universal finite-matrix `√2` doubling law (`reweightedDoublingLaw_sqrt_two`, `doublingLaw_sqrt_two`):* Unconditional proof of `DoublingLaw ρ (√2)` (and `ReweightedDoublingLaw ω ρ (√2)` for `|ω| ≤ B`) along every `ρ : ℕ → ℕ` directly from the bipartite floor-graph norm `|⟨σ, floorGraph k σ⟩| ≤ (2 Λ(k)/√k) ‖σ‖²`, dyadic Chebyshev summation `∑_{2 ≤ k ≤ Q} 2 Λ(k)/√k ≤ floorContactSqrtConst √Q`, and `blockPotential_ge_of_ratio` at `Q = 1`.
  2. *Sharp infimum `√2` on gluing-indistinguishable sub-Euler models (`sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`, `gluing_indistinguishable_obstruction_package`):* Exact evaluation of the infimum of valid doubling factors of `subEulerGluingWeight Q₀` as `√2` for every `Q₀` and every `ρ(K) ≥ 1`.
  3. *Single-step top-octave cancellation and `< 2^{3/8}` characterization on `neutralWindow` (`topOctave_jump_of_doublingLaw_lt_sqrt_two`, `exists_doublingLaw_lt_two_rpow_three_eighths_iff`, `riemannZeta_ne_zero_of_doublingLaw`, `zero_free_below_seven_eighths_of_doublingLaw`):* Any `DoublingLaw ρ λ` with `1 < λ < √2` (`ρ(K) ≥ 6`) forces `∑_{k=3K+2}^{6K+1} v ⬝ᵥ (windowMatrix (floorGraph k) R (6KR) *ᵥ v) < −((1/4000) √K) (v ⬝ᵥ v)` on a nonzero real vector `v`; along `K¹⁰ ≤ ρ(K) ≤ K^A`, `(∃ λ ∈ (1, 2^{3/8}), DoublingLaw ρ λ) ↔ zetaZeroWidth < 3/8`, implying `riemannZeta s ≠ 0` on `Re s > 1/2 + log₂ λ < 7/8`.
- **New insight:** Separates the local Green/Schur mechanics of finite Weil windows (`λ = √2` universal bipartite floor-map norm) from global prime cancellation across fresh octaves (`[3K + 2, 6K + 1]`), resolving `obstacles-summary.md` §2.4 and `ExponentDynamicsOfTheCriticalStrip/README.md` E2 unconditionally.
- **Status:** Unconditionally formalized in Lean 4 in `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing` and `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWindowGluingDoublingFactorStopsAtRootTwo`; `lake --old env lean` audit passed with zero warnings.

## Lean declarations
- `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow`:
  - `abs_sum_floorGraph_le`
  - `sum_vonMangoldt_div_sqrt_le`
  - `sum_reweightedNeutral_ge`
  - `hermNegIndex_reweightedNeutral_shift_eq_zero`
  - `reweightedNeutral_eq_of_agree_below_ratio`
  - `windowMatrix_reweightedNeutral_leftHalf_eq`
  - `windowMatrix_reweightedNeutral_rightHalf_eq`
  - `neutralWindow_doubling_topOctave_decomposition`
  - `subEulerGluingWeight`
  - `subEulerGluingWeight_prime_pow`
  - `windowMatrix_subEulerGluingWeight_eq_neutralWindow`
  - `two_le_hermNegIndex_subEulerGluingWeight`
  - `two_le_hermNegIndex_neutralWindow_halfCutoff_of_primeSums`
- `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip`:
  - `IsReweightedLevelLaw`, `ReweightedDoublingLaw`
  - `reweightedDoublingLaw_sqrt_two`
  - `doublingLaw_sqrt_two`
  - `not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`
  - `not_reweightedDoublingLaw_of_le_two_rpow_three_eighths_subEulerGluingWeight`
  - `sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`
  - `windowMatrix_reweightedNeutral_dyadic`
  - `gluing_indistinguishable_obstruction_package`
  - `eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`
  - `topOctave_jump_of_doublingLaw_lt_sqrt_two`
  - `exists_doublingLaw_lt_two_rpow_three_eighths_iff`
  - `riemannZeta_ne_zero_of_doublingLaw`
  - `zero_free_below_seven_eighths_of_doublingLaw`

## Log
- 2026-11-15 — dependency-closed paper proof completed and unconditionally formalized in Lean 4 (`TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean`, `TheWindowGluingDoublingFactorStopsAtRootTwo.lean`).
