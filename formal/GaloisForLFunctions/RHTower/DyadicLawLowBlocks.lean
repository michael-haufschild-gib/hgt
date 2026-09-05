import GaloisForLFunctions.RHTower.LevinsonGateFromDyadicMeanSquare

/-!
# Low blocks of the dyadic law are covered by the slack

On a block `[a, v]` with `20 ≤ a ≤ v ≤ 2a ≤ 2T₀` the mean square of the mollified detector on
any abscissa `σ₀ ∈ [¼, ½)` is at most `(v − a) · C(T₀)² · N²`, where `C(T₀)` bounds the detector
on the compact rectangle `[¼, ½] × [20, 2T₀]` and `N` bounds `‖Ψ‖` by the coefficient bound
`‖b_n‖ ≤ 1`. Since the dyadic law's slack is `ε (a + U/log U)` and `N = U^θ` with `θ < ½`, the low
blocks satisfy the law for `U` large with no analytic input.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The mollifier is bounded by its length on every abscissa `≥ 0`. -/
theorem norm_edPoly_le_card {b : ℕ → ℂ} {N : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖edPoly b (Finset.Icc 1 N) z‖ ≤ N := by
  classical
  unfold edPoly
  calc ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-z)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n * (n : ℂ) ^ (-z)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        rw [norm_mul]
        have hpow : ‖(n : ℂ) ^ (-z)‖ ≤ 1 := by
          rw [Complex.norm_natCast_cpow_of_pos (by omega)]
          simp only [Complex.neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
        calc ‖b n‖ * ‖(n : ℂ) ^ (-z)‖ ≤ 1 * 1 :=
              mul_le_mul (hbn n hn) hpow (norm_nonneg _) zero_le_one
          _ = 1 := by ring
    _ = N := by simp

/-- **Low blocks.** A uniform bound `C` for the detector on `[¼, ½] × [20, 2T₀]` controls the mean
square on every block `[a, v]` with `20 ≤ a ≤ v ≤ 2a`, `v ≤ 2T₀`. -/
theorem integral_normSq_mollifiedDetector_low_block_le {lam : ℂ} {C T₀ : ℝ}
    (hC : ∀ σ t : ℝ, 1 / 4 ≤ σ → σ ≤ 1 / 2 → 20 ≤ t → t ≤ 2 * T₀ →
      ‖levinsonG lam ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C)
    {b : ℕ → ℂ} {N : ℕ} (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    {σ₀ : ℝ} (hσ₀a : 1 / 4 ≤ σ₀) (hσ₀b : σ₀ ≤ 1 / 2)
    {a v : ℝ} (ha : 20 ≤ a) (hav : a ≤ v) (hv : v ≤ 2 * T₀) :
    (∫ t in a..v, ‖levinsonMollifiedDetector lam b (Finset.Icc 1 N)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (v - a) * (C * N) ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (1 / 4) 20 le_rfl (by norm_num) le_rfl (by linarith))
  have hpt : ∀ t ∈ Set.Icc a v,
      ‖levinsonMollifiedDetector lam b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ (C * N) ^ 2 := by
    intro t ht
    have h1 := hC σ₀ t hσ₀a hσ₀b (by linarith [ht.1]) (by linarith [ht.2])
    have h2 : ‖edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ≤ N :=
      norm_edPoly_le_card hbn (by simp; linarith)
    have hmul : ‖levinsonMollifiedDetector lam b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖
        ≤ C * N := by
      unfold levinsonMollifiedDetector
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) hC0
    exact pow_le_pow_left₀ (norm_nonneg _) hmul 2
  calc (∫ t in a..v, ‖levinsonMollifiedDetector lam b (Finset.Icc 1 N)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ∫ t in a..v, (C * N) ^ 2 := by
        apply intervalIntegral.integral_mono_on hav ?_ (by simp) ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [uIcc_of_le hav] at ht
          have hz : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
            intro h
            have := congrArg Complex.im h
            simp at this
            linarith [ht.1]
          have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
          have hA := (analyticAt_levinsonMollifiedDetector lam b hs hz).continuousAt
          have hmap : ContinuousAt (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) t := by fun_prop
          exact ((ContinuousAt.comp (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) hA hmap).norm.pow 2)
            |>.continuousWithinAt
        · intro t ht
          exact hpt t ht
    _ = (v - a) * (C * N) ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-- The detector is bounded on the compact rectangle `[¼, ½] × [20, 2T₀]`. -/
theorem exists_detector_bound_low (lam : ℂ) (T₀ : ℝ) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 4 ≤ σ → σ ≤ 1 / 2 → 20 ≤ t → t ≤ 2 * T₀ →
      ‖levinsonG lam ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  classical
  have hcomp : IsCompact (Set.Icc (1 / 4 : ℝ) (1 / 2) ×ˢ Set.Icc (20 : ℝ) (2 * T₀)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖levinsonG lam ((p.1 : ℂ) + (p.2 : ℂ) * I)‖)
      (Set.Icc (1 / 4 : ℝ) (1 / 2) ×ˢ Set.Icc (20 : ℝ) (2 * T₀)) := by
    intro p hp
    have hz : ((p.1 : ℂ) + (p.2 : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [hp.2.1]
    have hA := (analyticAt_levinsonG lam hz).continuousAt
    have hmap : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) p := by fun_prop
    exact ((ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) hA hmap).norm)
      |>.continuousWithinAt
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨C, fun σ t hσa hσb ht hT => ?_⟩
  have := hC (σ, t) ⟨⟨hσa, hσb⟩, ⟨ht, hT⟩⟩
  simpa using this

end

end RHTower
