import GaloisForLFunctions.RHTower.LevinsonOddFiberFinal
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# From Levinson's window count to a positive proportion

The window inequality bounds an *absolute* count on one window.  Turning it into a proportion needs
three asymptotic ingredients, all owned by the corpus: the Riemann–Siegel phase asymptotic
`θ(T) ~ ½ T log T`, the Riemann–von Mangoldt asymptotic `N(T) ~ (1/2π) T log T`, and monotonicity of
the odd-fibre census.  This file assembles them.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

noncomputable section

namespace RHTower

/-- The odd-fibre census is monotone. -/
theorem xiOddFiberCount_mono : Monotone xiOddFiberCount := by
  classical
  intro T U hTU
  refine Finset.card_le_card ?_
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  obtain ⟨hmem, hprop⟩ := hz
  refine ⟨?_, hprop⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_stripFinsetPos.mp hmem
  exact mem_stripFinsetPos.mpr ⟨h1, h2, h3, le_trans h4 hTU, h5⟩

/-- The Riemann–Siegel phase advance over a window anchored near `20` is `(½ − ε)·T log T`. -/
theorem eventually_phase_advance_ge (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ T₁ ∈ Set.Icc (20 : ℝ) 21,
      (1 / 2 - ε) * (T * Real.log T) ≤ gammaHardyTheta T - gammaHardyTheta T₁ := by
  obtain ⟨Cθ, hCθ⟩ : ∃ C : ℝ, ∀ t ∈ Set.Icc (20 : ℝ) 21, |gammaHardyTheta t| ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (20 : ℝ)) (b := 21)).exists_bound_of_continuousOn
      (differentiable_gammaHardyTheta.continuous.continuousOn)
    exact ⟨C, fun t ht => by simpa using hC t ht⟩
  have hCθ0 : (0 : ℝ) ≤ Cθ := le_trans (abs_nonneg _) (hCθ 20 (by norm_num))
  have hmain : Tendsto (fun t : ℝ => (gammaHardyTheta t - gammaHardyThetaMain t) / t)
      atTop (nhds 0) := gammaHardyTheta_sub_main_div_tendsto_zero
  have habs : ∀ᶠ t in atTop, |(gammaHardyTheta t - gammaHardyThetaMain t) / t| < ε / 4 := by
    have hz := NormedAddGroup.tendsto_nhds_zero.mp hmain (ε / 4) (by linarith)
    simpa [Real.norm_eq_abs, abs_div] using hz
  filter_upwards [habs, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (Real.exp (4 * (Cθ + 1) / ε)),
    eventually_ge_atTop (Real.exp (4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε)),
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (3 : ℝ)]
    with T hTabs hT0 hTexp hTexp2 hT1 hT3 T₁ hT₁
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos hT1
  have hdiff : |gammaHardyTheta T - gammaHardyThetaMain T| ≤ (ε / 4) * T := by
    have h := le_of_lt hTabs
    rw [abs_div, abs_of_pos hT0] at h
    rw [div_le_iff₀ hT0] at h
    linarith [h]
  have hmainval : gammaHardyThetaMain T
      = T / 2 * Real.log (T / (2 * Real.pi)) - T / 2 := rfl
  have hlogsplit : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) := by
    rw [Real.log_div (ne_of_gt hT0) (by positivity)]
  have hlow : gammaHardyThetaMain T
      = (1 / 2) * (T * Real.log T) - T * (Real.log (2 * Real.pi) / 2 + 1 / 2) := by
    rw [hmainval, hlogsplit]
    ring
  have hlogge : 4 * (Cθ + 1) / ε ≤ Real.log T := by
    rw [← Real.log_exp (4 * (Cθ + 1) / ε)]
    exact Real.log_le_log (Real.exp_pos _) hTexp
  have hlogge2 : 4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε ≤ Real.log T := by
    rw [← Real.log_exp (4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) / ε)]
    exact Real.log_le_log (Real.exp_pos _) hTexp2
  have hmul1 : 4 * (Cθ + 1) ≤ ε * Real.log T := by
    rw [div_le_iff₀ hε] at hlogge
    linarith
  have hmul2 : 4 * (Real.log (2 * Real.pi) / 2 + 1 / 2 + 1) ≤ ε * Real.log T := by
    rw [div_le_iff₀ hε] at hlogge2
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hTge : (1 : ℝ) ≤ T := by linarith
  have hTlog : Real.log T ≤ T * Real.log T := by nlinarith [hlogT, hTge]
  have hCbound : Cθ ≤ (ε / 4) * (T * Real.log T) := by
    have hstep : (ε / 4) * Real.log T ≤ (ε / 4) * (T * Real.log T) := by
      nlinarith [hTlog, hε]
    linarith [hmul1, hstep]
  have hlinbound : T * (Real.log (2 * Real.pi) / 2 + 1 / 2)
      ≤ (ε / 4) * (T * Real.log T) := by
    nlinarith [hmul2, hT0]
  have hTbound : (ε / 4) * T ≤ (ε / 4) * (T * Real.log T) := by
    nlinarith [hT0, hε, hlog1]
  have habs1 := abs_le.mp hdiff
  have hθ₁ := abs_le.mp (hCθ T₁ hT₁)
  linarith [habs1.1, hθ₁.2, hlow, hCbound, hlinbound, hTbound]

end RHTower

end
