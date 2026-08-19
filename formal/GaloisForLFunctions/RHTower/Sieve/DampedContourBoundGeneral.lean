import GaloisForLFunctions.RHTower.Sieve.DampedContourBoundDiag
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundGeneral

/-!
# The uniform sharp contour bound for the damped series

The damped analogue of `Sieve/MoebiusContourBoundGeneral`: the constants are uniform in both `N` and
the smoothing width `H`, which is what lets the eventual choice of `H` be made after the contour
parameter.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The uniform sharp contour bound, damped.** -/
theorem exists_norm_tsum_damped_smoothWeight_le_general {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K))
              * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ rightAbscissa K))
            / truncHeight K
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ rightAbscissa K)
              / (truncHeight K) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ leftAbscissa K)) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdecj⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨δ₁, hδ₁, hzfbox⟩ := exists_zero_free_box 1
  obtain ⟨δ₂, hδ₂, M₀, hM₀, hbdbox⟩ := exists_bound_invZeta_low_box 2 (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ 9) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in atTop,
      zeroFreeConst / (16 * min δ₁ δ₂) ≤ (Real.log n) ^ 9 := hpow.eventually_ge_atTop _
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨C, C', M₀, max K₁ 5, hC, hC', hM₀, fun N H hN hH K hKle => ?_⟩
  obtain ⟨hlogK, hfitpow⟩ := hK₁ K (le_trans (le_max_left _ _) hKle)
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hK2 : 2 ≤ K := by omega
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hL9 : (27 : ℝ) ≤ (Real.log K) ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (Real.log K) ^ 3 := by gcongr
      _ ≤ (Real.log K) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL9pos : (0 : ℝ) < (Real.log K) ^ 9 := by linarith
  have hδ0 : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hfit : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ min δ₁ δ₂ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfitpow
    linarith
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  have h2pos : (0 : ℝ) < zeroFreeConst / (2 * (Real.log K) ^ 9) := by positivity
  have h2small : zeroFreeConst / (2 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hd1 : 1 < rightAbscissa K := by rw [rightAbscissa]; linarith
  have hd2 : rightAbscissa K ≤ 2 := by rw [rightAbscissa]; linarith
  have hc0 : 0 < leftAbscissa K := by rw [leftAbscissa]; linarith
  have hc1 : leftAbscissa K ≤ 1 := by rw [leftAbscissa]; linarith
  have hchalf : 1 / 2 ≤ leftAbscissa K := by rw [leftAbscissa]; linarith
  have hcd : leftAbscissa K ≤ rightAbscissa K := by rw [leftAbscissa, rightAbscissa]; linarith
  have hT1 : 1 ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) ≤ truncHeight K := by linarith
  have hTK : 3 + 2 * truncHeight K ≤ (K : ℝ) := by rw [truncHeight]; linarith
  have hcorr0 : 0 ≤ dampedCorrBound P (leftAbscissa K) := by
    rw [dampedCorrBound]
    refine Finset.prod_nonneg fun p hp => ?_
    have hp2 := hP2 p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-leftAbscissa K) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hlt : (p : ℝ) ^ (-leftAbscissa K) < 1 := rpow_neg_lt_one hp2 hchalf
    positivity
  have hzf : ∀ s ∈ Set.uIcc (leftAbscissa K) (rightAbscissa K)
      ×ℂ Set.uIcc (-truncHeight K) (truncHeight K), s ≠ 1 → riemannZeta s ≠ 0 := by
    rw [leftAbscissa, rightAbscissa]
    exact zero_free_concrete_rect hlogK hK2
      (fun s h1' h2' h3' h4' => hzfbox s (by linarith [min_le_left δ₁ δ₂]) h2' h3' h4')
      (le_trans hfit (min_le_left _ _)) hT0 hTK
  -- the damped edge bounds
  have hFd : ∀ y : ℝ, ‖dampedInvZeta P t ((rightAbscissa K : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ invZetaRightBound K * dampedCorrBound P (leftAbscissa K) := by
    intro y
    have hre : ((rightAbscissa K : ℂ) + (y : ℝ) * Complex.I).re = rightAbscissa K := by simp
    refine norm_dampedInvZeta_le hP2 ht0 ht1 hchalf (by rw [hre]; exact hcd)
      (invZetaRightBound_nonneg K) ?_
    have h := norm_invZeta_right_le (d := rightAbscissa K) (y := y) hd1
    rw [invZetaRightBound, rightAbscissa]
    rw [rightAbscissa] at h
    simpa using h
  have hhor : ∀ (u : ℝ), 1 ≤ |u| → 3 + 2 * |u| ≤ (K : ℝ) →
      ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
        ‖dampedInvZeta P t ((x : ℂ) + (u : ℂ) * Complex.I)‖
          ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) := by
    intro u hu huK x hx
    have hre : ((x : ℂ) + (u : ℂ) * Complex.I).re = x := by simp
    refine norm_dampedInvZeta_le hP2 ht0 ht1 hchalf (by rw [hre]; exact hx.1.le)
      (invZetaEdgeBound_nonneg K) ?_
    rw [leftAbscissa] at hx
    rw [rightAbscissa] at hx
    rw [invZetaEdgeBound]
    exact norm_invZeta_horizontal_le hlogK hK2 hu huK hx.1.le hx.2
  have hFt : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖dampedInvZeta P t ((x : ℂ) + ((truncHeight K : ℝ) : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) :=
    hhor (truncHeight K) (by rw [abs_of_pos (by linarith)]; exact hT1)
      (by rw [abs_of_pos (by linarith)]; exact hTK)
  have hFb : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖dampedInvZeta P t ((x : ℂ) + ((-truncHeight K : ℝ) : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) :=
    hhor (-truncHeight K) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hT1)
      (by rw [abs_neg, abs_of_pos (by linarith)]; exact hTK)
  have hFc : ∀ y ∈ Set.Icc (-truncHeight K) (truncHeight K),
      ‖dampedInvZeta P t ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K) := by
    intro y hy
    have hre : ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I).re = leftAbscissa K := by simp
    refine norm_dampedInvZeta_le hP2 ht0 ht1 hchalf (by rw [hre])
      (le_trans hM₀ (le_max_left _ _)) ?_
    have hyabs : |y| ≤ truncHeight K := abs_le.2 ⟨hy.1, hy.2⟩
    have h := norm_invZeta_left_line_le (N := K) (M₀ := M₀) (δ₀ := min δ₁ δ₂) hlogK hK2
      (fun s h1' h2' h3' => hbdbox s (by linarith [min_le_right δ₁ δ₂]) h2' h3')
      hfit (y := y) (by linarith)
    rw [leftAbscissa, invZetaEdgeBound]
    exact h
  have hFccont : ContinuousOn
      (fun y : ℝ => dampedInvZeta P t ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-truncHeight K) (truncHeight K)) := by
    have hbase := continuousOn_invZeta_left_line hc1 (by linarith) hzf
    have hprod : Continuous (fun y : ℝ =>
        ∏ p ∈ P, dampedEulerFactor t p ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I)) :=
      continuous_finsetProd P
        (fun p hp => continuous_dampedEulerFactor_line (hP2 p hp) t hc0)
    exact hbase.mul hprod.continuousOn
  exact norm_tsum_damped_smoothWeight_le_sharp hPprime ht0 ht1 hN hH 0 hd1 hc0 hcd hT1
    (mul_nonneg (invZetaRightBound_nonneg K) hcorr0)
    (mul_nonneg (invZetaEdgeBound_nonneg K) hcorr0)
    (mul_nonneg (le_trans hM₀ (le_max_left _ _)) hcorr0) hzf hFd hFt hFb hFc hFccont
    (hdec1 N H hN hH (rightAbscissa K))
    (hdecj N H hN hH (rightAbscissa K))
    (hdec1 N H hN hH (leftAbscissa K))

end

end RHTower.Sieve
