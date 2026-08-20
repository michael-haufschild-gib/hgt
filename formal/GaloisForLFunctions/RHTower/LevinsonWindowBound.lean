import GaloisForLFunctions.RHTower.LevinsonWindowAdvance
import GaloisForLFunctions.RHTower.LevinsonHorizontalEdge
import GaloisForLFunctions.RHTower.LevinsonAdmissibleHeight

/-!
# The Levinson window with every edge estimated

Transporting the right-edge and horizontal-edge estimates from `G` to the entire detector
`G♯ = (s-1)^2 G` costs only the explicit rational term `2/(s-1)`, whose contribution to each edge is
`O(1)`.  What remains in the window inequality is the archimedean main term `θ(T₂) - θ(T₁)`, three
`O(log T)` edge terms, and `2π` times the number of zeros of `G♯` in `[1/2,4]×[T₁,T₂]`.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

/-! ## The pole correction on the edges -/

theorem im_two_div_horiz {x T : ℝ} (hT : 0 < T) :
    |((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im| ≤ 2 / T := by
  have hre : ((((x : ℂ) + (T : ℂ) * I) - 1)).re = x - 1 := by simp
  have him : ((((x : ℂ) + (T : ℂ) * I) - 1)).im = T := by simp
  have hns : Complex.normSq (((x : ℂ) + (T : ℂ) * I) - 1) = (x - 1) ^ 2 + T ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hden : (0 : ℝ) < (x - 1) ^ 2 + T ^ 2 := by positivity
  rw [Complex.div_im, hns, hre, him]
  simp only [Complex.re_ofNat, Complex.im_ofNat]
  rw [show (0 : ℝ) / ((x - 1) ^ 2 + T ^ 2) = 0 by simp, zero_sub, abs_neg, abs_div,
    abs_of_pos hden]
  rw [div_le_div_iff₀ hden hT]
  have : |2 * T| = 2 * T := abs_of_pos (by linarith)
  rw [this]
  nlinarith [sq_nonneg (x - 1), hT]

theorem re_two_div_vert {t : ℝ} :
    |((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re| ≤ 6 / (9 + t ^ 2) := by
  have hre : ((((4 : ℂ) + (t : ℂ) * I) - 1)).re = 3 := by simp; norm_num
  have him : ((((4 : ℂ) + (t : ℂ) * I) - 1)).im = t := by simp
  have hns : Complex.normSq (((4 : ℂ) + (t : ℂ) * I) - 1) = 9 + t ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hden : (0 : ℝ) < 9 + t ^ 2 := by positivity
  rw [Complex.div_re, hns, hre, him]
  simp only [Complex.re_ofNat, Complex.im_ofNat]
  rw [show (2 : ℝ) * 3 / (9 + t ^ 2) + 0 * t / (9 + t ^ 2) = 6 / (9 + t ^ 2) by ring]
  rw [abs_of_pos (by positivity)]

/-! ## The right edge for the entire detector -/

theorem abs_integral_re_logDeriv_levinsonGEntire_right_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ ≤ T₂) :
    |∫ t in T₁..T₂, (logDeriv (levinsonGEntire lam) ((4 : ℂ) + (t : ℂ) * I)).re|
      ≤ Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2) := by
  have hT0 : (0 : ℝ) < T₁ := by linarith
  have hne1 : ∀ t : ℝ, ((4 : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re] at this
    norm_num at this
  have hre4 : ∀ t : ℝ, (4 : ℝ) ≤ ((4 : ℂ) + (t : ℂ) * I).re := by
    intro t; simp
  have hGne : ∀ t : ℝ, levinsonG lam ((4 : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t => levinsonG_ne_zero_of_four_le hlam (hre4 t)
  have hsplit : ∀ t ∈ Set.uIcc T₁ T₂,
      (logDeriv (levinsonGEntire lam) ((4 : ℂ) + (t : ℂ) * I)).re
        = ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re
          + (logDeriv (levinsonG lam) ((4 : ℂ) + (t : ℂ) * I)).re := by
    intro t _
    rw [logDeriv_levinsonGEntire lam (hne1 t) (hGne t), Complex.add_re]
  have hcont₁ : ContinuousOn
      (fun t : ℝ => ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re) (Set.uIcc T₁ T₂) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    refine ContinuousOn.div continuous_const.continuousOn (by fun_prop) ?_
    intro t _
    exact sub_ne_zero.mpr (hne1 t)
  have hcont₂ : ContinuousOn
      (fun t : ℝ => (logDeriv (levinsonG lam) ((4 : ℂ) + (t : ℂ) * I)).re)
      (Set.uIcc T₁ T₂) := by
    refine Complex.continuous_re.comp_continuousOn ?_
    have hnum : Continuous fun t : ℝ => deriv (levinsonG lam) ((4 : ℂ) + (t : ℂ) * I) :=
      continuous_deriv_levinsonG_vertLine lam _ hne1
    have hden : Continuous fun t : ℝ => levinsonG lam ((4 : ℂ) + (t : ℂ) * I) :=
      continuous_levinsonG_vertLine lam _ hne1
    exact ContinuousOn.div hnum.continuousOn hden.continuousOn (fun t _ => hGne t)
  rw [intervalIntegral.integral_congr hsplit,
    intervalIntegral.integral_add hcont₁.intervalIntegrable hcont₂.intervalIntegrable]
  have hcorr : |∫ t in T₁..T₂, ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re|
      ≤ (T₂ - T₁) * (6 / T₁ ^ 2) := by
    have hbnd : ∀ t ∈ Set.uIoc T₁ T₂,
        ‖((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re‖ ≤ 6 / T₁ ^ 2 := by
      intro t ht
      rw [Set.uIoc_of_le hT] at ht
      rw [Real.norm_eq_abs]
      refine le_trans re_two_div_vert ?_
      have hTt : T₁ ≤ t := ht.1.le
      have hsq : T₁ ^ 2 ≤ 9 + t ^ 2 := by nlinarith [hTt, hT0]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs] at h
    calc |∫ t in T₁..T₂, ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re|
        ≤ 6 / T₁ ^ 2 * |T₂ - T₁| := h
      _ = (T₂ - T₁) * (6 / T₁ ^ 2) := by rw [abs_of_nonneg (by linarith)]; ring
  have hmain := abs_integral_re_logDeriv_levinsonG_right_le hlam (le_refl (4 : ℝ)) hT
  calc |(∫ t in T₁..T₂, ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re)
        + ∫ t in T₁..T₂, (logDeriv (levinsonG lam) ((4 : ℂ) + (t : ℂ) * I)).re|
      ≤ |∫ t in T₁..T₂, ((2 : ℂ) / (((4 : ℂ) + (t : ℂ) * I) - 1)).re|
        + |∫ t in T₁..T₂, (logDeriv (levinsonG lam) ((4 : ℂ) + (t : ℂ) * I)).re| :=
        abs_add_le _ _
    _ ≤ (T₂ - T₁) * (6 / T₁ ^ 2) + Real.pi := add_le_add hcorr hmain
    _ = Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2) := by ring

/-! ## The horizontal edges for the entire detector -/

theorem exists_horizontal_levinsonGEntire_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, |lam| ≤ 1 → ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..4,
          (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ c * Real.log T := by
  obtain ⟨c₀, hc₀, hbound⟩ := exists_horizontal_levinsonG_bound
  refine ⟨c₀ + 1, by positivity, fun lam hlam T hT hne => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hne1 : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im] at him
    exact hTne (by linarith)
  have huIcc : Set.uIcc (1 / 2 : ℝ) 4 = Icc (1 / 2 : ℝ) 4 := uIcc_of_le (by norm_num)
  have hsplit : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
      (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im
        = ((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im
          + (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x hx
    rw [huIcc] at hx
    rw [logDeriv_levinsonGEntire (lam : ℂ) (hne1 x) (hne x hx), Complex.add_im]
  have hcont₁ : ContinuousOn
      (fun x : ℝ => ((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im) (Set.uIcc (1 / 2 : ℝ) 4) := by
    refine Complex.continuous_im.comp_continuousOn ?_
    refine ContinuousOn.div continuous_const.continuousOn (by fun_prop) ?_
    intro x _
    exact sub_ne_zero.mpr (hne1 x)
  have hcont₂ : ContinuousOn
      (fun x : ℝ => (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im)
      (Set.uIcc (1 / 2 : ℝ) 4) := by
    rw [huIcc]
    refine Complex.continuous_im.comp_continuousOn ?_
    have hnum : Continuous fun x : ℝ => deriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I) :=
      continuous_deriv_levinsonG_horizEdge (lam : ℂ) _ hne1
    have hden : Continuous fun x : ℝ => levinsonG (lam : ℂ) ((x : ℂ) + (T : ℂ) * I) :=
      continuous_levinsonG_horizEdge (lam : ℂ) _ hne1
    exact ContinuousOn.div hnum.continuousOn hden.continuousOn (fun x hx => hne x hx)
  rw [intervalIntegral.integral_congr hsplit,
    intervalIntegral.integral_add hcont₁.intervalIntegrable hcont₂.intervalIntegrable]
  have hcorr : |∫ x in (1 / 2 : ℝ)..4, ((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im|
      ≤ Real.log T := by
    have hbnd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 4,
        ‖((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im‖ ≤ 2 / T := by
      intro x _
      rw [Real.norm_eq_abs]
      exact im_two_div_horiz hT0
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs] at h
    have habs : |(4 : ℝ) - 1 / 2| = 7 / 2 := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < (4 : ℝ) - 1 / 2)]; norm_num
    rw [habs] at h
    have hsmall : 2 / T * (7 / 2) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hT0]
      linarith
    linarith
  have hmain := hbound lam hlam T (by linarith) hne
  calc |(∫ x in (1 / 2 : ℝ)..4, ((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im)
        + ∫ x in (1 / 2 : ℝ)..4, (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ |∫ x in (1 / 2 : ℝ)..4, ((2 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - 1)).im|
        + |∫ x in (1 / 2 : ℝ)..4,
            (logDeriv (levinsonG (lam : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im| := abs_add_le _ _
    _ ≤ Real.log T + c₀ * Real.log T := add_le_add hcorr hmain
    _ = (c₀ + 1) * Real.log T := by ring


/-! ## The window inequality with every edge estimated -/

/-- **The Levinson window with all three non-critical edges bounded.**  The only term left
undetermined is the number of zeros of the entire detector inside the rectangle. -/
theorem exists_levinson_window_edge_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 → ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
      (∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
        levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
        levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (∀ τ ∈ Set.Icc T₁ T₂, levinsonG (lam : ℂ) (linePt τ) ≠ 0) →
      ∀ n : ℕ,
        (∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (Set.uIcc (1 / 2 : ℝ) 4 ×ℂ Set.uIcc T₁ T₂) ∧
            levinsonGEntire (lam : ℂ) z = 0) →
          ((n : ℝ) + 1) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2)
              + c * Real.log T₁ + c * Real.log T₂
              + 2 * Real.pi *
                (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))
            ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁) →
        n ≤ xiOddFiberCount T₂ := by
  obtain ⟨c, hc, hhoriz⟩ := exists_horizontal_levinsonGEntire_bound
  refine ⟨c, hc, ?_⟩
  intro lam hlam0 hlam T₁ T₂ h20 hT hbot htop hbotG htopG hleft n hn
  have hlamC : ‖(lam : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  refine le_xiOddFiberCount_of_levinson_window hlam0 (by norm_num : (1 / 2 : ℝ) < 4)
    h20 hT hbot htop ?_ hleft ?_
  · intro t _
    refine levinsonGEntire_ne_zero_of_four_le hlamC ?_
    simp
  · intro Z hZ
    have hR := abs_integral_re_logDeriv_levinsonGEntire_right_le hlamC h20 hT.le
    have hB := hhoriz lam hlam T₁ h20 hbotG
    have hTp := hhoriz lam hlam T₂ (by linarith) htopG
    have hgoal := hn Z hZ
    rw [abs_le] at hR hB hTp
    simp only [Complex.ofReal_ofNat]
    linarith [hR.1, hR.2, hB.1, hB.2, hTp.1, hTp.2, hgoal]


end RHTower

end
