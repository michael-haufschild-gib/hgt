import GaloisForLFunctions.RHTower.Sieve.PerronLemma

/-! Uniform control of the truncated Perron kernel at and away from the cutoff. -/

open Complex MeasureTheory RHTower.Sieve

noncomputable section

namespace GlobalTheory.PerronPsi

private lemma ne_zero_of_re {σ t : ℝ} (h : σ ≠ 0) : (σ : ℂ) + t * I ≠ 0 := by
  intro hzero
  exact h (by simpa using congrArg Complex.re hzero)

private lemma cont_vinv {σ : ℝ} (h : σ ≠ 0) : Continuous fun t : ℝ => ((σ : ℂ) + t * I)⁻¹ :=
  (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I).inv₀ (fun _ => ne_zero_of_re h)

private lemma vinv {σ : ℝ} (h : σ ≠ 0) (T : ℝ) :
    ∫ t in (-T)..T, ((σ : ℂ) + t * I)⁻¹ = ((2 * Real.arctan (T / σ) : ℝ) : ℂ) := by
  simp_rw [← one_div]
  rw [integral_const_div_re_add_self h]
  simp only [neg_sq, sub_self, mul_zero, zero_sub, div_neg, neg_div, neg_neg, Real.arctan_neg]
  rw [div_mul_cancel₀ _ I_ne_zero]
  push_cast
  ring

private lemma near (L : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (L * c) * (Real.pi + 2 * (T * |L|)) := by
  have hc0 : c ≠ 0 := hc.ne'
  set g : ℝ → ℂ := fun t => (cexp (I * ((L * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) with hg
  have hpt : ∀ t : ℝ, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I)
      = (Real.exp (L * c) : ℂ) * (g t + ((c : ℂ) + t * I)⁻¹) := by
    intro t
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have he : cexp (L * ((c : ℂ) + t * I)) =
        (Real.exp (L * c) : ℂ) * cexp (I * ((L * t : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hg]
    rw [he]
    field_simp
    ring
  have hgc : Continuous g := by
    simp only [hg]
    exact (by fun_prop : Continuous fun t : ℝ => cexp (I * ((L * t : ℝ) : ℂ)) - 1).div
      (by fun_prop) fun t => ne_zero_of_re hc0
  have hgb : ∀ t ∈ Set.uIoc (-T) T, ‖g t‖ ≤ |L| := by
    intro t _
    have hz : (c : ℂ) + t * I ≠ 0 := ne_zero_of_re hc0
    have hzn : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.mpr hz
    simp only [hg]
    rw [norm_div, div_le_iff₀ hzn]
    calc ‖cexp (I * ((L * t : ℝ) : ℂ)) - 1‖ ≤ ‖L * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |L| * |t| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |L| * ‖(c : ℂ) + t * I‖ := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg L)
        simpa using Complex.abs_im_le_norm ((c : ℂ) + t * I)
  have hint : (∫ t in (-T)..T, cexp (L * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I))
      = (Real.exp (L * c) : ℂ) *
        ((∫ t in (-T)..T, g t) + ∫ t in (-T)..T, ((c : ℂ) + t * I)⁻¹) := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hgc.intervalIntegrable _ _)
        ((cont_vinv hc0).intervalIntegrable _ _)]
  rw [hint, vinv hc0 T, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hg2 := intervalIntegral.norm_integral_le_of_norm_le_const hgb
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]] at hg2
  have hat : |2 * Real.arctan (T / c)| ≤ Real.pi := by
    rw [abs_of_pos (by have := Real.arctan_pos.mpr (div_pos hT hc); linarith)]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  calc ‖(∫ t in (-T)..T, g t) + ((2 * Real.arctan (T / c) : ℝ) : ℂ)‖
      ≤ ‖∫ t in (-T)..T, g t‖ + ‖((2 * Real.arctan (T / c) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ |L| * (2 * T) + Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
    _ = Real.pi + 2 * (T * |L|) := by ring

theorem kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ y c T : ℝ, 0 < y → 0 < c → 1 ≤ T →
    ‖perronVertical c T y - (if 1 ≤ y then 1 else 0)‖ ≤ C * y ^ c ∧
    ‖perronVertical c T y - (if 1 ≤ y then 1 else 0)‖ * (T * |Real.log y|) ≤ C * y ^ c := by
  refine ⟨3, by norm_num, ?_⟩
  intro y c T hy hc hT
  let d := T * |Real.log y|
  have hT0 : 0 < T := by linarith
  have hyc : 0 < y ^ c := Real.rpow_pos_of_pos hy _
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hfar (hne : y ≠ 1) :
      ‖perronVertical c T y - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c / (Real.pi * d) := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [if_neg (not_le.mpr h), d, mul_assoc] using norm_perronVertical_le hy h hc hT0
    · simpa [if_pos h.le, d, abs_of_pos (Real.log_pos h), mul_assoc] using
        norm_perronVertical_sub_one_le h hc hT0
  have hpos (hne : y ≠ 1) : 0 < d :=
    mul_pos hT0 (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy hne))
  constructor
  · by_cases hclose : d ≤ 1
    · have hV : ‖perronVertical c T y‖ ≤ 2 * y ^ c := by
        unfold perronVertical
        have he : (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
            ∫ t in (-T)..T, cexp ((Real.log y : ℝ) * ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'), ofReal_log hy.le]
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hn := near (Real.log y) hc hT0
        rw [← Real.rpow_def_of_pos hy] at hn
        refine (mul_le_mul_of_nonneg_left hn (by positivity)).trans ?_
        change 1 / (2 * Real.pi) * (y ^ c * (Real.pi + 2 * d)) ≤ _
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith only [hyc, mul_le_mul_of_nonneg_left hclose hyc.le,
          mul_nonneg hyc.le (show 0 ≤ Real.pi - 1 by linarith)]
      have hI : ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ ≤ y ^ c := by
        split_ifs with h
        · rw [norm_one]
          exact Real.one_le_rpow h hc.le
        · simpa using hyc.le
      exact (norm_sub_le _ _).trans ((add_le_add hV hI).trans_eq (by ring))
    · have hd : 1 < d := lt_of_not_ge hclose
      have hy1 : y ≠ 1 := by
        intro h
        simp [d, h] at hd
      refine (hfar hy1).trans ?_
      have hπd : 1 ≤ Real.pi * d := by nlinarith only [hπ, hd, mul_nonneg (sub_nonneg.mpr hπ) hd.le]
      exact (div_le_self hyc.le hπd).trans (by linarith only [hyc])
  · by_cases hy1 : y = 1
    · simp [hy1, hyc.le]
    have hd := hpos hy1
    calc _ ≤ (y ^ c / (Real.pi * d)) * d := mul_le_mul_of_nonneg_right (hfar hy1) hd.le
      _ = y ^ c / Real.pi := by field_simp
      _ ≤ y ^ c := div_le_self hyc.le hπ
      _ ≤ _ := by linarith only [hyc]

end GlobalTheory.PerronPsi
