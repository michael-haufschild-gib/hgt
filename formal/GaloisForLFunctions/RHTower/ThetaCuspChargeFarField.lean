import GaloisForLFunctions.RHTower.ThetaCuspChargeSaddleGeometry

open Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups

namespace RHTower

noncomputable section

open Bottcher

theorem sl_im_smul_eq (g : SL(2, ℤ)) (τ : ℍ) :
    (g • τ).im = τ.im / Complex.normSq (slDen g τ) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  congr 2

theorem thetaGroupBasis_one_eq_farey {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupBasis 1 τ = thetaTwo τ ^ 4 * thetaFour τ ^ 4 / thetaThree τ ^ 7 := by
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  unfold thetaGroupBasis thetaGroupHauptmodul
  field_simp

section FarField

variable {t : ℝ}

/-- The line point `τ(s) = e^{2s}ω` has `Im τ = e^{2s}·2ab`. -/
theorem im_line_point (s : ℝ) :
    ((Real.exp (2 * s) : ℂ) * chOmega t).im = Real.exp (2 * s) * (2 * t ^ 2 * chB t) := by
  simp [chOmega, -Complex.ofReal_exp]

/-- `|cτ+d|²` on the line. -/
theorem normSq_den_line (ht4 : t ^ 4 ≤ 1) (c d : ℤ) (s : ℝ) :
    Complex.normSq ((c : ℂ) * ((Real.exp (2 * s) : ℂ) * chOmega t) + (d : ℂ)) =
      (c : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 + 2 * c * d * Real.exp (2 * s) * (1 - 2 * t ^ 4) +
        (d : ℝ) ^ 2 := by
  rw [Complex.normSq_apply]
  simp [chOmega, -Complex.ofReal_exp]
  have hb := chB_sq ht4
  linear_combination ((c : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 * (4 * t ^ 4)) * hb

/-- **Farey exponent cap on the line away from the window.** -/
theorem normSq_den_line_ge (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {c d : ℤ} (hc : Odd c) (hd : Odd d)
    {s : ℝ} (hs : 2 * t ^ 2 ≤ |s|) :
    12 * Real.exp (2 * s) * t ^ 4 ≤
      (c : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 + 2 * c * d * Real.exp (2 * s) * (1 - 2 * t ^ 4) +
        (d : ℝ) ^ 2 := by
  set ρ := Real.exp (2 * s) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hcd : Odd (c * d) := Int.odd_mul.mpr ⟨hc, hd⟩
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have h12 : 0 ≤ 1 - 2 * t ^ 4 := by nlinarith
  have hcdR : ((c * d : ℤ) : ℝ) = (c : ℝ) * d := by push_cast; ring
  generalize hm : c * d = m at hcd hcdR
  obtain ⟨k, hk⟩ := hcd
  rcases (by omega : 1 ≤ m ∨ m = -1 ∨ m ≤ -3) with hpos | hm1 | hm3
  · have hpos' : (1 : ℝ) ≤ (c : ℝ) * d := by rw [← hcdR]; exact_mod_cast hpos
    have hsq : 2 * ((c : ℝ) * d) * ρ ≤ (c : ℝ) ^ 2 * ρ ^ 2 + (d : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((c : ℝ) * ρ - d)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (c : ℝ) * d) hρ0.le) h12,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 6 - t ^ 4) hρ0.le,
      mul_nonneg (by linarith : (0:ℝ) ≤ (c : ℝ) * d - 1) hρ0.le]
  · have hcdm : c * d = -1 := by rw [hm, hm1]
    have hc1 : c ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hcdm with h | h <;> rw [h] <;> norm_num
    have hd1 : d ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one (by rw [mul_comm]; exact hcdm) with h | h <;>
        rw [h] <;> norm_num
    have hc1' : (c : ℝ) ^ 2 = 1 := by exact_mod_cast hc1
    have hd1' : (d : ℝ) ^ 2 = 1 := by exact_mod_cast hd1
    have hcd' : (c : ℝ) * d = -1 := by rw [← hcdR, hm1]; norm_num
    have hD : (c : ℝ) ^ 2 * ρ ^ 2 + 2 * c * d * ρ * (1 - 2 * t ^ 4) + (d : ℝ) ^ 2 =
        chD t s := by
      rw [chD, hc1', hd1', ← hρ]
      linear_combination (2 * ρ * (1 - 2 * t ^ 4)) * hcd'
    rw [hD, chD_eq, ← hρ]
    have hσ := two_abs_le_abs_chSigma s
    have hσ2 : 16 * t ^ 4 ≤ chSigma s ^ 2 := by
      have h1 : 4 * t ^ 2 ≤ |chSigma s| := by linarith
      have := pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at this; nlinarith
    nlinarith [pow_pos ht 4]
  · have h3 : (3 : ℝ) ≤ -((c : ℝ) * d) := by
      rw [← hcdR]; have : (3 : ℤ) ≤ -m := by omega
      exact_mod_cast this
    have hsq : 2 * (-((c : ℝ) * d)) * ρ ≤ (c : ℝ) ^ 2 * ρ ^ 2 + (d : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((c : ℝ) * ρ + d)]
    nlinarith [pow_pos ht 4, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ -((c : ℝ) * d) - 3)
      hρ0.le) (pow_pos ht 4).le]

/-- `κ = 2ab = cos 2β = Im ω`. -/
def chKap (t : ℝ) : ℝ := 2 * t ^ 2 * chB t

theorem chKap_pos (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) : 0 < chKap t := by
  unfold chKap; have := half_le_chB (t := t) ht4; positivity

theorem chKap_le_one (ht2 : t ^ 2 ≤ 1 / 2) : chKap t ≤ 1 := by
  unfold chKap; have := chB_le_one (t := t); have := chB_nonneg (t := t); nlinarith

/-- **Farey bound for the charge form on the saddle ray.** -/
theorem norm_basis_line_farey (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {s : ℝ} (hs : 2 * t ^ 2 ≤ |s|)
    (hin : chKap t ≤ Real.exp (2 * s)) :
    ‖thetaGroupBasis 1 ((Real.exp (2 * s) : ℂ) * chOmega t)‖ ≤
      3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ * Real.exp (chR0 t / 3) := by
  have ht4' : t ^ 4 ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have hb := half_le_chB (t := t) (by linarith)
  have him : 0 < ((Real.exp (2 * s) : ℂ) * chOmega t).im := by
    rw [im_line_point]; have := chB_nonneg (t := t); positivity
  set τ : ℍ := ⟨(Real.exp (2 * s) : ℂ) * chOmega t, him⟩ with hτ
  have hτc : (τ : ℂ) = (Real.exp (2 * s) : ℂ) * chOmega t := rfl
  have hτim : τ.im = Real.exp (2 * s) * chKap t := by
    show ((τ : ℂ)).im = _; rw [hτc, im_line_point]; rfl
  rw [thetaGroupBasis_one_eq_farey him]
  obtain ⟨g, -, hg⟩ := norm_thetaForm_farey τ
  rw [hτc] at hg
  refine le_trans hg ?_
  have hR : 0 ≤ chR0 t := by unfold chR0; have := chB_nonneg (t := t); positivity
  -- the automorphy factor
  have hden : ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t)⁻¹ := by
    by_cases hc : g 1 0 = 0
    · have hdet := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      have hd : g 1 1 = 1 ∨ g 1 1 = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hn : ‖slDen g τ‖ = 1 := by
        unfold slDen; rw [hc]; rcases hd with h | h <;> rw [h] <;> simp
      rw [hn, Real.one_rpow]
      rw [le_inv_comm₀ one_pos hκ, inv_one]; exact hκ1
    · have hlow : chKap t * chKap t ≤ ‖slDen g τ‖ := by
        have h1 : |(slDen g τ).im| ≤ ‖slDen g τ‖ := Complex.abs_im_le_norm _
        have h2 : (slDen g τ).im = (g 1 0 : ℝ) * τ.im := by
          unfold slDen; simp
        have h3 : (1 : ℝ) ≤ |(g 1 0 : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
        rw [h2, abs_mul, abs_of_pos τ.im_pos, hτim] at h1
        have h4 : chKap t * chKap t ≤ Real.exp (2 * s) * chKap t :=
          mul_le_mul_of_nonneg_right hin hκ.le
        nlinarith [Real.exp_pos (2 * s)]
      have hpos : 0 < chKap t * chKap t := by positivity
      calc ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) ≤ (chKap t * chKap t) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
        _ = (chKap t)⁻¹ := by
            rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self hκ.le]
  -- the cusp exponential
  have hexp : (if Odd (g 1 0) ∧ Odd (g 1 1) then Real.exp (7 * Real.pi / 4 * (g • τ).im) else 1)
      ≤ Real.exp (chR0 t / 3) := by
    split_ifs with hodd
    · apply Real.exp_le_exp.mpr
      rw [sl_im_smul_eq, hτim]
      have hN := normSq_den_line_ge ht (by linarith) hodd.1 hodd.2 hs
      have hNeq := normSq_den_line ht4' (g 1 0) (g 1 1) s
      have hsl : slDen g τ = ((g 1 0 : ℤ) : ℂ) * ((Real.exp (2 * s) : ℂ) * chOmega t) +
          ((g 1 1 : ℤ) : ℂ) := by unfold slDen; rw [hτc]
      rw [hsl, hNeq]
      have hNpos : 0 < 12 * Real.exp (2 * s) * t ^ 4 := by positivity
      have hq : Real.exp (2 * s) * chKap t /
          ((g 1 0 : ℝ) ^ 2 * Real.exp (2 * s) ^ 2 +
            2 * (g 1 0 : ℝ) * (g 1 1 : ℝ) * Real.exp (2 * s) * (1 - 2 * t ^ 4) + (g 1 1 : ℝ) ^ 2)
          ≤ Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) :=
        div_le_div_of_nonneg_left (by positivity) hNpos hN
      have hval : Real.exp (2 * s) * chKap t / (12 * Real.exp (2 * s) * t ^ 4) =
          chB t / (6 * t ^ 2) := by
        unfold chKap; field_simp; ring
      rw [hval] at hq
      have h7 : 7 * Real.pi / 4 * (chB t / (6 * t ^ 2)) = chR0 t / 3 := by
        unfold chR0; field_simp; ring
      calc 7 * Real.pi / 4 * _ ≤ 7 * Real.pi / 4 * (chB t / (6 * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = chR0 t / 3 := h7
    · exact Real.one_le_exp (by linarith)
  calc 3 ^ 8 * 2 ^ 7 * ‖slDen g τ‖ ^ (-(1 / 2 : ℝ)) *
        (if Odd (g 1 0) ∧ Odd (g 1 1) then Real.exp (7 * Real.pi / 4 * (g • τ).im) else 1)
      ≤ 3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ * Real.exp (chR0 t / 3) := by
        gcongr

theorem thetaGroupBasis_S (j : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaGroupBasis j (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaGroupBasis j τ := by
  rw [thetaGroupBasis_eq_form]; exact thetaGroupForm_S _ hτ

theorem exists_thetaGroupBasis_one_cusp :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ‖ ≤ M * Real.exp (-π * τ.im) := by
  obtain ⟨M, hM⟩ := thetaGroupBasis_cuspDecay 1
  refine ⟨M, fun τ hτ => ?_⟩
  have h := hM τ hτ
  simpa [thetaGroupBasisCusp] using h

/-- The far-field constant. -/
def chBfar (t M : ℝ) : ℝ :=
  max (3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ ^ 3 * Real.exp (chR0 t / 3) / 2) (M / 2 * (1 / (π * chKap t)))

/-- **Far field of the saddle line.** -/
theorem norm_chLine_far (ht : 0 < t) (ht4 : t ^ 4 ≤ 1 / 6) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ‖ ≤ M * Real.exp (-π * τ.im))
    {s : ℝ} (hs : 2 * t ^ 2 ≤ |s|) :
    ‖chLine t s‖ ≤ chBfar t M * Real.exp (-|s|) := by
  have ht2 : t ^ 2 ≤ 1 / 2 := by nlinarith [pow_pos ht 2]
  have ht21 : t ^ 2 ≤ 1 := by linarith
  have hκ := chKap_pos ht (by linarith)
  have hκ1 := chKap_le_one ht2
  have hβ0 := chBeta_nonneg ht2
  have hβ := chBeta_lt ht ht21
  have hcos : Real.cos (2 * chBeta t) = chKap t := cos_two_chBeta ht21
  set z : ℂ := (s : ℂ) - (chBeta t : ℂ) * Complex.I with hz
  have hzre : z.re = s := by simp [hz]
  have hzim : |z.im| ≤ chBeta t := by simp [hz, abs_of_nonneg hβ0]
  have hnorm : ‖chLine t s‖ = ‖chargeTailC (thetaGroupBasis 1) z‖ := by
    unfold chLine; rw [norm_mul, Complex.norm_exp]
    have : (-Complex.I * (chU t : ℂ) * (s : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
  rw [hnorm]
  have hS : ∀ τ : ℂ, 0 < τ.im →
      thetaGroupBasis 1 (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaGroupBasis 1 τ :=
    fun τ hτ => thetaGroupBasis_S 1 hτ
  obtain ⟨hA, hB⟩ := norm_chargeTailC_le_cusp hS hM hβ hzim
  rw [hzre, hcos] at hA hB
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hBnn : 0 ≤ 3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ ^ 3 * Real.exp (chR0 t / 3) / 2 := by positivity
  by_cases h1 : 1 ≤ Real.exp (2 * s) * chKap t
  · have hs0 : 0 ≤ s := by
      by_contra hneg; push Not at hneg
      have : Real.exp (2 * s) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_pi_le hκ hκ1 h1
    rw [abs_of_nonneg hs0]
    calc ‖chargeTailC (thetaGroupBasis 1) z‖
        ≤ M / 2 * (Real.exp (s / 2) * Real.exp (-π * (Real.exp (2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hA h1
      _ ≤ M / 2 * (1 / (π * chKap t) * Real.exp (-s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfar t M * Real.exp (-s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  by_cases h2 : 1 ≤ Real.exp (-2 * s) * chKap t
  · have hs0 : s ≤ 0 := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-2 * s) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have hkey := exp_half_mul_exp_neg_pi_le (x := -s) hκ hκ1
      (by rw [show 2 * -s = -2 * s by ring]; exact h2)
    rw [abs_of_nonpos hs0]
    calc ‖chargeTailC (thetaGroupBasis 1) z‖
        ≤ M / 2 * (Real.exp (-s / 2) * Real.exp (-π * (Real.exp (-2 * s) * chKap t))) := by
          rw [← mul_assoc]; exact hB h2
      _ = M / 2 * (Real.exp (-s / 2) * Real.exp (-π * (Real.exp (2 * -s) * chKap t))) := by
          ring_nf
      _ ≤ M / 2 * (1 / (π * chKap t) * Real.exp (- -s)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ chBfar t M * Real.exp (- -s) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at h1 h2
    have hin : chKap t ≤ Real.exp (2 * s) := by
      have h3 : Real.exp (-2 * s) * Real.exp (2 * s) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (2 * s), Real.exp_pos (-2 * s)]
    have hF := norm_basis_line_farey ht ht4 hs hin
    have habs : Real.exp (2 * |s|) * chKap t < 1 := by
      rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      · exact h1
      · rw [show 2 * -s = -2 * s by ring]; exact h2
    have he1 : Real.exp (s / 2) ≤ (chKap t)⁻¹ := by
      rw [le_inv_comm₀ (Real.exp_pos _) hκ]
      have : Real.exp (s / 2) ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := le_abs_self s; have := abs_nonneg s; linarith)
      rw [inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
      nlinarith
    have he2 : 1 ≤ (chKap t)⁻¹ * Real.exp (-|s|) := by
      have : Real.exp |s| ≤ Real.exp (2 * |s|) :=
        Real.exp_le_exp.mpr (by have := abs_nonneg s; linarith)
      have h4 : Real.exp |s| * Real.exp (-|s|) = 1 := by rw [← Real.exp_add]; simp
      rw [← div_eq_inv_mul, le_div_iff₀ hκ]
      nlinarith [Real.exp_pos (-|s|), Real.exp_pos |s|]
    have hval : ‖chargeTailC (thetaGroupBasis 1) z‖ =
        Real.exp (s / 2) * ‖thetaGroupBasis 1 ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2 := by
      unfold chargeTailC
      rw [hz, I_mul_cexp_line ht21, norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
      simp
    rw [hval]
    have hFnn := norm_nonneg (thetaGroupBasis 1 ((Real.exp (2 * s) : ℂ) * chOmega t))
    calc Real.exp (s / 2) * ‖thetaGroupBasis 1 ((Real.exp (2 * s) : ℂ) * chOmega t)‖ / 2
        ≤ (chKap t)⁻¹ * (3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ * Real.exp (chR0 t / 3)) / 2 := by
          gcongr
      _ ≤ (chKap t)⁻¹ * (3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ * Real.exp (chR0 t / 3)) / 2 *
          ((chKap t)⁻¹ * Real.exp (-|s|)) := le_mul_of_one_le_right (by positivity) he2
      _ = 3 ^ 8 * 2 ^ 7 * (chKap t)⁻¹ ^ 3 * Real.exp (chR0 t / 3) / 2 * Real.exp (-|s|) := by ring
      _ ≤ chBfar t M * Real.exp (-|s|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end FarField

end

end RHTower
