import GaloisForLFunctions.RHTower.KuznetsovSameSignBessel
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Lower bounds for the spectral weight `∫ g_K(t) |W(1+it, ν)|² dt`

On the line `b = 1 + it`,

`|W(1+it, ν)|² = ½ |Γ(½+it)|² |Γ(½+it+ν)|² |Γ(½+it−ν)|² / |Γ(1+2it)|²`

(`norm_whittMellin_one_line_sq`).  For `ν = iκ` the factors are `π/cosh`, and for real `ν` the
reflection formula gives `|Γ(½+ν+it) Γ(½−ν+it)| = π/|cos π(ν+it)| ≥ π/cosh πt`.  Integrating over
`[κ+1, κ+2]`, resp. `[1, 2]`, for every eigenvalue `λ ≤ ¼ + K²` (`K ≥ 1`):

`∫ t² e^{−(t/K)²} · 4|W(1+it, ν_λ)|² dt ≥ c₀ (κ+1) e^{−πκ}`,
`κ = √(max(λ−¼, 0))`, `c₀ = (π²/4) e^{−9−2π}`

(`lintegral_gaussWeight_mul_whittMellin_ge`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

/-- The spectral height `κ = √(max(λ−¼, 0))`. -/
def specKappa (lam : ℝ) : ℝ := Real.sqrt (max (lam - 1 / 4) 0)

theorem norm_two_cpow (z : ℂ) : ‖(2 : ℂ) ^ z‖ = 2 ^ z.re := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (x := 2) (by norm_num) z
  simpa using this

/-- **`|W(1+it, ν)|²` in terms of four Gamma moduli.** -/
theorem norm_whittMellin_one_line_sq (t : ℝ) (ν : ℂ) :
    ‖whittMellin ((1 : ℝ) + t * Complex.I) ν‖ ^ 2 =
      1 / 2 * ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 *
        ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + ν)‖ ^ 2 *
        ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I - ν)‖ ^ 2 /
        ‖Complex.Gamma (1 + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  unfold whittMellin
  have e1 : ((1 : ℝ) : ℂ) + t * Complex.I - 1 / 2 = 1 / 2 + (t : ℂ) * Complex.I := by push_cast; ring
  have e2 : 2 * (1 / 2 + (t : ℂ) * Complex.I) = 1 + ((2 * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2, norm_div, norm_mul, norm_mul, norm_mul, norm_two_cpow]
  have h2 : ((2 : ℝ) ^ (1 / 2 + (t : ℂ) * Complex.I - 1).re) ^ 2 = 1 / 2 := by
    have : (1 / 2 + (t : ℂ) * Complex.I - 1).re = -(1 / 2) := by simp; norm_num
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [div_pow, mul_pow, mul_pow, mul_pow, h2]

theorem sinh_ge_exp_div_four {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 + 2 * x ≤ Real.exp x * Real.exp x := by
    rw [← Real.exp_add]; linarith [Real.add_one_le_exp (x + x)]
  have h3 := Real.exp_pos x
  have h4 := Real.exp_pos (-x)
  nlinarith

theorem norm_cos_le_cosh (a b : ℝ) : ‖Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ Real.cosh b := by
  rw [Complex.cos, norm_div, Complex.norm_two, Real.cosh_eq]
  refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans (le_of_eq ?_)) (by norm_num)
  rw [Complex.norm_exp, Complex.norm_exp]
  have e1 : (((a : ℂ) + (b : ℂ) * Complex.I) * Complex.I).re = -b := by simp
  have e2 : (-((a : ℂ) + (b : ℂ) * Complex.I) * Complex.I).re = b := by simp
  rw [e1, e2, add_comm]

/-- **The reflection bound** `|Γ(½+ν+it)| |Γ(½−ν+it)| ≥ π / cosh πt` for real `ν`, `t ≠ 0`. -/
theorem norm_Gamma_mul_norm_Gamma_ge {ν t : ℝ} (ht : t ≠ 0) :
    Real.pi / Real.cosh (Real.pi * t) ≤
      ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + ν)‖ *
        ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I - ν)‖ := by
  set z : ℂ := 1 / 2 + (t : ℂ) * Complex.I + ν
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have h1 : 1 - z = conj (1 / 2 + (t : ℂ) * Complex.I - ν) := by
    simp only [z, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
      map_ofNat]
    ring
  have hsin : Complex.sin (Real.pi * z) =
      Complex.cos (((Real.pi * ν : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [show (Real.pi : ℂ) * z = (Real.pi / 2 : ℂ) +
      (((Real.pi * ν : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I) by simp only [z]; push_cast; ring,
      Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    simp
  rw [h1, Complex.Gamma_conj, hsin] at hrefl
  have hnorm := congrArg norm hrefl
  rw [norm_mul, Complex.norm_conj, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    at hnorm
  have hpos : 0 < ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I - ν)‖ := by
    have hne : ∀ w : ℂ, w.im = t → ∀ m : ℕ, w ≠ -(m : ℂ) := fun w hw m =>
      ne_neg_nat_of_im_ne_zero (by rw [hw]; exact ht) m
    exact mul_pos (norm_pos_iff.2 (Complex.Gamma_ne_zero (hne _ (by simp [z]))))
      (norm_pos_iff.2 (Complex.Gamma_ne_zero (hne _ (by simp))))
  have hcos := norm_cos_le_cosh (Real.pi * ν) (Real.pi * t)
  have hcpos : 0 < ‖Complex.cos (((Real.pi * ν : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I)‖ := by
    by_contra h0
    have h00 : ‖Complex.cos (((Real.pi * ν : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 0 :=
      le_antisymm (not_lt.1 h0) (norm_nonneg _)
    rw [h00, div_zero] at hnorm
    linarith
  rw [hnorm]
  exact div_le_div_of_nonneg_left Real.pi_pos.le hcpos hcos

theorem norm_Gamma_one_add_two_I_sq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + ((2 * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      2 * Real.pi * t / Real.sinh (2 * Real.pi * t) := by
  rw [HTGeometry.norm_Gamma_one_add_I_sq (by positivity), abs_of_pos (by positivity : (0 : ℝ) < 2 * t),
    abs_of_pos (Real.sinh_pos_iff.2 (by positivity : (0 : ℝ) < Real.pi * (2 * t)))]
  ring_nf

theorem norm_Gamma_half_add_shift_sq (t κ : ℝ) :
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + Complex.I * κ)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * (t + κ)) ∧
    ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I - Complex.I * κ)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * (t - κ)) := by
  constructor
  · rw [show 1 / 2 + (t : ℂ) * Complex.I + Complex.I * κ = 1 / 2 + ((t + κ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, HTGeometry.norm_Gamma_half_add_I_sq]
  · rw [show 1 / 2 + (t : ℂ) * Complex.I - Complex.I * κ = 1 / 2 + ((t - κ : ℝ) : ℂ) * Complex.I by
      push_cast; ring, HTGeometry.norm_Gamma_half_add_I_sq]

/-- **The tempered weight**: `4|W(1+it, iκ)|² ≥ (π²/2) e^{−πκ−2π}/(κ+2)` on `[κ+1, κ+2]`. -/
theorem whittMellin_imag_lower {κ t : ℝ} (hκ : 0 ≤ κ) (ht1 : κ + 1 ≤ t) (ht2 : t ≤ κ + 2) :
    Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi) / (κ + 2) ≤
      4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (Complex.I * κ)‖ ^ 2 := by
  have ht : 0 < t := by linarith
  obtain ⟨hp, hm⟩ := norm_Gamma_half_add_shift_sq t κ
  rw [norm_whittMellin_one_line_sq, hp, hm, HTGeometry.norm_Gamma_half_add_I_sq,
    norm_Gamma_one_add_two_I_sq ht, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    Real.sinh_two_mul]
  have hA := sinh_ge_exp_div_four (show 1 ≤ Real.pi * t by nlinarith [Real.pi_gt_three])
  have hB := cosh_le_exp_abs' (Real.pi * (t + κ))
  have hC := cosh_le_exp_abs' (Real.pi * (t - κ))
  rw [abs_of_nonneg (by positivity)] at hB
  rw [abs_of_nonneg (by nlinarith [Real.pi_pos])] at hC
  have hC2 : Real.exp (Real.pi * (t - κ)) ≤ Real.exp (2 * Real.pi) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hcA := Real.cosh_pos (Real.pi * t)
  have hcB := Real.cosh_pos (Real.pi * (t + κ))
  have hcC := Real.cosh_pos (Real.pi * (t - κ))
  have hsA : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.2 (by positivity)
  have hπ := Real.pi_pos
  have key : 4 * (1 / 2 * (Real.pi / Real.cosh (Real.pi * t)) *
      (Real.pi / Real.cosh (Real.pi * (t + κ))) * (Real.pi / Real.cosh (Real.pi * (t - κ))) /
      (2 * (Real.pi * t) / (2 * Real.sinh (Real.pi * t) * Real.cosh (Real.pi * t)))) =
      2 * Real.pi ^ 2 * Real.sinh (Real.pi * t) /
        (t * Real.cosh (Real.pi * (t + κ)) * Real.cosh (Real.pi * (t - κ))) := by
    field_simp
    norm_num
  rw [key]
  have he : Real.exp (-(Real.pi * κ) - 2 * Real.pi) * Real.exp (Real.pi * (t + κ)) *
      Real.exp (2 * Real.pi) = Real.exp (Real.pi * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi) *
        (t * Real.cosh (Real.pi * (t + κ)) * Real.cosh (Real.pi * (t - κ)))
      ≤ Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi) *
        ((κ + 2) * Real.exp (Real.pi * (t + κ)) * Real.exp (2 * Real.pi)) := by
        gcongr
        exact hC.trans hC2
    _ = 2 * Real.pi ^ 2 * (Real.exp (Real.pi * t) / 4) * (κ + 2) := by
        rw [← he]; ring
    _ ≤ 2 * Real.pi ^ 2 * Real.sinh (Real.pi * t) * (κ + 2) := by gcongr

/-- **The exceptional weight**: `4|W(1+it, ν)|² ≥ (π²/4) e^{−2π}` for real `ν`, `t ∈ [1, 2]`. -/
theorem whittMellin_real_lower {ν t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    Real.pi ^ 2 / 4 * Real.exp (-(2 * Real.pi)) ≤
      4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) ν‖ ^ 2 := by
  have ht : 0 < t := by linarith
  have hprod := norm_Gamma_mul_norm_Gamma_ge (ν := ν) ht.ne'
  rw [norm_whittMellin_one_line_sq, HTGeometry.norm_Gamma_half_add_I_sq,
    norm_Gamma_one_add_two_I_sq ht, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    Real.sinh_two_mul]
  have hA := sinh_ge_exp_div_four (show 1 ≤ Real.pi * t by nlinarith [Real.pi_gt_three])
  have hB := cosh_le_exp_abs' (Real.pi * t)
  rw [abs_of_nonneg (by positivity)] at hB
  have hcA := Real.cosh_pos (Real.pi * t)
  have hsA : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.2 (by positivity)
  have hπ := Real.pi_pos
  set P := ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I + ν)‖
  set Q := ‖Complex.Gamma (1 / 2 + (t : ℂ) * Complex.I - ν)‖
  have hPQ : (Real.pi / Real.cosh (Real.pi * t)) ^ 2 ≤ P ^ 2 * Q ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hprod 2
  have key : 4 * (1 / 2 * (Real.pi / Real.cosh (Real.pi * t)) * P ^ 2 * Q ^ 2 /
      (2 * (Real.pi * t) / (2 * Real.sinh (Real.pi * t) * Real.cosh (Real.pi * t)))) =
      2 * Real.sinh (Real.pi * t) * (P ^ 2 * Q ^ 2) / t := by
    field_simp
    ring
  rw [key, le_div_iff₀ ht]
  have he : Real.exp (-(2 * Real.pi)) * Real.exp (Real.pi * t) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.pi ^ 2 / 4 * Real.exp (-(2 * Real.pi)) * t
      ≤ Real.pi ^ 2 / 4 * Real.exp (-(2 * Real.pi)) * 2 := by gcongr
    _ ≤ 2 * (Real.exp (Real.pi * t) / 4) * (Real.pi / Real.exp (Real.pi * t)) ^ 2 := by
        rw [div_pow, show Real.pi ^ 2 / 4 * Real.exp (-(2 * Real.pi)) * 2 =
          Real.pi ^ 2 / 2 * Real.exp (-(2 * Real.pi)) by ring]
        rw [show 2 * (Real.exp (Real.pi * t) / 4) * (Real.pi ^ 2 / Real.exp (Real.pi * t) ^ 2) =
          Real.pi ^ 2 / 2 * (Real.exp (Real.pi * t))⁻¹ by field_simp; norm_num]
        gcongr
        rw [← Real.exp_neg]
        exact Real.exp_le_exp.2 (by nlinarith)
    _ ≤ 2 * Real.sinh (Real.pi * t) * (Real.pi / Real.cosh (Real.pi * t)) ^ 2 := by
        gcongr
    _ ≤ 2 * Real.sinh (Real.pi * t) * (P ^ 2 * Q ^ 2) := by gcongr

/-- The constant `c₀ = (π²/4) e^{−9−2π}`. -/
def specWeightConst : ℝ := Real.pi ^ 2 / 4 * Real.exp (-9 - 2 * Real.pi)

theorem specWeightConst_pos : 0 < specWeightConst := by unfold specWeightConst; positivity

theorem lintegral_ge_of_Icc {f : ℝ → ENNReal} {a c : ℝ}
    (h : ∀ t ∈ Icc a (a + 1), ENNReal.ofReal c ≤ f t) :
    ENNReal.ofReal c ≤ ∫⁻ t, f t := by
  calc ENNReal.ofReal c = ∫⁻ _ in Icc a (a + 1), ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Icc]; simp
    _ ≤ ∫⁻ t in Icc a (a + 1), f t := setLIntegral_mono' measurableSet_Icc h
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

theorem gaussWeight_ge {K t a : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ 3 * K) :
    a ^ 2 * Real.exp (-9) ≤ gaussWeight K t := by
  unfold gaussWeight
  have hK0 : 0 < K := by linarith
  have h1 : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha hat 2
  have h2 : (t / K) ^ 2 ≤ 9 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have h3 : Real.exp (-9) ≤ Real.exp (-(t / K) ^ 2) := Real.exp_le_exp.2 (by linarith)
  exact mul_le_mul h1 h3 (Real.exp_pos _).le (sq_nonneg _)

/-- The tempered spectral weight bound: `∫ g_K · 4|W(1+it, iκ)|² ≥ c₀ (κ+1) e^{−πκ}` for `0 ≤ κ ≤ K`. -/
theorem lintegral_gaussWeight_mul_whittMellin_imag_ge {K κ : ℝ} (hK : 1 ≤ K) (hκ0 : 0 ≤ κ)
    (hκK : κ ≤ K) :
    ENNReal.ofReal (specWeightConst * (κ + 1) * Real.exp (-(Real.pi * κ))) ≤
      ∫⁻ t, ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (Complex.I * κ)‖ ^ 2)) := by
  refine lintegral_ge_of_Icc (a := κ + 1) fun t ⟨ht1, ht2⟩ => ENNReal.ofReal_le_ofReal ?_
  have hg := gaussWeight_ge (a := κ + 1) hK (by linarith) ht1 (by linarith)
  have hW := whittMellin_imag_lower hκ0 ht1 (by linarith)
  have he : Real.exp (-9 - 2 * Real.pi) * Real.exp (-(Real.pi * κ)) =
      Real.exp (-9) * Real.exp (-(Real.pi * κ) - 2 * Real.pi) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hfrac : (κ + 1) / 2 ≤ (κ + 1) ^ 2 / (κ + 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  calc specWeightConst * (κ + 1) * Real.exp (-(Real.pi * κ))
      = Real.exp (-9) * (Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi)) *
          ((κ + 1) / 2) := by
        rw [specWeightConst, mul_assoc, mul_comm (κ + 1), ← mul_assoc, mul_assoc (Real.pi ^ 2 / 4),
          he]; ring
    _ ≤ Real.exp (-9) * (Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi)) *
          ((κ + 1) ^ 2 / (κ + 2)) := by gcongr
    _ = (κ + 1) ^ 2 * Real.exp (-9) *
          (Real.pi ^ 2 / 2 * Real.exp (-(Real.pi * κ) - 2 * Real.pi) / (κ + 2)) := by
        field_simp
    _ ≤ gaussWeight K t * (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (Complex.I * κ)‖ ^ 2) :=
        mul_le_mul hg hW (by positivity) (gaussWeight_nonneg K t)

/-- **The spectral weight lower bound** for every eigenvalue `λ ≤ ¼ + K²`. -/
theorem lintegral_gaussWeight_mul_whittMellin_ge {K lam : ℝ} (hK : 1 ≤ K)
    (hlamK : lam ≤ 1 / 4 + K ^ 2) :
    ENNReal.ofReal (specWeightConst * (specKappa lam + 1) * Real.exp (-(Real.pi * specKappa lam))) ≤
      ∫⁻ t, ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam lam)‖ ^ 2)) := by
  have hπ := Real.pi_pos
  by_cases hq : lam ≤ 1 / 4
  · have hκ : specKappa lam = 0 := by
      rw [specKappa, max_eq_right (by linarith), Real.sqrt_zero]
    have hν : specParam lam = ((Real.sqrt (1 / 4 - lam) : ℝ) : ℂ) := by
      rw [specParam, if_pos hq]
    rw [hκ, hν]
    refine lintegral_ge_of_Icc (a := 1) fun t ⟨ht1, ht2⟩ => ENNReal.ofReal_le_ofReal ?_
    have hg := gaussWeight_ge (a := 1) hK zero_le_one ht1 (by linarith)
    have hW := whittMellin_real_lower (ν := Real.sqrt (1 / 4 - lam)) ht1 (by linarith)
    have he : Real.exp (-9 - 2 * Real.pi) = Real.exp (-9) * Real.exp (-(2 * Real.pi)) := by
      rw [← Real.exp_add]; ring_nf
    calc specWeightConst * (0 + 1) * Real.exp (-(Real.pi * 0))
        = 1 ^ 2 * Real.exp (-9) * (Real.pi ^ 2 / 4 * Real.exp (-(2 * Real.pi))) := by
          rw [specWeightConst, he]; simp; ring
      _ ≤ gaussWeight K t * (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I)
            ((Real.sqrt (1 / 4 - lam) : ℝ) : ℂ)‖ ^ 2) :=
          mul_le_mul hg hW (by positivity) (gaussWeight_nonneg K t)
  · push Not at hq
    set κ := Real.sqrt (lam - 1 / 4) with hκdef
    have hκ : specKappa lam = κ := by rw [specKappa, max_eq_left (by linarith)]
    have hν : specParam lam = Complex.I * κ := by rw [specParam, if_neg (not_le.2 hq)]
    have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
    have hκK : κ ≤ K := by
      rw [hκdef, Real.sqrt_le_left (by linarith)]
      linarith
    rw [hκ, hν]
    exact lintegral_gaussWeight_mul_whittMellin_imag_ge hK hκ0 hκK

/-- The spectral large-sieve weight `c₀ (κ_j+1) e^{−πκ_j}` on `λ_j ≤ ¼ + K²`, zero above. -/
def sieveWeight (K lam : ℝ) : ℝ :=
  if lam ≤ 1 / 4 + K ^ 2 then specWeightConst * (specKappa lam + 1) *
    Real.exp (-(Real.pi * specKappa lam)) else 0

theorem sieveWeight_nonneg (K lam : ℝ) : 0 ≤ sieveWeight K lam := by
  unfold sieveWeight
  split_ifs
  · have := specWeightConst_pos
    have : 0 ≤ specKappa lam := Real.sqrt_nonneg _
    positivity
  · exact le_rfl

variable {N : ℕ} {ι : Type*}

/-- **The spectral large-sieve inequality** (discrete spectrum, `K ≥ 1`):
`Σ_j c₀ (κ_j+1) e^{−πκ_j} [λ_j ≤ ¼+K²] |A_j|² ≤ |Σ_{k,l} b̄_k b_l geomRow_{kl}(1, K)|`. -/
theorem large_sieve_spectral {K : ℝ} (hK : 1 ≤ K) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    Summable (fun j : CuspEigenIndex N => sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2) ∧
      ∑' j : CuspEigenIndex N, sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2 ≤
        ‖geomForm 1 K s μ v b‖ := by
  have hK0 : 0 < K := by linarith
  have hle : ∑' j : CuspEigenIndex N, ENNReal.ofReal (sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2)
      ≤ ENNReal.ofReal (geomForm 1 K s μ v b).re := by
    refine le_trans (ENNReal.tsum_le_tsum fun j => ?_) (lintegral_bessel_le_one hK0 s hμ hv b)
    have hpt : ∀ t : ℝ, ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
          ‖specCoeff j 1 s μ v b‖ ^ 2)) =
        ENNReal.ofReal (gaussWeight K t *
          (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2)) *
          ENNReal.ofReal (‖specCoeff j 1 s μ v b‖ ^ 2) := fun t => by
      rw [← ENNReal.ofReal_mul (mul_nonneg (gaussWeight_nonneg K t) (by positivity))]
      ring_nf
    simp_rw [hpt]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (sieveWeight_nonneg K j.1)]
    refine mul_le_mul_left ?_ _
    unfold sieveWeight
    split_ifs with h
    · exact lintegral_gaussWeight_mul_whittMellin_ge hK h
    · simp
  have hfin : ∑' j : CuspEigenIndex N,
      ENNReal.ofReal (sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hnn : ∀ j : CuspEigenIndex N, 0 ≤ sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2 :=
    fun j => mul_nonneg (sieveWeight_nonneg K j.1) (by positivity)
  have hsum := ENNReal.summable_toReal hfin
  simp only [ENNReal.toReal_ofReal (hnn _)] at hsum
  refine ⟨hsum, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact hle.trans (ENNReal.ofReal_le_ofReal (Complex.re_le_norm _))

end

end GaloisForLFunctions.RHTower.DeckPointPair
