import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.BoxLogDerivative

/-! The finite quadratic sums give centered Chebyshev estimates for characters with a zero-free box. -/

open Complex Filter UpperTheory.Top WindowedLandauTheory.HC

namespace QH

private theorem eventually_box_truncation {ε K : ℝ} (hε : 0 < ε) (hK : 1 ≤ K) :
    ∀ᶠ Y : ℝ in atTop,
      2 ≤ (Y ^ K) ^ (400 : ℕ) ∧ ((Y ^ K) ^ (400 : ℕ)) ^ 8 + 2 ≤ Real.exp (Y ^ (ε / 6)) ∧
      100000000 * (1 + Real.log ((Y ^ K) ^ (400 : ℕ))) ^ 2 ≤ Y ^ (3 * ε / 4) := by
  let D := 3200 * K + 1
  let C := 100000000 * (1 + 400 * K) ^ 2
  have hD : 0 < D := by dsimp [D]; linarith only [hK]
  have hC : 0 < C := by dsimp [C]; positivity
  have hb := (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < ε / 6)).bound
    (c := 1 / D) (by positivity)
  have hpoly := (isLittleO_log_rpow_rpow_atTop 2 (by positivity : (0 : ℝ) < 3 * ε / 4)).bound
    (c := 1 / C) (by positivity)
  filter_upwards [eventually_ge_atTop (max 3 (Real.exp 1)), hb, hpoly] with Y hY hbound hpol
  have hY₃ := (le_max_left _ _).trans hY
  have hY₀ : 0 < Y := by linarith only [hY₃]
  have hY₁ : 1 ≤ Y := by linarith only [hY₃]
  have hlog : 1 ≤ Real.log Y := (Real.le_log_iff_exp_le hY₀).mpr ((le_max_right _ _).trans hY)
  rw [Real.norm_of_nonneg (Real.log_nonneg hY₁), Real.norm_of_nonneg (by positivity), one_div,
    inv_mul_eq_div, le_div_iff₀ hD] at hbound
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity),
    one_div, inv_mul_eq_div, le_div_iff₀ hC] at hpol
  let X := Y ^ K
  let z := X ^ (400 : ℕ)
  have hX : Y ≤ X := by
    exact (Real.rpow_one Y).symm.le.trans (Real.rpow_le_rpow_of_exponent_le hY₁ hK)
  have hX₁ : 1 ≤ X := hY₁.trans hX
  have hz : 2 ≤ z := (by linarith only [hY₃] : 2 ≤ Y).trans
    (hX.trans (le_self_pow₀ hX₁ (by norm_num)))
  refine ⟨hz, ?_, ?_⟩
  · have hpow : z ^ 8 = Y ^ (3200 * K) := by
      have hz' : z = Y ^ (K * 400) := by
        dsimp [X, z]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY₀.le]
        norm_num
      rw [hz', ← Real.rpow_natCast, ← Real.rpow_mul hY₀.le]
      congr 1
      push_cast
      ring
    have hz₈ : 1 ≤ z ^ 8 := one_le_pow₀ (one_le_two.trans hz)
    have hb' : Real.log Y * D ≤ Y ^ (ε / 6) := hbound
    calc z ^ 8 + 2 ≤ z ^ 8 * Y := by
          have hm := mul_le_mul_of_nonneg_left hY₃ (show 0 ≤ z ^ 8 by positivity)
          linarith only [hm, hz₈]
      _ = Y ^ D := by rw [hpow, ← Real.rpow_add_one hY₀.ne']
      _ ≤ _ := by rw [Real.rpow_def_of_pos hY₀]; exact Real.exp_le_exp.mpr hb'
  · have hlogz : Real.log z = 400 * K * Real.log Y := by
      dsimp [z, X]
      rw [Real.log_pow, Real.log_rpow hY₀]
      push_cast
      ring
    have hl (h : 1 ≤ z) : 0 ≤ 1 + Real.log z := by
      have := Real.log_nonneg h
      linarith
    have hlogle : 1 + Real.log z ≤ (1 + 400 * K) * Real.log Y := by
      rw [hlogz, add_mul, one_mul]
      linarith only [hlog]
    calc 100000000 * (1 + Real.log z) ^ 2 ≤
          100000000 * ((1 + 400 * K) * Real.log Y) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hl (one_le_two.trans hz)) hlogle 2) (by norm_num)
      _ = Real.log Y ^ 2 * C := by dsimp [C]; ring
      _ ≤ _ := hpol

theorem box_of_S :
    ∃ C : ℝ, 0 < C ∧ ∀ ε τ K : ℝ, 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K →
      ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
        (q : ℕ) (κ : ℕ → ℂ),
        Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → χ.IsPrimitive →
        GoodC Q χ → (∀ n : ℕ, χ n = κ n * J q n) →
        (∀ y ∈ Set.Icc Y (Y ^ K), ‖S ((Y ^ K) ^ (400 : ℕ)) y q κ‖ ≤ y ^ (1 / 2 + τ) / 2) →
        Box Q C τ Y (Y ^ K) χ := by
  obtain ⟨L₀, hL₀, hkap⟩ := logDerivativeAtOne_le_loglog
  have hlog₄ : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨55 + Real.log 4, by linarith only [hlog₄], fun ε τ K hε hε' hτ hK => ?_⟩
  have hL := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 6)).eventually_ge_atTop L₀
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (Real.exp 4)).and (hL.and (eventually_box_truncation hε hK)))
  refine ⟨Y₀, fun Y hY Q N _ χ q κ hlo hhi hp hg hval hS => ?_⟩
  obtain ⟨hYe, hYl, hz, hzQ, hzlog⟩ := hY₀ Y hY
  have hY₀' : 0 < Y := (Real.exp_pos _).trans_le hYe
  have hlogY : 4 ≤ Real.log Y := (Real.le_log_iff_exp_le hY₀').mpr hYe
  have hYe' : 16 ≤ Y := by
    have h := Real.exp_one_gt_d9
    have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [h]
    have h₄ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 4
    rw [← Real.exp_nat_mul] at h₄
    norm_num at h₄
    exact h₄.trans hYe
  have hY₁ : 1 ≤ Y := by linarith only [hYe']
  have hQ₀ : 0 < Q := (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N).trans_le hg.2.1
  have hLogQ : 1 ≤ Real.log Q := hL₀.trans (hYl.trans hlo)
  have hlogQ := Real.log_le_log (zero_lt_one.trans_le hLogQ) hhi
  rw [Real.log_rpow hY₀'] at hlogQ
  refine ⟨hg, ?_, fun y hy => ?_⟩
  · have h := hkap Q N χ (hYl.trans hlo) hp hg
    have hεlog := mul_le_mul_of_nonneg_right hε' (Real.log_nonneg hY₁)
    have hconst := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.log Y by linarith only [hlogY])
      (show 0 ≤ Real.log 4 + 5 by linarith only [hlog₄])
    linarith only [h, hεlog, hlogQ, hconst]
  let X := Y ^ K
  let z := X ^ (400 : ℕ)
  have hX : 1 ≤ X := Real.one_le_rpow hY₁ (by positivity)
  have hy₁ := hY₁.trans hy.1
  have hyz : y ≤ z := hy.2.trans (le_self_pow₀ hX (by norm_num))
  have hQ := hzQ.trans ((Real.le_log_iff_exp_le hQ₀).mp hlo)
  have hNQ := Real.log_le_log (by exact_mod_cast NeZero.pos N) hg.2.1
  have hNlo : 1 + Real.log N ≤ 2 * Y ^ (ε / 4) := by linarith only [hNQ, hhi, hLogQ]
  have hKpow : z ^ (-1 / 400 : ℝ) = X⁻¹ := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hX),
      show (400 : ℝ) * (-1 / 400) = -1 by norm_num, Real.rpow_neg_one]
  have htail : ‖(y : ℂ) * (partialLogDerivative χ z + An.logDerivativeAtOne χ)‖ ≤ Y ^ ε := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hy₁)]
    have h := norm_partialLogDerivative_error_le hg.1 hp hg.2.2 hz hQ
    rw [hKpow] at h
    calc _ ≤ X * (50000000 * (1 + Real.log N) * (1 + Real.log z) ^ 2 * X⁻¹) :=
          mul_le_mul hy.2 h (norm_nonneg _) (zero_le_one.trans hX)
      _ = 50000000 * (1 + Real.log N) * (1 + Real.log z) ^ 2 := by
        field_simp [(zero_lt_one.trans_le hX).ne']
      _ ≤ Y ^ (ε / 4) * (100000000 * (1 + Real.log z) ^ 2) := by
        have hh := mul_le_mul_of_nonneg_right hNlo (show 0 ≤ 50000000 * (1 + Real.log z) ^ 2 by positivity)
        linarith only [hh]
      _ ≤ Y ^ (ε / 4) * Y ^ (3 * ε / 4) :=
          mul_le_mul_of_nonneg_left hzlog (by positivity)
      _ = _ := by rw [← Real.rpow_add hY₀']; congr 1; ring
  have hnum : Y ^ ε ≤ y ^ (1 / 2 + τ) / 2 := by
    have h₁ := Real.rpow_le_rpow_of_exponent_le hY₁ hε'
    have h₂ : 2 ≤ Y ^ (1 / 4 : ℝ) := by
      calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ _ := Real.rpow_le_rpow (by norm_num) hYe' (by norm_num)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc Y ^ ε * 2 ≤ Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := mul_le_mul h₁ h₂ (by norm_num) (by positivity)
      _ = Y ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hY₀']; norm_num
      _ ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hY₀'.le hy.1 (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hy₁ (by linarith only [hτ])
  rw [gChi_eq_truncated hg.1 hy₁ hyz hval]
  have hs := hS y hy
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  linarith only [hs, htail, hnum]

end QH
