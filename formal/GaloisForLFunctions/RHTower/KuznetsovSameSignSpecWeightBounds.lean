import GaloisForLFunctions.RHTower.KuznetsovWhittakerStripBounds

/-!
# Uniform bounds for the same-sign spectral weights

A same-sign weight is *rapid* if `|h(t)| ≤ C_A t² (1+|t|)^{−A}` for every `A`.  For such weights,
uniformly in `1 ≤ σ ≤ 2` and for every `B`,

`∫ |h(t)| |W(σ+it, ν)|² dt ≤ C_B e^{−πκ} (1+κ)^{−B}`

both for `ν = ν(λ)` (`κ = κ(λ)`, `exists_bound_integral_weight_whittMellin_specParam`) and for
`ν = ir` (`κ = |r|`, `exists_bound_integral_weight_whittMellin_imag`).  The factor `t²` absorbs the
pole of `Γ(σ−½−ν+it)` at `t = 0` for the exceptional parameters, and the elementary inequality
`(1+|t|)^{L+2−A}(1+κ)^L e^{−π(2max(|t|,κ)−|t|)} ≤ K e^{−πκ}(1+κ)^{−B}(1+t²)⁻¹` (`rapid_profile_le`)
does the rest.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-- A same-sign weight with `|h(t)| ≤ C_A t² (1+|t|)^{−A}` for every `A`. -/
def SameSignWeight.IsRapid (W : SameSignWeight) : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖W.h t‖ * (1 + |t|) ^ A ≤ C * t ^ 2

/-! ## The elementary profile inequality -/

theorem one_add_pow_mul_exp_neg_le (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    (1 + κ) ^ n * Real.exp (-(Real.pi * κ / 2)) ≤ n.factorial * Real.exp 1 := by
  have h1 := Real.pow_div_factorial_le_exp (1 + κ) (by linarith) n
  rw [div_le_iff₀ (by positivity)] at h1
  have h2 : Real.exp (1 + κ) * Real.exp (-(Real.pi * κ / 2)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
  calc (1 + κ) ^ n * Real.exp (-(Real.pi * κ / 2))
      ≤ Real.exp (1 + κ) * n.factorial * Real.exp (-(Real.pi * κ / 2)) := by gcongr
    _ = n.factorial * (Real.exp (1 + κ) * Real.exp (-(Real.pi * κ / 2))) := by ring
    _ ≤ n.factorial * Real.exp 1 := by gcongr

theorem two_mul_max_sub_ge (t κ : ℝ) : κ ≤ 2 * max |t| κ - |t| := by
  rcases le_total |t| κ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- **The profile inequality**: for `A ≥ 2L + B + 4`,
`(1+|t|)^{L+2−A}(1+κ)^L e^{−π(2max(|t|,κ)−|t|)} ≤ K_B e^{−πκ}(1+κ)^{−B}(1+t²)⁻¹`, written without
negative powers. -/
theorem rapid_profile_le (L B : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℕ), 2 * L + B + 4 ≤ A → ∀ t κ : ℝ, 0 ≤ κ →
      (1 + |t|) ^ (L + 2) * (1 + κ) ^ L * Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) *
          ((1 + κ) ^ B * (1 + t ^ 2)) ≤
        K * Real.exp (-(Real.pi * κ)) * (1 + |t|) ^ A := by
  refine ⟨2 ^ (2 * L + B + 4) + (2 * L + B + 4).factorial * Real.exp 1, by positivity,
    fun A hA t κ hκ => ?_⟩
  have ht0 := abs_nonneg t
  have hb1 : 1 ≤ 1 + |t| := by linarith
  have hκ1 : 1 ≤ 1 + κ := by linarith
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t]
  rcases le_or_gt (κ / 2) |t| with h | h
  · -- `|t| ≥ κ/2`: the exponential is at most `e^{−πκ}`
    have hE : Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) ≤ Real.exp (-(Real.pi * κ)) :=
      Real.exp_le_exp.2 (by nlinarith [two_mul_max_sub_ge t κ, Real.pi_pos])
    have hκt : 1 + κ ≤ 2 * (1 + |t|) := by linarith
    have hpow : (1 + κ) ^ (L + B) ≤ 2 ^ (2 * L + B + 4) * (1 + |t|) ^ (L + B) := by
      calc (1 + κ) ^ (L + B) ≤ (2 * (1 + |t|)) ^ (L + B) := by gcongr
        _ = 2 ^ (L + B) * (1 + |t|) ^ (L + B) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) (by positivity)
    have hA' : (1 + |t|) ^ (L + 2) * (1 + |t|) ^ (L + B) * (1 + |t|) ^ 2 ≤ (1 + |t|) ^ A := by
      rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hb1 (by omega)
    calc (1 + |t|) ^ (L + 2) * (1 + κ) ^ L * Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) *
          ((1 + κ) ^ B * (1 + t ^ 2))
        ≤ (1 + |t|) ^ (L + 2) * (1 + κ) ^ L * Real.exp (-(Real.pi * κ)) *
          ((1 + κ) ^ B * (1 + |t|) ^ 2) := by gcongr
      _ = (1 + |t|) ^ (L + 2) * (1 + κ) ^ (L + B) * (1 + |t|) ^ 2 * Real.exp (-(Real.pi * κ)) := by
          rw [pow_add]; ring
      _ ≤ (1 + |t|) ^ (L + 2) * (2 ^ (2 * L + B + 4) * (1 + |t|) ^ (L + B)) * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi * κ)) := by gcongr
      _ = 2 ^ (2 * L + B + 4) * Real.exp (-(Real.pi * κ)) *
          ((1 + |t|) ^ (L + 2) * (1 + |t|) ^ (L + B) * (1 + |t|) ^ 2) := by ring
      _ ≤ 2 ^ (2 * L + B + 4) * Real.exp (-(Real.pi * κ)) * (1 + |t|) ^ A := by gcongr
      _ ≤ _ := by gcongr; linarith [show 0 ≤ ((2 * L + B + 4).factorial : ℝ) * Real.exp 1 by positivity]
  · -- `|t| < κ/2`: an extra factor `e^{−πκ/2}`
    have hE : Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) ≤
        Real.exp (-(Real.pi * κ)) * Real.exp (-(Real.pi * κ / 2)) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
      have : 2 * max |t| κ - |t| ≥ 3 * κ / 2 := by
        rw [max_eq_right (by linarith)]; linarith
      nlinarith [Real.pi_pos]
    have htκ : 1 + |t| ≤ 1 + κ := by linarith
    have hsqκ : 1 + t ^ 2 ≤ (1 + κ) ^ 2 := hsq.trans (by gcongr)
    have hpow : (1 + |t|) ^ (L + 2) ≤ (1 + κ) ^ (L + 2) := by gcongr
    have hF := one_add_pow_mul_exp_neg_le (2 * L + B + 4) κ hκ
    have hA' : 1 ≤ (1 + |t|) ^ A := one_le_pow₀ hb1
    calc (1 + |t|) ^ (L + 2) * (1 + κ) ^ L * Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) *
          ((1 + κ) ^ B * (1 + t ^ 2))
        ≤ (1 + κ) ^ (L + 2) * (1 + κ) ^ L *
          (Real.exp (-(Real.pi * κ)) * Real.exp (-(Real.pi * κ / 2))) * ((1 + κ) ^ B * (1 + κ) ^ 2) := by
          gcongr
      _ = Real.exp (-(Real.pi * κ)) * ((1 + κ) ^ (2 * L + B + 4) * Real.exp (-(Real.pi * κ / 2))) := by
          rw [show 2 * L + B + 4 = (L + 2) + L + B + 2 by omega, pow_add, pow_add, pow_add]; ring
      _ ≤ Real.exp (-(Real.pi * κ)) * ((2 * L + B + 4).factorial * Real.exp 1) := by gcongr
      _ ≤ (2 ^ (2 * L + B + 4) + (2 * L + B + 4).factorial * Real.exp 1) *
          Real.exp (-(Real.pi * κ)) * 1 := by
          rw [mul_one, mul_comm]; gcongr; linarith [show (0 : ℝ) ≤ 2 ^ (2 * L + B + 4) by positivity]
      _ ≤ _ := by gcongr

/-! ## The spectral-weight bounds -/

variable (W : SameSignWeight)

theorem integral_inv_one_add_sq_eq : ∫ t : ℝ, (1 + t ^ 2)⁻¹ = Real.pi := integral_univ_inv_one_add_sq

/-- **Pointwise domination for `ν = ν(λ)`**, uniformly in `1 ≤ σ ≤ 2`. -/
theorem exists_bound_weight_whittMellin_specParam (hW : W.IsRapid) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t lam : ℝ, 1 ≤ σ → σ ≤ 2 → 0 ≤ lam →
      ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 * (1 + specKappa lam) ^ B ≤
        C * Real.exp (-(Real.pi * specKappa lam)) * (1 + t ^ 2)⁻¹ := by
  obtain ⟨D, L, hD, hWb⟩ := exists_bound_norm_whittMellin_specParam_sq
  obtain ⟨K, hK, hprof⟩ := rapid_profile_le L B
  obtain ⟨Ch, hCh, hh⟩ := hW (2 * L + B + 4)
  refine ⟨2 * Ch * D * K, by positivity, fun σ t lam h1 h2 hlam => ?_⟩
  set κ := specKappa lam
  have hκ : 0 ≤ κ := Real.sqrt_nonneg _
  have hb1 : 0 < 1 + |t| := by linarith [abs_nonneg t]
  have hq : 0 < 1 + t ^ 2 := by positivity
  rcases eq_or_ne t 0 with ht | ht
  · have h0 : ‖W.h 0‖ = 0 := by
      have := hh 0; simp at this; exact le_antisymm (by simpa using this) (norm_nonneg _)
    rw [ht, h0]; simp only [zero_mul]; positivity
  have hw := hWb σ t lam h1 h2 hlam ht
  have hht := hh t
  have hpos : 0 < (1 + |t|) ^ (2 * L + B + 4) := by positivity
  have hpr := hprof (2 * L + B + 4) le_rfl t κ hκ
  -- `t² (1 + t⁻²) = t² + 1`
  have ht2 : t ^ 2 * (1 + (t ^ 2)⁻¹) = 1 + t ^ 2 := by field_simp; ring
  have hmain : ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 *
      (1 + κ) ^ B * (1 + t ^ 2) * (1 + |t|) ^ (2 * L + B + 4) ≤
      Ch * t ^ 2 * (D * (1 + |t|) ^ L * (1 + κ) ^ L *
        Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * (1 + (t ^ 2)⁻¹)) * (1 + κ) ^ B * (1 + t ^ 2) := by
    calc _ = (‖W.h t‖ * (1 + |t|) ^ (2 * L + B + 4)) *
          ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 * (1 + κ) ^ B * (1 + t ^ 2) := by
          ring
      _ ≤ (Ch * t ^ 2) * (D * (1 + |t|) ^ L * (1 + κ) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * (1 + (t ^ 2)⁻¹)) * (1 + κ) ^ B *
            (1 + t ^ 2) := by gcongr
      _ = _ := by ring
  have hreorg : Ch * t ^ 2 * (D * (1 + |t|) ^ L * (1 + κ) ^ L *
        Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * (1 + (t ^ 2)⁻¹)) * (1 + κ) ^ B * (1 + t ^ 2) =
      Ch * D * ((1 + |t|) ^ L * (1 + t ^ 2)) * (1 + κ) ^ L *
        Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * ((1 + κ) ^ B * (1 + t ^ 2)) := by
    rw [← ht2]; ring
  have hle2 : (1 + |t|) ^ L * (1 + t ^ 2) ≤ 2 * (1 + |t|) ^ (L + 2) := by
    rw [pow_add]; nlinarith [sq_abs t, abs_nonneg t, pow_pos hb1 L]
  have hfin : Ch * D * ((1 + |t|) ^ L * (1 + t ^ 2)) * (1 + κ) ^ L *
        Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * ((1 + κ) ^ B * (1 + t ^ 2)) ≤
      2 * Ch * D * (K * Real.exp (-(Real.pi * κ)) * (1 + |t|) ^ (2 * L + B + 4)) := by
    calc _ ≤ Ch * D * (2 * (1 + |t|) ^ (L + 2)) * (1 + κ) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * ((1 + κ) ^ B * (1 + t ^ 2)) := by gcongr
      _ = 2 * Ch * D * ((1 + |t|) ^ (L + 2) * (1 + κ) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| κ - |t|))) * ((1 + κ) ^ B * (1 + t ^ 2))) := by ring
      _ ≤ _ := by gcongr
  have hall := (hmain.trans (le_of_eq hreorg)).trans hfin
  have key : ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 *
      (1 + κ) ^ B * (1 + t ^ 2) ≤ 2 * Ch * D * K * Real.exp (-(Real.pi * κ)) := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc _ ≤ 2 * Ch * D * (K * Real.exp (-(Real.pi * κ)) * (1 + |t|) ^ (2 * L + B + 4)) := hall
      _ = _ := by ring
  calc ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 * (1 + κ) ^ B
      = (‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 * (1 + κ) ^ B *
          (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ := by field_simp
    _ ≤ (2 * Ch * D * K * Real.exp (-(Real.pi * κ))) * (1 + t ^ 2)⁻¹ := by gcongr


/-- **Pointwise domination for `ν = ir`**, uniformly in `1 ≤ σ ≤ 2`. -/
theorem exists_bound_weight_whittMellin_imag (hW : W.IsRapid) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t r : ℝ, 1 ≤ σ → σ ≤ 2 →
      ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 * (1 + |r|) ^ B ≤
        C * Real.exp (-(Real.pi * |r|)) * (1 + t ^ 2)⁻¹ := by
  obtain ⟨D, L, hD, hWb⟩ := exists_bound_norm_whittMellin_imag_sq
  obtain ⟨K, hK, hprof⟩ := rapid_profile_le L B
  obtain ⟨Ch, hCh, hh⟩ := hW (2 * L + B + 4)
  refine ⟨Ch * D * K, by positivity, fun σ t r h1 h2 => ?_⟩
  have hb1 : 0 < 1 + |t| := by linarith [abs_nonneg t]
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hpos : 0 < (1 + |t|) ^ (2 * L + B + 4) := by positivity
  have hw := hWb σ t r h1 h2
  have hht := hh t
  have hpr := hprof (2 * L + B + 4) le_rfl t |r| (abs_nonneg r)
  have ht2 : t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have key : ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
      (1 + |r|) ^ B * (1 + t ^ 2) ≤ Ch * D * K * Real.exp (-(Real.pi * |r|)) := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
          (1 + |r|) ^ B * (1 + t ^ 2) * (1 + |t|) ^ (2 * L + B + 4)
        = (‖W.h t‖ * (1 + |t|) ^ (2 * L + B + 4)) *
          ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 * ((1 + |r|) ^ B * (1 + t ^ 2)) := by
          ring
      _ ≤ (Ch * t ^ 2) * (D * (1 + |t|) ^ L * (1 + |r|) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| |r| - |t|)))) * ((1 + |r|) ^ B * (1 + t ^ 2)) := by
          gcongr
      _ ≤ (Ch * (1 + |t|) ^ 2) * (D * (1 + |t|) ^ L * (1 + |r|) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| |r| - |t|)))) * ((1 + |r|) ^ B * (1 + t ^ 2)) := by
          gcongr
      _ = Ch * D * ((1 + |t|) ^ (L + 2) * (1 + |r|) ^ L *
          Real.exp (-(Real.pi * (2 * max |t| |r| - |t|))) * ((1 + |r|) ^ B * (1 + t ^ 2))) := by
          rw [pow_add]; ring
      _ ≤ Ch * D * (K * Real.exp (-(Real.pi * |r|)) * (1 + |t|) ^ (2 * L + B + 4)) := by gcongr
      _ = _ := by ring
  calc ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 * (1 + |r|) ^ B
      = (‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 * (1 + |r|) ^ B *
          (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ := by field_simp
    _ ≤ (Ch * D * K * Real.exp (-(Real.pi * |r|))) * (1 + t ^ 2)⁻¹ := by gcongr

theorem continuous_whittMellin_line_imag {σ : ℝ} (hσ : 1 / 2 < σ) (r : ℝ) :
    Continuous fun t : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) :=
  continuous_iff_continuousAt.2 fun t =>
    (continuousAt_whittMellin_imag (t := t) (r := r) hσ).comp
      (f := fun t : ℝ => (σ, t, r)) (by fun_prop : Continuous fun t : ℝ =>
        ((σ, t, r) : ℝ × ℝ × ℝ)).continuousAt

/-- **The spectral weight at `ν(λ)`**: integrable, with `|∫ h |W|²| (1+κ)^B ≤ C e^{−πκ}`. -/
theorem exists_bound_specWeight_specParam (hW : W.IsRapid) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ lam : ℝ, 1 ≤ σ → σ ≤ 2 → 0 ≤ lam →
      Integrable (fun t : ℝ => W.h t *
          ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 : ℝ) : ℂ)) ∧
        ‖specWeight W σ (specParam lam)‖ * (1 + specKappa lam) ^ B ≤
          C * Real.exp (-(Real.pi * specKappa lam)) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_weight_whittMellin_specParam W hW B
  refine ⟨Real.pi * C, by positivity, fun σ lam h1 h2 hlam => ?_⟩
  set κ := specKappa lam
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ1 : 0 < (1 + κ) ^ B := pow_pos (by linarith) B
  have hpt : ∀ t : ℝ, ‖W.h t * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (C * Real.exp (-(Real.pi * κ)) / (1 + κ) ^ B) * (1 + t ^ 2)⁻¹ := fun t => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
      le_div_iff₀ hκ1]
    calc ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 * (1 + κ) ^ B
        ≤ C * Real.exp (-(Real.pi * κ)) * (1 + t ^ 2)⁻¹ := hb σ t lam h1 h2 hlam
      _ = _ := by ring
  have hint : Integrable (fun t : ℝ => W.h t *
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 : ℝ) : ℂ)) :=
    (integrable_inv_one_add_sq.const_mul _).mono'
      (W.continuous_h.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp
        (measurable_specCoeff_line lam hlam h1)).aestronglyMeasurable)
      (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  rw [← le_div_iff₀ hκ1, specWeight]
  refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

/-- **The spectral weight at `ir`**: integrable, with `|∫ h |W|²| (1+|r|)^B ≤ C e^{−π|r|}`. -/
theorem exists_bound_specWeight_imag (hW : W.IsRapid) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ r : ℝ, 1 ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => W.h t *
          ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ)) ∧
        ‖specWeight W σ (r * Complex.I)‖ * (1 + |r|) ^ B ≤ C * Real.exp (-(Real.pi * |r|)) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_weight_whittMellin_imag W hW B
  refine ⟨Real.pi * C, by positivity, fun σ r h1 h2 => ?_⟩
  have hκ1 : 0 < (1 + |r|) ^ B := pow_pos (by linarith [abs_nonneg r]) B
  have hpt : ∀ t : ℝ, ‖W.h t * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (C * Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ B) * (1 + t ^ 2)⁻¹ := fun t => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
      le_div_iff₀ hκ1]
    calc ‖W.h t‖ * ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 * (1 + |r|) ^ B
        ≤ C * Real.exp (-(Real.pi * |r|)) * (1 + t ^ 2)⁻¹ := hb σ t r h1 h2
      _ = _ := by ring
  have hint : Integrable (fun t : ℝ => W.h t *
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ)) :=
    (integrable_inv_one_add_sq.const_mul _).mono'
      (W.continuous_h.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        ((continuous_whittMellin_line_imag (by linarith) r).norm.pow 2)).aestronglyMeasurable)
      (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  rw [← le_div_iff₀ hκ1, specWeight]
  refine (norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
