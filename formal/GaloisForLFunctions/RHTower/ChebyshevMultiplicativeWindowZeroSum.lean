import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound

/-!
# Multiplicative windows: a zero sum with height-independent coefficients

Scaling both ends of a window by `x > 0` multiplies its zero term by `x^ρ`:
`T(ρ; lx, mx) = x^ρ T(ρ; l, m)` (`lagWindowZeroTerm_mul_scale`).  The two-window squeeze, kept in
signed form (`psi_window_ge_add_re_tsum`), then reads for `h = δx`, `h' = ηx`

`ψ(x + δx) - ψ(x) ≥ (δ - 2η)x - 4/(η x²) + Re Σ_ρ x^ρ d_ρ`,
`d_ρ = T(ρ; 1+δ-η, 1+δ) - T(ρ; 1, 1+η)`

(`psi_mul_window_ge`), with coefficients independent of `x`.  For `0 < 2η ≤ δ ≤ 1` they obey
`|d_ρ| ≤ 2δ` and `|d_ρ| ≤ 12/(η|ρ||1-ρ|)`.
-/

namespace RHTower

noncomputable section

open Complex

/-- **Scaling a window.**  `T(ρ; lx, mx) = x^ρ T(ρ; l, m)` for `x > 0`, `0 < l < m`. -/
theorem lagWindowZeroTerm_mul_scale {x l m : ℝ} (hx : 0 < x) (hl : 0 < l) (hlm : l < m)
    (ρ : ℂ) :
    lagWindowZeroTerm ρ (l * x) (m * x) = (x : ℂ) ^ ρ * lagWindowZeroTerm ρ l m := by
  have hm : 0 < m := lt_trans hl hlm
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hw : 0 < 1 / l - 1 / m := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hl hlm
  have hwC : ((1 / l - 1 / m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have h1 : ((m * x : ℝ) : ℂ) ^ (ρ - 1) = (m : ℂ) ^ (ρ - 1) * (x : ℂ) ^ (ρ - 1) := by
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg hm.le hx.le _
  have h2 : ((l * x : ℝ) : ℂ) ^ (ρ - 1) = (l : ℂ) ^ (ρ - 1) * (x : ℂ) ^ (ρ - 1) := by
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg hl.le hx.le _
  have h3 : ((1 / (l * x) - 1 / (m * x) : ℝ) : ℂ) = ((1 / l - 1 / m : ℝ) : ℂ) / (x : ℂ) := by
    push_cast
    field_simp
  have h4 : (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ / (x : ℂ) := by
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  rw [lagWindowZeroTerm, lagWindowZeroTerm, h1, h2, h3, h4]
  generalize ((1 / l - 1 / m : ℝ) : ℂ) = W at hwC ⊢
  rcases eq_or_ne (ρ * (1 - ρ)) 0 with hρ | hρ
  · rw [mul_assoc ρ, ← mul_assoc ρ (1 - ρ), hρ]
    simp
  field_simp

/-- **The `ψ` window lower bound, signed form.**  As `psi_window_ge_sub_tsum`, keeping the zero sum
inside the real part. -/
theorem psi_window_ge_add_re_tsum {x h h' : ℝ} (hx : 2 ≤ x) (hh' : 0 < h') (hh'h : 2 * h' ≤ h)
    (hhx : h ≤ x) :
    h - 2 * h' - 4 / (x * h')
        + (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) (x + h - h') (x + h)
            - lagWindowZeroTerm (q.1 : ℂ) x (x + h'))).re
      ≤ Chebyshev.psi (x + h) - Chebyshev.psi x := by
  set a₁ := x + h - h' with ha₁
  set b₁ := x + h with hb₁
  set b₂ := x + h' with hb₂
  have hx1 : 1 < x := by linarith
  have ha₁1 : 1 < a₁ := by rw [ha₁]; linarith
  have hab₁ : a₁ < b₁ := by rw [ha₁, hb₁]; linarith
  have hab₂ : x < b₂ := by rw [hb₂]; linarith
  have ha₁0 : 0 < a₁ := by linarith
  have hx0 : 0 < x := by linarith
  have hw₁ : 0 < 1 / a₁ - 1 / b₁ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha₁0 hab₁
  have hw₂ : 0 < 1 / x - 1 / b₂ := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 hab₂
  have hsq₁ := (chebyshevLagWindow_bounds ha₁0 hab₁.le).2
  have hsq₂ := (chebyshevLagWindow_bounds hx0 hab₂.le).1
  have hψ₁ : chebyshevLagWindow a₁ b₁ / (1 / a₁ - 1 / b₁) ≤ Chebyshev.psi b₁ := by
    rw [div_le_iff₀ hw₁]
    exact hsq₁
  have hψ₂ : Chebyshev.psi x ≤ chebyshevLagWindow x b₂ / (1 / x - 1 / b₂) := by
    rw [le_div_iff₀ hw₂]
    exact hsq₂
  rw [chebyshevLagWindow_div_eq ha₁1 hab₁] at hψ₁
  rw [chebyshevLagWindow_div_eq hx1 hab₂] at hψ₂
  have hL₁ : a₁ ≤ Real.log (b₁ / a₁) / (1 / a₁ - 1 / b₁) := by
    rw [le_div_iff₀ hw₁]
    exact (log_div_le_mul_inv_sub ha₁0 hab₁.le).1
  have hL₂ : Real.log (b₂ / x) / (1 / x - 1 / b₂) ≤ b₂ := by
    rw [div_le_iff₀ hw₂]
    exact (log_div_le_mul_inv_sub hx0 hab₂.le).2
  have hE₁ : 0 ≤ (trivialZeroSeriesReal a₁ / a₁ - trivialZeroSeriesReal b₁ / b₁)
      / (1 / a₁ - 1 / b₁) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha₁1.le hab₁.le)) hw₁.le
  have hE₂ : (trivialZeroSeriesReal x / x - trivialZeroSeriesReal b₂ / b₂) / (1 / x - 1 / b₂)
      ≤ 4 / (x * h') := by
    have hEb := trivialZeroSeriesReal_nonneg (hx1.le.trans hab₂.le)
    have hEx := trivialZeroSeriesReal_le_two_div_sq hx
    have hb₂0 : 0 < b₂ := by linarith
    have hnum : trivialZeroSeriesReal x / x - trivialZeroSeriesReal b₂ / b₂ ≤ 2 / x ^ 2 / x := by
      have : 0 ≤ trivialZeroSeriesReal b₂ / b₂ := div_nonneg hEb hb₂0.le
      have : trivialZeroSeriesReal x / x ≤ 2 / x ^ 2 / x :=
        div_le_div_of_nonneg_right hEx hx0.le
      linarith
    have hweq : 1 / x - 1 / b₂ = h' / (x * b₂) := by
      rw [hb₂]
      field_simp
      ring
    rw [div_le_iff₀ hw₂, hweq]
    refine le_trans hnum ?_
    rw [show 4 / (x * h') * (h' / (x * b₂)) = 4 / (x ^ 2 * b₂) by field_simp, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hb₂]
    nlinarith
  have hs₁ := summable_norm_lagWindowZeroTerm ha₁1.le hab₁
  have hs₂ := summable_norm_lagWindowZeroTerm hx1.le hab₂
  have hdiff : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a₁ b₁).re
      - (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x b₂).re
      = (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) a₁ b₁
          - lagWindowZeroTerm (q.1 : ℂ) x b₂)).re := by
    rw [← Complex.sub_re, ← (Summable.of_norm hs₁).tsum_sub (Summable.of_norm hs₂)]
  have hab : a₁ - b₂ = h - 2 * h' := by rw [ha₁, hb₂]; ring
  linarith

/-- The coefficient of `x^ρ` in the multiplicative two-window zero sum. -/
def multWindowCoeff (δ η : ℝ) (ρ : ℂ) : ℂ :=
  lagWindowZeroTerm ρ (1 + δ - η) (1 + δ) - lagWindowZeroTerm ρ 1 (1 + η)

/-- **The multiplicative window lower bound.**  For `2 ≤ x`, `0 < η`, `2η ≤ δ ≤ 1`:
`ψ(x + δx) - ψ(x) ≥ (δ - 2η)x - 4/(η x²) + Re Σ_ρ x^ρ d_ρ`. -/
theorem psi_mul_window_ge {x δ η : ℝ} (hx : 2 ≤ x) (hη : 0 < η) (hηδ : 2 * η ≤ δ)
    (hδ : δ ≤ 1) :
    (δ - 2 * η) * x - 4 / (η * x ^ 2)
        + (∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ)).re
      ≤ Chebyshev.psi (x + δ * x) - Chebyshev.psi x := by
  have hx0 : 0 < x := by linarith
  have h := psi_window_ge_add_re_tsum (h := δ * x) (h' := η * x) hx (by positivity)
    (by nlinarith) (by nlinarith)
  have hsum : (∑' q : XiZeroCopy, (lagWindowZeroTerm (q.1 : ℂ) (x + δ * x - η * x) (x + δ * x)
      - lagWindowZeroTerm (q.1 : ℂ) x (x + η * x)))
      = ∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ) := by
    refine tsum_congr fun q => ?_
    have e1 : x + δ * x - η * x = (1 + δ - η) * x := by ring
    have e2 : x + δ * x = (1 + δ) * x := by ring
    have e3 : x = 1 * x := by ring
    have e4 : x + η * x = (1 + η) * x := by ring
    rw [e1, e2, e4]
    conv_lhs => rw [show lagWindowZeroTerm (q.1 : ℂ) x ((1 + η) * x)
      = lagWindowZeroTerm (q.1 : ℂ) (1 * x) ((1 + η) * x) by rw [one_mul]]
    rw [lagWindowZeroTerm_mul_scale hx0 (by linarith) (by linarith),
      lagWindowZeroTerm_mul_scale hx0 one_pos (by linarith), multWindowCoeff, mul_sub]
  rw [hsum] at h
  have e5 : δ * x - 2 * (η * x) - 4 / (x * (η * x)) = (δ - 2 * η) * x - 4 / (η * x ^ 2) := by
    rw [show x * (η * x) = η * x ^ 2 by ring]
    ring
  linarith

/-- **Short range.**  `|d_ρ| ≤ 2δ`. -/
theorem norm_multWindowCoeff_le_two_mul {δ η : ℝ} (hη : 0 < η) (hηδ : 2 * η ≤ δ) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) : ‖multWindowCoeff δ η ρ‖ ≤ 2 * δ := by
  have h := norm_lagWindowZeroTerm_sub_le (x := 1) (H := δ) (a₁ := 1 + δ - η) (b₁ := 1 + δ)
    (a₂ := 1) (b₂ := 1 + η) one_pos (by linarith) (by linarith) le_rfl le_rfl (by linarith)
    (by linarith) hρ0 hρ1
  rwa [Real.one_rpow, mul_one] at h

/-- `‖T(ρ; a, b)‖ ≤ 2/(|ρ||1-ρ| w)` for `1 ≤ a < b` and any `0 < w ≤ 1/a - 1/b`. -/
theorem norm_lagWindowZeroTerm_le_of_width {a b w : ℝ} (ha : 1 ≤ a) (hab : a < b) (hw : 0 < w)
    (hwab : w ≤ 1 / a - 1 / b) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖lagWindowZeroTerm ρ a b‖ ≤ 2 / (‖ρ‖ * ‖1 - ρ‖ * w) := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hP : 0 < ‖ρ‖ * ‖1 - ρ‖ := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
  have h := norm_lagWindowZeroTerm_le (lt_of_lt_of_le one_pos ha) hab ρ
  have hpa : a ^ (ρ.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have hpb : b ^ (ρ.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hD : 0 < ‖ρ‖ * ‖1 - ρ‖ * (1 / a - 1 / b) := mul_pos hP (lt_of_lt_of_le hw hwab)
  refine le_trans h ?_
  calc (a ^ (ρ.re - 1) + b ^ (ρ.re - 1)) / (‖ρ‖ * ‖1 - ρ‖ * (1 / a - 1 / b))
      ≤ 2 / (‖ρ‖ * ‖1 - ρ‖ * (1 / a - 1 / b)) :=
        div_le_div_of_nonneg_right (by linarith) hD.le
    _ ≤ 2 / (‖ρ‖ * ‖1 - ρ‖ * w) := by gcongr

/-- **Long range.**  `|d_ρ| ≤ 12/(η|ρ||1-ρ|)` for `0 < 2η ≤ δ ≤ 1`. -/
theorem norm_multWindowCoeff_le_div {δ η : ℝ} (hη : 0 < η) (hηδ : 2 * η ≤ δ) (hδ : δ ≤ 1)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖multWindowCoeff δ η ρ‖ ≤ 12 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hρ1ne : 1 - ρ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hP : 0 < ‖ρ‖ * ‖1 - ρ‖ := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
  have hw₁ : η / 4 ≤ 1 / (1 + δ - η) - 1 / (1 + δ) := by
    have h1 : 0 < 1 + δ - η := by linarith
    have h2 : 0 < 1 + δ := by linarith
    have h4 : (1 + δ - η) * (1 + δ) ≤ 4 := by nlinarith
    rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hη.le]
  have hw₂ : η / 2 ≤ 1 / 1 - 1 / (1 + η) := by
    have h2 : 0 < 1 + η := by linarith
    rw [div_one, one_sub_div h2.ne', div_le_div_iff₀ (by norm_num) h2]
    nlinarith
  have hT₁ := norm_lagWindowZeroTerm_le_of_width (a := 1 + δ - η) (b := 1 + δ) (by linarith)
    (by linarith) (by positivity) hw₁ hρ0 hρ1
  have hT₂ := norm_lagWindowZeroTerm_le_of_width (a := 1) (b := 1 + η) le_rfl (by linarith)
    (by positivity) hw₂ hρ0 hρ1
  have e₁ : 2 / (‖ρ‖ * ‖1 - ρ‖ * (η / 4)) = 8 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
    field_simp
    ring
  have e₂ : 2 / (‖ρ‖ * ‖1 - ρ‖ * (η / 2)) = 4 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by
    field_simp
    ring
  rw [e₁] at hT₁
  rw [e₂] at hT₂
  have e₃ : 12 / (η * (‖ρ‖ * ‖1 - ρ‖))
      = 8 / (η * (‖ρ‖ * ‖1 - ρ‖)) + 4 / (η * (‖ρ‖ * ‖1 - ρ‖)) := by ring
  rw [multWindowCoeff, e₃]
  exact le_trans (norm_sub_le _ _) (add_le_add hT₁ hT₂)

end

end RHTower
