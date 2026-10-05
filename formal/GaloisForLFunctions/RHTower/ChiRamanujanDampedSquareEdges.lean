import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareContour

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval
namespace RHTower.BAGTrace

private theorem square_rectangle_bound :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ j : ℕ, ∃ C > 0,
    ∀ {T δ ε b X x t : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 ≤ X →
      x ∈ Icc (1-δ) (1+b) → |t| ≤ T →
      ‖dampedSquareContourIntegrand ε X ((x : ℂ)+t*I)‖ ≤
        C*X^x*(1+|t|)^54*
          (1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖)/(1+|t|)^j := by
  obtain ⟨c,hc,A,hA,hsource⟩ := exists_dampedSquareContinuation_remainder_bound
  have hc0 : 0 < c := hc.1
  let d := c/4
  refine ⟨d,⟨by dsimp [d]; positivity,by dsimp [d]; linarith [hc.2]⟩,?_⟩
  intro j
  obtain ⟨B,hB,hM⟩ := exists_dampedSquareWindowMellin_rapidDecay j 1
  refine ⟨A*B,by positivity,?_⟩
  intro T δ ε b X x t hT hδ hδd hε hεδ hb hbδ hX hx ht
  have hbase : 1 ≤ (1+T)^9 := one_le_pow₀ (by linarith)
  have hδsmall : δ ≤ d := hδd.trans (div_le_self (by dsimp [d]; positivity) hbase)
  have hδ1 : δ ≤ 1 := by dsimp [d] at hδsmall; linarith [hc.2]
  have hrad : 2*δ ≤ c/(1+|t|)^9 := by
    calc 2*δ ≤ 2*(d/(1+T)^9) := by gcongr
      _ = (c/2)/(1+T)^9 := by dsimp [d]; ring
      _ ≤ c/(1+T)^9 := by gcongr; linarith [hc.1]
      _ ≤ c/(1+|t|)^9 := by gcongr
  have hdist : dist (((x : ℂ)+t*I)+ε) (1+(t : ℂ)*I) ≤ c/(1+|t|)^9 := by
    rw [dist_eq_norm,show (((x : ℂ)+t*I)+ε)-(1+(t : ℂ)*I) =
      ((x+ε-1 : ℝ) : ℂ) by push_cast; ring,Complex.norm_real,Real.norm_eq_abs]
    exact (show |x+ε-1| ≤ 2*δ from abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩).trans hrad
  have heps : ‖(ε : ℂ)‖ ≤ c/(1+|t|)^9 := by
    rw [Complex.norm_real,Real.norm_of_nonneg hε.le]
    exact (show ε ≤ 2*δ by linarith).trans hrad
  have hJ : ‖(dampedSquareContinuation ε ((x : ℂ)+t*I)-1)/(ε : ℂ)^2‖ ≤
      A*(1+|t|)^54*(1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖) := by
    have h := hsource t ((x : ℂ)+t*I) ε hdist heps
    rw [Complex.norm_real,Real.norm_of_nonneg hε.le] at h
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hε.le,
      div_le_iff₀ (sq_pos_of_pos hε)]
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have hstrip : |(((x : ℂ)+t*I)).re-1| ≤ 1 := by
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero]
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hm : ‖dampedSquareWindowMellin ((x : ℂ)+t*I)‖ ≤ B/(1+|t|)^j := by
    simpa using hM ((x : ℂ)+t*I) hstrip
  have hp : ‖(X : ℂ)^((x : ℂ)+t*I)‖ = X^x := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < X) ((x : ℂ)+t*I)
  unfold dampedSquareContourIntegrand
  rw [norm_mul,norm_mul,hp]
  calc _ ≤ (A*(1+|t|)^54*(1+‖((((x : ℂ)+t*I)-1)*
      (((x : ℂ)+t*I)+2*ε-1))⁻¹‖))*(B/(1+|t|)^j)*X^x := by gcongr
    _ = _ := by ring

private theorem left_pole_inverse_le {δ ε t : ℝ} (hδ : 0 < δ)
    (hε : ε < δ/4) :
    ‖((((1-δ : ℝ) : ℂ)+t*I)-1)*((((1-δ : ℝ) : ℂ)+t*I)+2*ε-1)‖⁻¹ ≤ 2/δ^2 := by
  let s : ℂ := (1-δ : ℝ)+t*I
  have hp : δ ≤ ‖s-1‖ := by
    have h := Complex.abs_re_le_norm (s-1)
    simpa [s,abs_of_pos hδ] using h
  have hq : δ/2 ≤ ‖s+2*ε-1‖ := by
    have h := Complex.abs_re_le_norm (s+2*ε-1)
    have hr : (s+2*ε-1).re = -δ+2*ε := by dsimp [s]; simp; ring
    rw [hr,abs_of_neg (by linarith)] at h
    linarith
  have hprod : δ^2/2 ≤ ‖(s-1)*(s+2*ε-1)‖ := by
    rw [norm_mul]
    calc δ^2/2 = δ*(δ/2) := by ring
      _ ≤ _ := mul_le_mul hp hq (by positivity) (norm_nonneg _)
  calc _ ≤ (δ^2/2)⁻¹ := inv_anti₀ (by positivity) hprod
    _ = _ := by ring

private theorem horizontal_pole_inverse_le {x ε t T : ℝ} (hT : 1 ≤ T) (ht : |t| = T) :
    ‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖ ≤ 1 := by
  have hp : T ≤ ‖((x : ℂ)+t*I)-1‖ := by
    simpa [ht] using Complex.abs_im_le_norm (((x : ℂ)+t*I)-1)
  have hq : T ≤ ‖((x : ℂ)+t*I)+2*ε-1‖ := by
    simpa [ht] using Complex.abs_im_le_norm (((x : ℂ)+t*I)+2*ε-1)
  rw [norm_inv,norm_mul]
  exact inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (hT.trans hp) (hT.trans hq))

/-- Integrated left and both horizontal edges of the actual moving rectangle.
All constants are constructed from the actual source and actual window. -/
theorem exists_dampedSquareContour_edge_bounds :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ j : ℕ, ∃ A > 0,
    ∀ {T δ ε b X : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 ≤ X →
      (‖∫ t in (-T)..T,dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I)‖ ≤
        C*X^(1-δ)*(1+T)^55*(1+2/δ^2)) ∧
      (∀ t : ℝ, |t| = T →
        ‖∫ x in (1-δ)..(1+b),dampedSquareContourIntegrand ε X ((x : ℂ)+t*I)‖ ≤
          A*X^(1+b)*(1+T)^54/(1+T)^j) := by
  obtain ⟨d,hd,hrect⟩ := square_rectangle_bound
  obtain ⟨C,hC,hzero⟩ := hrect 0
  refine ⟨d,hd,2*C,by positivity,?_⟩
  intro j
  obtain ⟨A,hA,horder⟩ := hrect j
  refine ⟨4*A,by positivity,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX
  have hδ1 : δ ≤ 1 := by
    have h := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith : 1 ≤ 1+T)))
    linarith [hd.2]
  constructor
  · have hpoint : ∀ t ∈ Ι (-T) T,
        ‖dampedSquareContourIntegrand ε X ((1-δ : ℝ)+t*I)‖ ≤
          C*X^(1-δ)*(1+T)^54*(1+2/δ^2) := by
      intro t ht
      have ht' : |t| ≤ T := by
        rw [uIoc_of_le (by linarith : -T ≤ T)] at ht
        exact abs_le.mpr ⟨ht.1.le,ht.2⟩
      have h := hzero hT hδ hδd hε hεδ hb hbδ hX
        (show 1-δ ∈ Icc (1-δ) (1+b) from ⟨le_rfl,by linarith⟩) ht'
      simp only [pow_zero,div_one,norm_inv] at h
      calc _ ≤ C*X^(1-δ)*(1+|t|)^54*
          (1+‖((((1-δ : ℝ) : ℂ)+t*I)-1)*((((1-δ : ℝ) : ℂ)+t*I)+2*ε-1)‖⁻¹) := h
        _ ≤ _ := by
          gcongr
          exact left_pole_inverse_le hδ hεδ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [show |T-(-T)| = 2*T by rw [abs_of_pos (by linarith)]; ring] at h
    calc _ ≤ (C*X^(1-δ)*(1+T)^54*(1+2/δ^2))*(2*T) := h
      _ ≤ (C*X^(1-δ)*(1+T)^54*(1+2/δ^2))*(2*(1+T)) := by gcongr; linarith
      _ = _ := by rw [pow_succ]; ring
  · intro t ht
    have hpoint : ∀ x ∈ Ι (1-δ) (1+b),
        ‖dampedSquareContourIntegrand ε X ((x : ℂ)+t*I)‖ ≤
          2*A*X^(1+b)*(1+T)^54/(1+T)^j := by
      intro x hx
      rw [uIoc_of_le (by linarith : 1-δ ≤ 1+b)] at hx
      have h := horder hT hδ hδd hε hεδ hb hbδ hX ⟨hx.1.le,hx.2⟩ ht.le
      rw [ht] at h
      have hxp : X^x ≤ X^(1+b) := Real.rpow_le_rpow_of_exponent_le hX hx.2
      have hpole := horizontal_pole_inverse_le (x := x) (ε := ε) hT ht
      calc _ ≤ A*X^x*(1+T)^54*
          (1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖)/(1+T)^j := h
        _ ≤ A*X^(1+b)*(1+T)^54*(1+1)/(1+T)^j := by gcongr
        _ = _ := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [abs_of_nonneg (by linarith : 0 ≤ (1+b)-(1-δ))] at h
    calc _ ≤ (2*A*X^(1+b)*(1+T)^54/(1+T)^j)*((1+b)-(1-δ)) := h
      _ ≤ (2*A*X^(1+b)*(1+T)^54/(1+T)^j)*2 := by gcongr; linarith
      _ = _ := by ring

end RHTower.BAGTrace
