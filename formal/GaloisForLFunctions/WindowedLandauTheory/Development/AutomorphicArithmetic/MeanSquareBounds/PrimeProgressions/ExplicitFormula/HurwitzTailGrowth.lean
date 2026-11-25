import GaloisForLFunctions.HTGeometry.HurwitzZetaEulerMaclaurinBridge

/-! Uniform bounds for the pole-removed Hurwitz zeta function from its second-order Euler–Maclaurin tail. -/

open Complex Filter MeasureTheory Metric Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace QH.PrimeProgressions

private theorem norm_emIntegrand_le {a x p : ℝ} (ha : 1 ≤ a) (hx : 0 < x)
    {s : ℂ} (hp : p ≤ s.re + 2) :
    ‖((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)‖ ≤
      (1 / 8) * (x + a) ^ (-p) := by
  have hb : 1 ≤ x + a := by linarith only [ha, hx]
  rw [norm_mul, norm_real, Real.norm_eq_abs, norm_shiftCpow (zero_lt_one.trans_le hb)]
  exact mul_le_mul (abs_bernoulliHalfPer_le x)
    (Real.rpow_le_rpow_of_exponent_le hb (by linarith only [hp])) (by positivity) (by norm_num)

private theorem emKernel_differentiableAt {a : ℝ} (ha : 1 ≤ a) {s : ℂ}
    (hs : -1 < s.re) : DifferentiableAt ℂ (emKernel a) s := by
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  let ε := (s.re + 1) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith only [hs]
  let p := 1 + ε
  have hp : 1 < p := by dsimp [p]; linarith only [hε]
  let F (z : ℂ) (x : ℝ) :=
    ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-z - 2)
  let D (z : ℂ) (x : ℝ) := F z x * (-((Real.log (x + a) : ℝ) : ℂ))
  let μ := volume.restrict (Ioi (0 : ℝ))
  let B (x : ℝ) := ((1 / 8) / ε) * (x + a) ^ (-p)
  have hF (z : ℂ) : AEStronglyMeasurable (F z) μ := aestronglyMeasurable_emKernel_integrand ha₀ z
  have hmeas : AEStronglyMeasurable (D s) μ := (hF s).mul
    (Complex.measurable_ofReal.comp (Real.measurable_log.comp (measurable_id.add_const a))).neg.aestronglyMeasurable
  have hInt : Integrable (F s) μ := by
    refine ((integrableOn_Ioi_shift_rpow_neg ha₀ hp).const_mul (1 / 8)).mono' (hF s) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x (hx : 0 < x)
    exact norm_emIntegrand_le ha hx (by dsimp [p, ε]; linarith only [hs])
  have hB : Integrable B μ := (integrableOn_Ioi_shift_rpow_neg ha₀ hp).const_mul _
  have hbd : ∀ᵐ x ∂μ, ∀ z ∈ ball s ε, ‖D z x‖ ≤ B x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x (hx : 0 < x) z hz
    have hb : 1 ≤ x + a := by linarith only [ha, hx]
    have hb₀ : 0 < x + a := zero_lt_one.trans_le hb
    have hnear := (abs_re_le_norm (z - s)).trans_lt (by
      rwa [← Complex.dist_eq, ← mem_ball])
    have hre : p + ε ≤ z.re + 2 := by
      have h := (abs_lt.mp hnear).1
      rw [sub_re] at h
      dsimp [p, ε] at *
      linarith only [h]
    have hl := Real.log_le_rpow_div hb₀.le hε
    rw [show ‖D z x‖ = ‖F z x‖ * Real.log (x + a) by
      simp [D, Real.norm_of_nonneg (Real.log_nonneg hb)]]
    refine (mul_le_mul (norm_emIntegrand_le ha hx hre) hl (Real.log_nonneg hb) (by positivity)).trans_eq ?_
    calc
      _ = ((1 / 8) * ((x + a) ^ (-(p + ε)) * (x + a) ^ ε)) / ε := by ring
      _ = _ := by
        rw [← Real.rpow_add hb₀, show -(p + ε) + ε = -p by ring]
        dsimp only [B]
        ring
  have hd : ∀ᵐ x ∂μ, ∀ z ∈ ball s ε, HasDerivAt (fun w => F w x) (D z x) z := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x (hx : 0 < x) z _
    have hb : 0 < x + a := by linarith only [ha, hx]
    have h₀ : ((x + a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
    have h₁ : HasDerivAt (fun w : ℂ => -w - 2) (-1) z :=
      ((hasDerivAt_id z).neg).sub_const 2
    refine ((h₁.const_cpow (c := ((x + a : ℝ) : ℂ)) (Or.inl h₀)).const_mul
      ((bernoulliHalfPer x : ℝ) : ℂ)).congr_deriv ?_
    simp only [F, D, ← Complex.ofReal_log hb.le]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hε)
    (.of_forall hF) hInt hmeas hbd hB hd).2.differentiableAt

private theorem hurwitzZetaEM_differentiableAt {a : ℝ} (ha : 1 ≤ a) {s : ℂ}
    (hs : -1 < s.re) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (hurwitzZetaEM a) s := by
  have ha₀ : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans_le ha).ne'
  unfold hurwitzZetaEM
  exact (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl ha₀) |>.div
    (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs₁) |>.add
    ((differentiableAt_id.neg.const_cpow (Or.inl ha₀)).div_const 2)).sub
    ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul (emKernel_differentiableAt ha hs))

private theorem hurwitzZeta_tail {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) {s : ℂ}
    (hs : -1 < s.re) (hs₁ : s ≠ 1) :
    HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s =
      (a : ℂ) ^ (-s) + hurwitzZetaEM (a + 1) s := by
  refine eq_of_eq_on_one_lt_re (c := -1) (f := HurwitzZeta.hurwitzZeta (a : UnitAddCircle))
    (g := fun z => (a : ℂ) ^ (-z) + hurwitzZetaEM (a + 1) z) (by norm_num)
    (fun z _ hz => HurwitzZeta.differentiableAt_hurwitzZeta _ hz)
    (fun z hz hz₁ => (differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))).add
      (hurwitzZetaEM_differentiableAt (by linarith only [ha]) hz hz₁)) ?_ hs hs₁
  intro z hz
  exact hurwitzZeta_eq_rpow_add_hurwitzZetaEM ha ha₁ (by linarith only [hz])
    (fun e => by norm_num [e] at hz)

private theorem norm_emKernel_wide {a : ℝ} (ha : 1 ≤ a) {s : ℂ}
    (hs : -(49 / 50 : ℝ) ≤ s.re) : ‖emKernel a s‖ ≤ 50 / 8 := by
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  unfold emKernel
  calc
    _ ≤ ∫ x in Ioi (0 : ℝ), (1 / 8) * (x + a) ^ (-(51 / 50 : ℝ)) := by
      refine norm_integral_le_of_norm_le
        ((integrableOn_Ioi_shift_rpow_neg ha₀ (by norm_num : (1 : ℝ) < 51 / 50)).const_mul _) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x (hx : 0 < x)
      exact norm_emIntegrand_le ha hx (by linarith only [hs])
    _ ≤ _ := by
      rw [integral_const_mul, integral_Ioi_shift_rpow_neg ha₀ (by norm_num)]
      norm_num
      have hk := Real.rpow_le_one_of_one_le_of_nonpos ha (by norm_num : (1 - 51 / 50 : ℝ) ≤ 0)
      linarith only [hk]

/-- The pole-removed Hurwitz zeta function grows polynomially, uniformly after accounting for its first summand. -/
theorem norm_hurwitzZeta_pole_removed {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) {s : ℂ}
    (hs : -(49 / 50 : ℝ) ≤ s.re) (hs₀ : s.re ≤ 1 / 2) :
    ‖(s - 1) * HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s‖ ≤ 13 * a⁻¹ * (‖s‖ + 1) ^ 3 := by
  have hs₁ : s ≠ 1 := fun e => by norm_num [e] at hs₀
  have hb : 1 ≤ a + 1 := by linarith only [ha]
  have hb₀ : 0 < a + 1 := zero_lt_one.trans_le hb
  have hb₂ : a + 1 ≤ 2 := by linarith only [ha₁]
  have haI : 1 ≤ a⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le ha ha₁
  let R := ‖s‖ + 1
  have hR : 1 ≤ R := le_add_of_nonneg_left (norm_nonneg s)
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hm : ‖s - 1‖ ≤ R := by simpa [R] using norm_sub_le s (1 : ℂ)
  have hp : ‖s + 1‖ ≤ R := by simpa [R] using norm_add_le s (1 : ℂ)
  have haPow : ‖(a : ℂ) ^ (-s)‖ ≤ a⁻¹ := by
    rw [norm_cpow_eq_rpow_re_of_pos ha, neg_re, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge ha ha₁ (by linarith only [hs₀])
  have hbPow : ‖((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ 2 := by
    rw [norm_cpow_eq_rpow_re_of_pos hb₀, neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hb (by linarith only [hs] : -s.re ≤ 1)).trans
      (by simpa only [Real.rpow_one] using hb₂)
  have hbPow' : ‖((a + 1 : ℝ) : ℂ) ^ (1 - s)‖ ≤ 4 := by
    rw [norm_cpow_eq_rpow_re_of_pos hb₀, sub_re, one_re]
    exact (Real.rpow_le_rpow_of_exponent_le hb (by linarith only [hs] : 1 - s.re ≤ 2)).trans
      (by rw [Real.rpow_two]; exact (pow_le_pow_left₀ hb₀.le hb₂ 2).trans_eq (by norm_num))
  rw [hurwitzZeta_tail ha ha₁ (by linarith only [hs]) hs₁, hurwitzZetaEM, mul_add, mul_sub, mul_add,
    mul_div_cancel₀ _ (sub_ne_zero.mpr hs₁)]
  refine (norm_add_le _ _).trans ((add_le_add le_rfl (norm_sub_le _ _)).trans ?_)
  refine (add_le_add le_rfl (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
  simp only [norm_mul, norm_div, Complex.norm_ofNat]
  have h₁ : ‖s - 1‖ * ‖(a : ℂ) ^ (-s)‖ ≤ R * a⁻¹ :=
    mul_le_mul hm haPow (norm_nonneg _) hR₀
  have h₂ : ‖s - 1‖ * (‖((a + 1 : ℝ) : ℂ) ^ (-s)‖ / 2) ≤ R :=
    (mul_le_mul hm (by linarith only [hbPow] : ‖((a + 1 : ℝ) : ℂ) ^ (-s)‖ / 2 ≤ 1)
      (by positivity) hR₀).trans_eq (mul_one _)
  have h₃ : ‖s - 1‖ * (‖s‖ * ‖s + 1‖ * ‖emKernel (a + 1) s‖) ≤ (50 / 8) * R ^ 3 := by
    have hR' : ‖s‖ ≤ R := by dsimp [R]; linarith
    exact (mul_le_mul hm (mul_le_mul (mul_le_mul hR' hp (norm_nonneg _) hR₀)
      (norm_emKernel_wide hb hs) (norm_nonneg _) (by positivity)) (by positivity) hR₀).trans_eq (by ring)
  have hP : R ≤ R ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hR (show 1 ≤ (3 : ℕ) by decide)
  have hPR : R ^ 3 ≤ a⁻¹ * R ^ 3 := le_mul_of_one_le_left (by positivity) haI
  have hPa : R * a⁻¹ ≤ a⁻¹ * R ^ 3 := (mul_le_mul_of_nonneg_right hP (by positivity)).trans_eq (mul_comm _ _)
  change _ ≤ 13 * a⁻¹ * R ^ 3
  linarith only [h₁, h₂, h₃, hbPow', hP, hPR, hPa, hR]

end QH.PrimeProgressions
