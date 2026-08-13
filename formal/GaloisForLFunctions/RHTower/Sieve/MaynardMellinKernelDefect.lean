import GaloisForLFunctions.RHTower.Sieve.MaynardMellinWaveletCalibration

/-!
# Quantitative target--reference Mellin defect

The normalized adjacent smooth window is close to the point-mass Mellin character at its left
endpoint throughout the natural low-frequency band `2 H * ‖s-1‖ <= N`.  The error is linear in
relative width `H/N`, uniformly in the window shape.  Applying this estimate at target and
reference widths supplies the honest approximate common mode for Route-T calibration.
-/

noncomputable section
namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

private theorem norm_real_cpow_sub_le_of_log_small
    {N x : ℝ} (hN : 0 < N) (hx : 0 < x) {s : ℂ}
    (hsmall : ‖(s - 1) * ((Real.log x - Real.log N : ℝ) : ℂ)‖ ≤ 1) :
    ‖(x : ℂ) ^ (s - 1) - (N : ℂ) ^ (s - 1)‖ ≤
      2 * N ^ (s.re - 1) * ‖s - 1‖ * |Real.log x - Real.log N| := by
  let z : ℂ := s - 1
  let q : ℂ := ((Real.log x - Real.log N : ℝ) : ℂ) * z
  have hfactor :
      (x : ℂ) ^ z - (N : ℂ) ^ z =
        (N : ℂ) ^ z * (Complex.exp q - 1) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hN.ne')]
    rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hN.le]
    rw [show ((Real.log x : ℝ) : ℂ) * z =
      ((Real.log N : ℝ) : ℂ) * z + q by dsimp only [q]; push_cast; ring,
      Complex.exp_add]
    ring
  have hqsmall : ‖q‖ ≤ 1 := by
    dsimp only [q, z]
    simpa only [mul_comm] using hsmall
  have hq := Complex.norm_exp_sub_one_le hqsmall
  rw [hfactor, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  dsimp only [z]
  simp only [sub_re, one_re]
  have hqnorm : ‖q‖ = |Real.log x - Real.log N| * ‖s - 1‖ := by
    dsimp only [q, z]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hqnorm] at hq
  nlinarith [Real.rpow_nonneg hN.le (s.re - 1), norm_nonneg (s - 1),
    abs_nonneg (Real.log x - Real.log N)]

/-- A narrow adjacent window is a quantitative Mellin approximation to a point mass at its
left endpoint. -/
theorem norm_routeTNormalizedSmoothWindowMellin_sub_pointMass_le
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : 0 < s.re)
    (hsmall : ‖s - 1‖ * (2 * H / N) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin N H s - (N : ℂ) ^ (s - 1)‖ ≤
      4 * N ^ (s.re - 1) * ‖s - 1‖ * (H / N) := by
  let W : ℝ → ℝ := routeTSmoothWindowWeight N H
  let z : ℂ := s - 1
  let C : ℝ := 4 * N ^ (s.re - 1) * ‖s - 1‖ * (H / N)
  have hN0 : 0 ≤ N := hN.le
  have hNH0 : 0 ≤ N + H := by linarith
  have hWnonneg : ∀ x : ℝ, 0 ≤ W x := fun x => routeTSmoothWindowWeight_nonneg hH
  have hWint : IntegrableOn (fun x : ℝ => (W x : ℂ)) (Ioi 0) := by
    have hplus : IntegrableOn
        (fun x : ℝ => (smoothWeight (N + H) H x : ℂ)) (Ioi 0) :=
      (integrableOn_smoothWeight_Ioi hNH0 hH).ofReal
    have hbase : IntegrableOn
        (fun x : ℝ => (smoothWeight N H x : ℂ)) (Ioi 0) :=
      (integrableOn_smoothWeight_Ioi hN0 hH).ofReal
    exact (hplus.sub hbase).congr_fun (fun x _hx => by
      simp only [Pi.sub_apply, W, routeTSmoothWindowWeight, ofReal_sub]) measurableSet_Ioi
  have hMellinInt : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ z * (W x : ℂ)) (Ioi 0) := by
    dsimp only [W, z, routeTSmoothWindowWeight]
    exact ((integrableOn_mellin_smoothWeight hNH0 hH hs).sub
      (integrableOn_mellin_smoothWeight hN0 hH hs)).congr_fun (fun x _hx => by
        simp only [Pi.sub_apply, ofReal_sub, mul_sub])
          measurableSet_Ioi
  have hconstInt : IntegrableOn
      (fun x : ℝ => ((N : ℂ) ^ z) * (W x : ℂ)) (Ioi 0) :=
    hWint.const_mul ((N : ℂ) ^ z)
  have hmassC : (∫ x in Ioi (0 : ℝ), (W x : ℂ)) = (H : ℂ) := by
    calc
      (∫ x in Ioi (0 : ℝ), (W x : ℂ)) =
          ((∫ x in Ioi (0 : ℝ), W x : ℝ) : ℂ) := integral_ofReal (𝕜 := ℂ)
      _ = (H : ℂ) := by
        dsimp only [W]
        rw [integral_routeTSmoothWindowWeight_eq_width hN0 hH]
  have hrewrite :
      routeTNormalizedSmoothWindowMellin N H s - (N : ℂ) ^ z =
        (H : ℂ)⁻¹ * (∫ x in Ioi (0 : ℝ),
          (W x : ℂ) * ((x : ℂ) ^ z - (N : ℂ) ^ z)) := by
    rw [routeTNormalizedSmoothWindowMellin]
    have hmellin :
        mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
          ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ z * (W x : ℂ) := by
      rw [mellin]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      dsimp only [W, z]
      rw [smul_eq_mul]
    rw [hmellin]
    have hdiff :
        (∫ x in Ioi (0 : ℝ),
            (W x : ℂ) * ((x : ℂ) ^ z - (N : ℂ) ^ z)) =
          (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ z * (W x : ℂ)) -
            (N : ℂ) ^ z * (∫ x in Ioi (0 : ℝ), (W x : ℂ)) := by
      rw [← integral_const_mul]
      rw [← integral_sub hMellinInt hconstInt]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      ring
    rw [hdiff, hmassC]
    have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    field_simp [hHne]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ‖(W x : ℂ) * ((x : ℂ) ^ z - (N : ℂ) ^ z)‖ ≤ C * W x := by
    intro x hx
    by_cases hxN : x ≤ N
    · have hfirst : smoothWeight (N + H) H x = 1 :=
        smoothWeight_eq_one hH (by linarith)
      have hsecond : smoothWeight N H x = 1 := smoothWeight_eq_one hH hxN
      have hWzero : W x = 0 := by
        dsimp only [W, routeTSmoothWindowWeight]
        rw [hfirst, hsecond, sub_self]
      rw [hWzero]
      simp
    · by_cases hxB : x ≤ N + 2 * H
      · have hxpos : 0 < x := hx
        have hNx : N ≤ x := le_of_not_ge hxN
        have hlog0 : 0 ≤ Real.log x - Real.log N := by
          exact sub_nonneg.mpr (Real.log_le_log hN hNx)
        have hlogUpper : Real.log x - Real.log N ≤ 2 * H / N := by
          have hlogdiv := Real.log_le_sub_one_of_pos (div_pos hxpos hN)
          rw [Real.log_div hxpos.ne' hN.ne'] at hlogdiv
          have hdiv : x / N - 1 ≤ 2 * H / N := by
            field_simp [hN.ne']
            linarith
          exact hlogdiv.trans hdiv
        have hlocalSmall :
            ‖(s - 1) * ((Real.log x - Real.log N : ℝ) : ℂ)‖ ≤ 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
          exact (mul_le_mul_of_nonneg_left hlogUpper (norm_nonneg (s - 1))).trans hsmall
        have hcpow := norm_real_cpow_sub_le_of_log_small hN hxpos hlocalSmall
        have hcpowC :
            ‖(x : ℂ) ^ (s - 1) - (N : ℂ) ^ (s - 1)‖ ≤ C := by
          have hpow0 : 0 ≤ N ^ (s.re - 1) := Real.rpow_nonneg hN.le _
          have hnorm0 : 0 ≤ ‖s - 1‖ := norm_nonneg _
          dsimp only [C]
          calc
            ‖(x : ℂ) ^ (s - 1) - (N : ℂ) ^ (s - 1)‖ ≤
                2 * N ^ (s.re - 1) * ‖s - 1‖ *
                  |Real.log x - Real.log N| := hcpow
            _ ≤ 2 * N ^ (s.re - 1) * ‖s - 1‖ * (2 * H / N) := by
              rw [abs_of_nonneg hlog0]
              gcongr
            _ = 4 * N ^ (s.re - 1) * ‖s - 1‖ * (H / N) := by ring
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hWnonneg x)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcpowC (hWnonneg x)
      · have hxge : N + 2 * H ≤ x := le_of_not_ge hxB
        have hfirst : smoothWeight (N + H) H x = 0 :=
          smoothWeight_eq_zero hH (by linarith)
        have hsecond : smoothWeight N H x = 0 :=
          smoothWeight_eq_zero hH (by linarith)
        have hWzero : W x = 0 := by
          dsimp only [W, routeTSmoothWindowWeight]
          rw [hfirst, hsecond, sub_self]
        rw [hWzero]
        simp
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hmajorInt : IntegrableOn (fun x : ℝ => C * W x) (Ioi 0) := by
    have hWreal : IntegrableOn W (Ioi 0) := by
      exact ((integrableOn_smoothWeight_Ioi hNH0 hH).sub
        (integrableOn_smoothWeight_Ioi hN0 hH)).congr_fun (fun x _hx => by
          simp only [Pi.sub_apply, W, routeTSmoothWindowWeight]) measurableSet_Ioi
    exact hWreal.const_mul C
  rw [hrewrite, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hH]
  have hintBound :
      ‖∫ x in Ioi (0 : ℝ),
          (W x : ℂ) * ((x : ℂ) ^ z - (N : ℂ) ^ z)‖ ≤
        ∫ x in Ioi (0 : ℝ), C * W x := by
    apply norm_integral_le_of_norm_le hmajorInt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  calc
    H⁻¹ * ‖∫ x in Ioi (0 : ℝ),
        (W x : ℂ) * ((x : ℂ) ^ z - (N : ℂ) ^ z)‖ ≤
        H⁻¹ * (∫ x in Ioi (0 : ℝ), C * W x) :=
      mul_le_mul_of_nonneg_left hintBound (inv_nonneg.mpr hH.le)
    _ = C := by
      rw [integral_const_mul]
      dsimp only [W]
      rw [integral_routeTSmoothWindowWeight_eq_width hN0 hH]
      field_simp [hH.ne']
    _ = 4 * N ^ (s.re - 1) * ‖s - 1‖ * (H / N) := rfl

/-- Two normalized widths share the same approximate point-mass mode on their common low band. -/
theorem norm_routeTNormalizedSmoothWindowMellin_sub_le
    {N H R : ℝ} (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    {s : ℂ} (hs : 0 < s.re)
    (hsmallH : ‖s - 1‖ * (2 * H / N) ≤ 1)
    (hsmallR : ‖s - 1‖ * (2 * R / N) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin N R s -
        routeTNormalizedSmoothWindowMellin N H s‖ ≤
      4 * N ^ (s.re - 1) * ‖s - 1‖ * ((R + H) / N) := by
  let P : ℂ := (N : ℂ) ^ (s - 1)
  have hRbound := norm_routeTNormalizedSmoothWindowMellin_sub_pointMass_le
    hN hR hs hsmallR
  have hHbound := norm_routeTNormalizedSmoothWindowMellin_sub_pointMass_le
    hN hH hs hsmallH
  calc
    ‖routeTNormalizedSmoothWindowMellin N R s -
        routeTNormalizedSmoothWindowMellin N H s‖ =
        ‖(routeTNormalizedSmoothWindowMellin N R s - P) -
          (routeTNormalizedSmoothWindowMellin N H s - P)‖ := by
            congr 1
            ring
    _ ≤ ‖routeTNormalizedSmoothWindowMellin N R s - P‖ +
        ‖routeTNormalizedSmoothWindowMellin N H s - P‖ := norm_sub_le _ _
    _ ≤ 4 * N ^ (s.re - 1) * ‖s - 1‖ * (R / N) +
        4 * N ^ (s.re - 1) * ‖s - 1‖ * (H / N) :=
      add_le_add hRbound hHbound
    _ = 4 * N ^ (s.re - 1) * ‖s - 1‖ * ((R + H) / N) := by ring

/-- If target width is no larger than reference width, reference scale alone determines the
common low band and the defect costs at most twice its relative width. -/
theorem norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
    {N H R : ℝ} (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    {s : ℂ} (hs : 0 < s.re)
    (hsmallR : ‖s - 1‖ * (2 * R / N) ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin N R s -
        routeTNormalizedSmoothWindowMellin N H s‖ ≤
      8 * N ^ (s.re - 1) * ‖s - 1‖ * (R / N) := by
  have hwidth : 2 * H / N ≤ 2 * R / N := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHR (by norm_num)) hN.le
  have hsmallH : ‖s - 1‖ * (2 * H / N) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hwidth (norm_nonneg (s - 1))).trans hsmallR
  have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le
    hN hH hR hs hsmallH hsmallR
  have hsum : (R + H) / N ≤ 2 * R / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    linarith
  calc
    ‖routeTNormalizedSmoothWindowMellin N R s -
        routeTNormalizedSmoothWindowMellin N H s‖ ≤
        4 * N ^ (s.re - 1) * ‖s - 1‖ * ((R + H) / N) := hkernel
    _ ≤ 4 * N ^ (s.re - 1) * ‖s - 1‖ * (2 * R / N) := by
      gcongr
    _ = 8 * N ^ (s.re - 1) * ‖s - 1‖ * (R / N) := by ring

end RHTower.Sieve
