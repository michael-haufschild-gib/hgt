import GaloisForLFunctions.RHTower.Sieve.MaynardMellinWaveletCalibration

/-!
# Positive normalized Mellin kernels

An adjacent Route-T smooth window is nonnegative, supported to the right of its positive left
endpoint, and has mass exactly equal to its width.  After width normalization its Mellin transform
is therefore a probability average of Mellin characters.  On the entire half-plane `re s ≤ 1`,
the norm of that average is bounded by the character at the left endpoint.  This global estimate
has no frequency restriction and no loss.
-/

noncomputable section
namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- A positive normalized adjacent smooth window is a Mellin probability kernel on the
half-plane `re s ≤ 1`: its norm never exceeds the left-endpoint character. -/
theorem norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {s : ℂ} (hs : s.re ≤ 1) :
    ‖routeTNormalizedSmoothWindowMellin N H s‖ ≤ N ^ (s.re - 1) := by
  let W : ℝ → ℝ := routeTSmoothWindowWeight N H
  let z : ℂ := s - 1
  let C : ℝ := N ^ (s.re - 1)
  have hN0 : 0 ≤ N := hN.le
  have hNH0 : 0 ≤ N + H := by linarith
  have hWnonneg : ∀ x : ℝ, 0 ≤ W x := fun x => routeTSmoothWindowWeight_nonneg hH
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ‖(x : ℂ) ^ z * (W x : ℂ)‖ ≤ C * W x := by
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
        have hpow : x ^ (s.re - 1) ≤ C := by
          dsimp only [C]
          exact Real.rpow_le_rpow_of_nonpos hN hNx (by linarith)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWnonneg x)]
        simp only [z, sub_re, one_re]
        exact mul_le_mul_of_nonneg_right hpow (hWnonneg x)
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
  have hWreal : IntegrableOn W (Ioi 0) := by
    exact ((integrableOn_smoothWeight_Ioi hNH0 hH).sub
      (integrableOn_smoothWeight_Ioi hN0 hH)).congr_fun (fun x _hx => by
        simp only [Pi.sub_apply, W, routeTSmoothWindowWeight]) measurableSet_Ioi
  have hmajorInt : IntegrableOn (fun x : ℝ => C * W x) (Ioi 0) :=
    hWreal.const_mul C
  have hmellin :
      mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ z * (W x : ℂ) := by
    rw [mellin]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    dsimp only [W, z]
    rw [smul_eq_mul]
  rw [routeTNormalizedSmoothWindowMellin, hmellin, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hintBound :
      ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ z * (W x : ℂ)‖ ≤
        ∫ x in Ioi (0 : ℝ), C * W x := by
    apply norm_integral_le_of_norm_le hmajorInt
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  calc
    H⁻¹ * ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ z * (W x : ℂ)‖ ≤
        H⁻¹ * (∫ x in Ioi (0 : ℝ), C * W x) :=
      mul_le_mul_of_nonneg_left hintBound (inv_nonneg.mpr hH.le)
    _ = C := by
      rw [integral_const_mul]
      dsimp only [W]
      rw [integral_routeTSmoothWindowWeight_eq_width hN0 hH]
      field_simp [hH.ne']
    _ = N ^ (s.re - 1) := rfl

end RHTower.Sieve
