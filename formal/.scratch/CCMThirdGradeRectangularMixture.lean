import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedQuantileTransport

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Positive aperture density obtained by differentiating the third-grade anchored kernel. -/
def ccmThirdGradeCesaroRectangularMixDensity (H t : ℝ) : ℝ :=
  192 * (2 * H - t) / (H * t ^ 5)

theorem ccmThirdGradeCesaroRectangularMixDensity_nonneg
    {H t : ℝ} (hH : 0 < H) (ht : 0 < t) (htH : t ≤ H) :
    0 ≤ ccmThirdGradeCesaroRectangularMixDensity H t := by
  have hnum : 0 ≤ 2 * H - t := by linarith
  unfold ccmThirdGradeCesaroRectangularMixDensity
  positivity

/-- The positive rectangular-mixture density is the negative aperture derivative of the
third-grade anchored kernel. -/
theorem hasDerivAt_ccmGuinandWeilThirdGradeCesaroErrorKernel
    {H t : ℝ} (hH : H ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (ccmGuinandWeilThirdGradeCesaroErrorKernel H)
      (-ccmThirdGradeCesaroRectangularMixDensity H t) t := by
  have hlin : HasDerivAt (fun x : ℝ => 64 * x / H) (64 / H) t := by
    convert ((hasDerivAt_id t).const_mul 64).div_const H using 1 <;> ring
  have hnum : HasDerivAt (fun x : ℝ => 96 - 64 * x / H) (-64 / H) t := by
    convert (hasDerivAt_const (x := t) (c := (96 : ℝ))).sub hlin using 1 <;> ring
  have hden : HasDerivAt (fun x : ℝ => x ^ 4) (4 * t ^ 3) t := by
    convert hasDerivAt_pow 4 t using 1 <;> ring
  apply (hnum.div hden (pow_ne_zero 4 ht)).congr_deriv
  unfold ccmThirdGradeCesaroRectangularMixDensity
  field_simp [hH, ht]
  ring

theorem ccmGuinandWeilThirdGradeCesaroErrorKernel_endpoint
    {H : ℝ} (hH : H ≠ 0) :
    ccmGuinandWeilThirdGradeCesaroErrorKernel H H = 32 / H ^ 4 := by
  unfold ccmGuinandWeilThirdGradeCesaroErrorKernel
  field_simp [hH]
  ring

/-- Tail mass of the rectangular mixture is exactly the anchored error kernel. The endpoint atom
is forced by the nonzero left derivative at the moving wall. -/
theorem integral_rectangularMixDensity_add_endpoint_eq_errorKernel
    {H h : ℝ} (hh : 0 < h) (hhH : h ≤ H) :
    (∫ t in h..H, ccmThirdGradeCesaroRectangularMixDensity H t) + 32 / H ^ 4 =
      ccmGuinandWeilThirdGradeCesaroErrorKernel H h := by
  have hH : 0 < H := hh.trans_le hhH
  have hderiv : ∀ t ∈ Set.uIcc h H,
      HasDerivAt (fun x : ℝ => -ccmGuinandWeilThirdGradeCesaroErrorKernel H x)
        (ccmThirdGradeCesaroRectangularMixDensity H t) t := by
    intro t ht
    rw [Set.uIcc_of_le hhH] at ht
    have ht0 : t ≠ 0 := ne_of_gt (hh.trans_le ht.1)
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroErrorKernel hH.ne' ht0).neg.congr_deriv
      (by ring)
  have hint : IntervalIntegrable (ccmThirdGradeCesaroRectangularMixDensity H) volume h H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hderiv t ht).continuousAt.neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [ccmGuinandWeilThirdGradeCesaroErrorKernel_endpoint hH.ne']
  ring

/-- Exact positive rectangular-autocorrelation mixture of the literal third-grade triangular
reporter on its physical window. The endpoint atom cancels the terminal slope exactly. -/
theorem ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_rectangularMixture
    {H h : ℝ} (hh : 0 < h) (hhH : h ≤ H) :
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H h =
      (∫ t in h..H,
        ccmThirdGradeCesaroRectangularMixDensity H t * (t - h)) +
        (32 / H ^ 4) * (H - h) := by
  have hH : 0 < H := hh.trans_le hhH
  let A : ℝ → ℝ := fun t =>
    ccmGuinandWeilThirdGradeCesaroErrorKernel H t * (h - t) -
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H t
  have hderiv : ∀ t ∈ Set.uIcc h H,
      HasDerivAt A
        (ccmThirdGradeCesaroRectangularMixDensity H t * (t - h)) t := by
    intro t ht
    rw [Set.uIcc_of_le hhH] at ht
    have ht0 : t ≠ 0 := ne_of_gt (hh.trans_le ht.1)
    have hk := hasDerivAt_ccmGuinandWeilThirdGradeCesaroErrorKernel hH.ne' ht0
    have hlin : HasDerivAt (fun x : ℝ => h - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub h
    have hw := hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (H := H) ht0
    apply ((hk.mul hlin).sub hw).congr_deriv
    dsimp only [A]
    ring
  have hint : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * (t - h)) volume h H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hderiv t ht).continuousAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hweightH : ccmGuinandWeilThirdGradeCesaroTriangularWeight H H = 0 := by
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    field_simp [hH.ne']
  have hkernelH := ccmGuinandWeilThirdGradeCesaroErrorKernel_endpoint hH.ne'
  dsimp only [A] at hftc
  rw [hweightH, hkernelH] at hftc
  linarith

/-- Fixed-lower-wall total mixture mass is uniformly bounded independently of the moving wall. -/
theorem rectangularMixDensity_totalMass_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t) + 32 / H ^ 4 ≤
      96 / b ^ 4 := by
  rw [integral_rectangularMixDensity_add_endpoint_eq_errorKernel hb hbH]
  exact (ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds hb hbH
    (show b ∈ Set.Icc b H by exact ⟨le_rfl, hbH⟩)).2

end GaloisForLFunctions.RHTower
