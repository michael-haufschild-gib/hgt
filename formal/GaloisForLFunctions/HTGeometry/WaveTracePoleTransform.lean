import GaloisForLFunctions.HTGeometry.WaveTraceLaplace

/-!
# Holomorphy of the active-pole transform

Away from the resolvent poles the active-pole transform of a wave trace is holomorphic: its
terms are `O(‖gamma‖⁻²)` uniformly on any bounded region whose distance to the pole set is
positive, so the series converges locally uniformly and Weierstrass applies.

This is the analytic continuation the Landau argument consumes: the transform is the Laplace
transform of the wave trace only to the right of the horizontal width, but it is holomorphic
on a much larger region.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_ccos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  rw [norm_div]
  have h1 : ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ ≤
      ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖ := norm_add_le _ _
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h3 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [h2, h3] at h1
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  linarith

namespace WaveSpectrum

variable {G : Type*} [Countable G] (S : WaveSpectrum G)

omit [Countable G] in
theorem norm_traceCoeff_le (P : Polynomial ℝ) (g : G) :
    ‖S.traceCoeff P g‖ ≤ polyBallBound P (S.lower⁻¹ ^ 2) * ‖S.gamma g‖⁻¹ ^ 3 := by
  rw [traceCoeff, norm_div, norm_pow]
  have hg : 0 < ‖S.gamma g‖ := S.norm_gamma_pos g
  have hpoly : ‖Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P‖ ≤ polyBallBound P (S.lower⁻¹ ^ 2) :=
    norm_aeval_le_polyBallBound P (S.norm_inv_gamma_sq_le g)
  rw [div_le_iff₀ (by positivity)]
  calc ‖Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P‖
      ≤ polyBallBound P (S.lower⁻¹ ^ 2) := hpoly
    _ = polyBallBound P (S.lower⁻¹ ^ 2) * ‖S.gamma g‖⁻¹ ^ 3 * ‖S.gamma g‖ ^ 3 := by
        field_simp

omit [Countable G] in
theorem norm_poleNumer_le (T : ℝ) {s : ℂ} {M : ℝ} (hs : ‖s‖ ≤ M) (g : G) :
    ‖S.poleNumer T s g‖ ≤
      Real.exp ((M + S.width) * |T|) * (M + ‖S.gamma g‖) := by
  rw [poleNumer, norm_mul]
  have hexp : ‖Complex.exp (-s * (T : ℂ))‖ ≤ Real.exp (M * |T|) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (-s * (T : ℂ)).re = -(s.re * T) := by simp [Complex.mul_re]
    rw [hre]
    have h1 : |s.re| ≤ M := le_trans (Complex.abs_re_le_norm s) hs
    have h2 : -(s.re * T) ≤ |s.re * T| := neg_le_abs _
    have h3 : |s.re * T| = |s.re| * |T| := abs_mul _ _
    have h4 : |s.re| * |T| ≤ M * |T| := mul_le_mul_of_nonneg_right h1 (abs_nonneg T)
    linarith [h2, h3 ▸ h4]
  have hsin : ‖Complex.sin (S.gamma g * (T : ℂ))‖ ≤ Real.exp (S.width * |T|) := by
    refine le_trans (norm_csin_le_exp_abs_im _) (Real.exp_le_exp.mpr ?_)
    have him : (S.gamma g * (T : ℂ)).im = (S.gamma g).im * T := by simp [Complex.mul_im]
    rw [him, abs_mul]
    exact mul_le_mul_of_nonneg_right (S.im_le g) (abs_nonneg T)
  have hcos : ‖Complex.cos (S.gamma g * (T : ℂ))‖ ≤ Real.exp (S.width * |T|) := by
    refine le_trans (norm_ccos_le_exp_abs_im _) (Real.exp_le_exp.mpr ?_)
    have him : (S.gamma g * (T : ℂ)).im = (S.gamma g).im * T := by simp [Complex.mul_im]
    rw [him, abs_mul]
    exact mul_le_mul_of_nonneg_right (S.im_le g) (abs_nonneg T)
  have hnum : ‖s * Complex.sin (S.gamma g * (T : ℂ)) +
      S.gamma g * Complex.cos (S.gamma g * (T : ℂ))‖ ≤
      Real.exp (S.width * |T|) * (M + ‖S.gamma g‖) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖s‖ * ‖Complex.sin (S.gamma g * (T : ℂ))‖ ≤ M * Real.exp (S.width * |T|) :=
      mul_le_mul hs hsin (norm_nonneg _) (le_trans (norm_nonneg s) hs)
    have h2 : ‖S.gamma g‖ * ‖Complex.cos (S.gamma g * (T : ℂ))‖ ≤
        ‖S.gamma g‖ * Real.exp (S.width * |T|) :=
      mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
    nlinarith [h1, h2]
  have hMnn : 0 ≤ M := le_trans (norm_nonneg s) hs
  calc ‖Complex.exp (-s * (T : ℂ))‖ *
        ‖s * Complex.sin (S.gamma g * (T : ℂ)) + S.gamma g * Complex.cos (S.gamma g * (T : ℂ))‖
      ≤ Real.exp (M * |T|) * (Real.exp (S.width * |T|) * (M + ‖S.gamma g‖)) := by
        refine mul_le_mul hexp hnum (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((M + S.width) * |T|) * (M + ‖S.gamma g‖) := by
        rw [show (M + S.width) * |T| = M * |T| + S.width * |T| by ring, Real.exp_add]
        ring

/-- Active-pole transform of the wave trace. -/
def poleTransform (P : Polynomial ℝ) (T : ℝ) (s : ℂ) : ℂ := ∑' g, S.poleTerm P T s g

/-- Uniform majorant for the resolvent terms on a bounded pole-free region. -/
def poleMajorant (P : Polynomial ℝ) (T M d : ℝ) (g : G) : ℝ :=
  polyBallBound P (S.lower⁻¹ ^ 2) * Real.exp ((M + S.width) * |T|) / d *
    (M * ‖S.gamma g‖⁻¹ ^ 3 + ‖S.gamma g‖⁻¹ ^ 2)

omit [Countable G] in
theorem summable_poleMajorant (P : Polynomial ℝ) (T M d : ℝ) :
    Summable (S.poleMajorant P T M d) := by
  have hrepr : S.poleMajorant P T M d = fun g =>
      polyBallBound P (S.lower⁻¹ ^ 2) * Real.exp ((M + S.width) * |T|) / d *
        (M * ‖S.gamma g‖⁻¹ ^ 3 + ‖S.gamma g‖⁻¹ ^ 2) := rfl
  rw [hrepr]
  exact ((S.summable_inv_cube.mul_left M).add S.summable_inv_sq).mul_left _

omit [Countable G] in
theorem norm_poleTerm_le (P : Polynomial ℝ) (T : ℝ) {s : ℂ} {M d : ℝ} (hd : 0 < d)
    (hs : ‖s‖ ≤ M) (g : G) (hden : d ≤ ‖s ^ 2 + S.gamma g ^ 2‖) :
    ‖S.poleTerm P T s g‖ ≤ S.poleMajorant P T M d g := by
  have hg : 0 < ‖S.gamma g‖ := S.norm_gamma_pos g
  have hC : 0 ≤ polyBallBound P (S.lower⁻¹ ^ 2) := polyBallBound_nonneg P (by positivity)
  have hc := S.norm_traceCoeff_le P g
  have hn := S.norm_poleNumer_le T hs g
  have hMnn : 0 ≤ M := le_trans (norm_nonneg s) hs
  have hnum : ‖S.traceCoeff P g‖ * ‖S.poleNumer T s g‖ ≤
      (polyBallBound P (S.lower⁻¹ ^ 2) * ‖S.gamma g‖⁻¹ ^ 3) *
        (Real.exp ((M + S.width) * |T|) * (M + ‖S.gamma g‖)) :=
    mul_le_mul hc hn (norm_nonneg _) (by positivity)
  rw [poleTerm, norm_div, norm_mul]
  refine le_trans (div_le_div₀ (by positivity) hnum hd hden) (le_of_eq ?_)
  rw [poleMajorant]
  have hgne : ‖S.gamma g‖ ≠ 0 := ne_of_gt hg
  have hdne : d ≠ 0 := ne_of_gt hd
  field_simp

omit [Countable G] in
theorem differentiableOn_poleTerm (P : Polynomial ℝ) (T : ℝ) {U : Set ℂ} (g : G)
    (hden : ∀ s ∈ U, s ^ 2 + S.gamma g ^ 2 ≠ 0) :
    DifferentiableOn ℂ (fun s => S.poleTerm P T s g) U := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hne := hden s hs
  have hA : DifferentiableAt ℂ
      (fun z : ℂ => S.traceCoeff P g *
        (Complex.exp (-z * (T : ℂ)) *
          (z * Complex.sin (S.gamma g * (T : ℂ)) +
            S.gamma g * Complex.cos (S.gamma g * (T : ℂ))))) s := by
    fun_prop
  have hB : DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + S.gamma g ^ 2) s := by fun_prop
  have hdiv : DifferentiableAt ℂ
      (fun z : ℂ => (S.traceCoeff P g *
        (Complex.exp (-z * (T : ℂ)) *
          (z * Complex.sin (S.gamma g * (T : ℂ)) +
            S.gamma g * Complex.cos (S.gamma g * (T : ℂ))))) / (z ^ 2 + S.gamma g ^ 2)) s :=
    hA.div hB hne
  exact hdiv

omit [Countable G] in
/-- **Holomorphy of the active-pole transform.** On any bounded region whose distance to the
resolvent pole set is positive, the transform is holomorphic. -/
theorem differentiableOn_poleTransform (P : Polynomial ℝ) (T : ℝ) {U : Set ℂ} (hU : IsOpen U)
    {M d : ℝ} (hd : 0 < d)
    (hbd : ∀ s ∈ U, ‖s‖ ≤ M)
    (hden : ∀ s ∈ U, ∀ g, d ≤ ‖s ^ 2 + S.gamma g ^ 2‖) :
    DifferentiableOn ℂ (S.poleTransform P T) U := by
  refine differentiableOn_tsum_of_summable_norm (u := S.poleMajorant P T M d)
    (S.summable_poleMajorant P T M d) (fun g => ?_) hU (fun g s hs => ?_)
  · refine S.differentiableOn_poleTerm P T g (fun z hz => ?_)
    intro hzero
    have hb := hden z hz g
    rw [hzero, norm_zero] at hb
    linarith
  · exact S.norm_poleTerm_le P T hd (hbd s hs) g (hden s hs g)

end WaveSpectrum

end

end GaloisForLFunctions.HTGeometry
