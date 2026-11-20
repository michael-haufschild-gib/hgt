import GaloisForLFunctions.goldbach.LiLiu.Mellin.ProfileDecay
import GaloisForLFunctions.goldbach.LiLiu.Arithmetic.EulerBounds
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound

/-! # Shifting the signed density contour through its removable pole -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set MeasureTheory
noncomputable section

/-- On the finite-height rectangle continuity extends the high-ordinate bound. -/
private theorem extend_height_bound {a b D : ℝ} {F : ℂ → ℂ}
    (hc : ∀ s : ℂ, s.re ∈ Icc a b → ContinuousAt F s)
    (ht : ∀ s : ℂ, s.re ∈ Icc a b → 2 ≤ |s.im| → ‖F s‖*(1+s.im^2) ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖F s‖ ≤ B/(1+s.im^2) := by
  let K := Icc a b ×ˢ Icc (-2:ℝ) 2
  let f := fun x : ℝ × ℝ => ‖F ((x.1:ℂ)+x.2*I)‖ * (1+x.2^2)
  have hcont : ContinuousOn f K := by
    intro x hx
    exact (((hc _ (by simpa using hx.1)).comp (by fun_prop)).norm.mul (by fun_prop)).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max 0 (max C D), le_max_left .., fun s hs => (le_div_iff₀ (by positivity)).mpr ?_⟩
  apply le_trans _ (le_max_right ..)
  by_cases h : 2 ≤ |s.im|
  · exact (ht s hs h).trans (le_max_right ..)
  · have hb := hC (s.re,s.im) (show (s.re,s.im) ∈ K from ⟨hs,abs_le.mp (le_of_not_ge h)⟩)
    have h0 : 0 ≤ ‖F s‖*(1+s.im^2) := by positivity
    simp only [f,Complex.re_add_im,Real.norm_eq_abs,abs_of_nonneg h0] at hb
    exact hb.trans (le_max_left ..)

theorem profileMellin_vertical_integrable (φ : TestWeight) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => profileMellin φ ((σ:ℂ)+t*I)) := by
  obtain ⟨D,hD,hd⟩ := profileMellin_height_bound φ hσ
  have hc (s : ℂ) (hs : s.re ∈ Icc σ σ) := (profileMellin_differentiableAt φ (hσ.trans_le hs.1)).continuousAt
  obtain ⟨B,_,hb⟩ := extend_height_bound (D := 2*D) hc (by
    intro s hs ht
    have hpow : 1+s.im^2 ≤ 2*|s.im|^3 := by
      have hh := mul_nonneg (sq_nonneg |s.im|) (show 0 ≤ |s.im|-1 by linarith only [ht])
      nlinarith only [hh,sq_abs s.im,ht,sq_nonneg (|s.im|-1)]
    have H := mul_le_mul_of_nonneg_left hpow (norm_nonneg (profileMellin φ s))
    linarith only [H,hd s (hσ.trans_le hs.1) hs.2 (by linarith only [ht])])
  have hcont : Continuous (fun t : ℝ => profileMellin φ ((σ:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc _ (by simp)).comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul B).mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa [div_eq_mul_inv] using hb ((σ:ℂ)+t*I) (by simp)

theorem continuedProfileDensity_strip_bound (N : ℕ) (φ : TestWeight) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc a (3/2) →
      ‖continuedProfileDensity N φ s‖ ≤ B/(1+s.im^2) := by
  obtain ⟨D,hD,hd⟩ := profileMellin_height_bound φ (by norm_num : (0:ℝ)<3/2)
  obtain ⟨E,hE,he⟩ := densityEuler_norm_bound ha
  let C := singularSeries N * E * (1 + 2/a)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (singularSeries_pos N).le hE.le) (by positivity)
  apply extend_height_bound (D := C*(2*D))
    (fun s hs => (continuedProfileDensity_differentiableAt N φ (ha.trans_le hs.1)).continuousAt)
  intro s hs ht
  have hne : s ≠ 1 := by intro H; norm_num [H] at ht
  have hζ := _root_.RHTower.norm_riemannZeta_le_of_re_pos (ha.trans_le hs.1)
    (by linarith only [hs.2]) ht
  rw [Complex.re_add_im] at hζ
  have hquot := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * |s.im|) ha hs.1
  have hz : ‖riemannZeta s‖ ≤ (1+2/a)*|s.im| := calc
    _ ≤ 2 + 2*|s.im|/s.re := hζ
    _ ≤ |s.im| + 2*|s.im|/a := add_le_add ht hquot
    _ = _ := by ring
  have h2 : 1+s.im^2 ≤ 2*|s.im|^2 := by nlinarith only [sq_abs s.im, ht, sq_nonneg (|s.im|-1)]
  rw [continuedProfileDensity_eq hne, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (singularSeries_pos _)]
  calc
    _ ≤ singularSeries N * ((1+2/a)*|s.im|) * E * ‖profileMellin φ s‖ * (2*|s.im|^2) := by
      have hS := (singularSeries_pos N).le
      have hEuler := he N s hs.1
      gcongr
    _ = C * (2*(|s.im|^3 * ‖profileMellin φ s‖)) := by dsimp [C]; ring
    _ ≤ _ := by gcongr; exact hd s (ha.trans_le hs.1) hs.2 (by linarith only [ht])

theorem model_contour_shift (N : ℕ) (φ : TestWeight) {a : ℝ} (ha : 0 < a) (hb : a ≤ 3/2) :
    (∫ t : ℝ, continuedProfileDensity N φ ((a:ℂ)+t*I)) =
      ∫ t : ℝ, continuedProfileDensity N φ (((3/2:ℝ):ℂ)+t*I) := by
  obtain ⟨B,_,hbound⟩ := continuedProfileDensity_strip_bound N φ ha
  apply HTGeometry.integral_vertical_line_shift_of_decay (C := B)
  · intro s hs
    rw [uIcc_of_le hb] at hs
    exact continuedProfileDensity_differentiableAt N φ (ha.trans_le hs.1)
  · simpa only [uIcc_of_le hb] using hbound

#print axioms profileMellin_vertical_integrable
#print axioms model_contour_shift
end
end GaloisForLFunctions.Goldbach.LiLiu
