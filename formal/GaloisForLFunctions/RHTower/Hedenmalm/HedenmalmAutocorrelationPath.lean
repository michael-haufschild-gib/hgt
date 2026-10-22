import GaloisForLFunctions.RHTower.ThetaWignerCenterMix
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmLocalFrameObstruction

/-!
# The Hedenmalm center-mixed density is an autocorrelation tangent

The positive center-mixed theta density is not an auxiliary Wigner coordinate.  After the exact
linear change from center/difference variables, it is the first variation of the autocorrelation
of the exponentially tilted theta source.  Thus the remaining spectral orientation is a genuine
order question for one canonical autocorrelation path.

The identification is unconditional.  It also extends integrability and continuity of the
center-mixed density from the critical half-aperture to the full Fourier--Laplace strip `|a| < 1`.
No positivity of a Fourier transform or Riemann-hypothesis assumption occurs here.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap Convolution ComplexConjugate

noncomputable section

namespace RHTower

private theorem half_integral_neg_exp_mul_even_eq_sinh_Ioi
    (a : ℝ) (h : ℝ → ℝ) (heven : ∀ r, h (-r) = h r)
    (hf : Integrable (fun r : ℝ =>
      (((-r * Real.exp (-a * r) * h r : ℝ)) : ℂ))) :
    ((1 / 2 : ℂ) * ∫ r : ℝ,
      (((-r * Real.exp (-a * r) * h r : ℝ)) : ℂ)) =
      ∫ r : ℝ in Ioi 0,
        (((r * Real.sinh (a * r) * h r : ℝ)) : ℂ) := by
  let f : ℝ → ℂ := fun r => (((-r * Real.exp (-a * r) * h r : ℝ)) : ℂ)
  let g : ℝ → ℂ := fun r => (((r * Real.sinh (a * r) * h r : ℝ)) : ℂ)
  have hfneg : Integrable (fun r => f (-r)) := hf.comp_neg
  have hfg : (fun r => (f r + f (-r)) / 2) = g := by
    funext r
    simp only [f, g, heven]
    rw [Real.sinh_eq]
    push_cast
    ring
  have hg : Integrable g := by
    rw [← hfg]
    exact (hf.add hfneg).div_const 2
  have hint_fg : (∫ r, f r) = ∫ r, g r := by
    rw [← hfg, integral_div, MeasureTheory.integral_add hf hfneg,
      MeasureTheory.integral_neg_eq_self f volume]
    ring
  let j : ℝ → ℂ := (Ioi (0 : ℝ)).indicator g
  have hj : Integrable j := hg.indicator measurableSet_Ioi
  have hjneg : Integrable (fun r => j (-r)) := hj.comp_neg
  have geven (r : ℝ) : g (-r) = g r := by
    change ((((-r) * Real.sinh (a * (-r)) * h (-r) : ℝ)) : ℂ) =
      (((r * Real.sinh (a * r) * h r : ℝ)) : ℂ)
    rw [heven, show a * (-r) = -(a * r) by ring, Real.sinh_neg]
    ring
  have hgj : g = fun r => j r + j (-r) := by
    funext r
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · have hnr : 0 < -r := by linarith
      rw [show j r = 0 by simp [j, not_lt.mpr hr.le],
        show j (-r) = g (-r) by simp [j, hnr], zero_add, geven]
    · simp [j, g]
    · have hnmem : -r ∉ Ioi (0 : ℝ) := by simp [hr.le]
      rw [show j r = g r by simp [j, hr],
        show j (-r) = 0 by simp [j, hnmem], add_zero]
  have hint_gj : (∫ r, g r) = 2 * ∫ r, j r := by
    rw [hgj, MeasureTheory.integral_add hj hjneg,
      MeasureTheory.integral_neg_eq_self j volume]
    ring
  have hj_set : (∫ r, j r) = ∫ r in Ioi (0 : ℝ), g r := by
    exact MeasureTheory.integral_indicator measurableSet_Ioi
  rw [hint_fg, hint_gj, hj_set]
  ring

private theorem integrable_schwartz_mul_conj_shift
    (u v : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun y : ℝ => u y * (starRingEnd ℂ) (v (y - x))) := by
  have hcont : Continuous (fun y : ℝ => (starRingEnd ℂ) (v (y - x))) :=
    Complex.continuous_conj.comp
      (v.continuous.comp (continuous_id.sub continuous_const))
  apply u.integrable.mul_bdd (c := (SchwartzMap.seminorm ℂ 0 0) v)
    hcont.aestronglyMeasurable
  filter_upwards with y
  simpa only [RCLike.norm_conj] using
    SchwartzMap.norm_le_seminorm ℂ v (y - x)

private theorem thetaCuspHorizontalAutocorrelationTangent_integrand_eq
    {a : ℝ} (ha : |a| < 1) (x y : ℝ) :
    thetaCuspRightLineTangent a ha y *
          (starRingEnd ℂ) (thetaCuspRightLineSource a ha (y - x)) +
        thetaCuspRightLineSource a ha y *
          (starRingEnd ℂ) (thetaCuspRightLineTangent a ha (y - x)) =
      ((-(2 * y - x) * Real.exp (-a * (2 * y - x)) *
        thetaCuspFullSource y * thetaCuspFullSource (y - x) : ℝ) : ℂ) := by
  simp only [thetaCuspRightLineTangent_apply,
    thetaCuspRightLineSource_apply, map_mul, Complex.conj_ofReal]
  push_cast
  simp only [map_neg, map_sub, Complex.conj_ofReal]
  have hexp : Complex.exp (-((a : ℂ) * (y : ℂ))) *
      Complex.exp (-((a : ℂ) * ((y : ℂ) - (x : ℂ)))) =
      Complex.exp (-((a : ℂ) * (2 * (y : ℂ) - (x : ℂ)))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = ((x : ℂ) - 2 * (y : ℂ)) *
        (Complex.exp (-((a : ℂ) * (y : ℂ))) *
          Complex.exp (-((a : ℂ) * ((y : ℂ) - (x : ℂ))))) *
        (thetaCuspFullSource y : ℂ) *
          (thetaCuspFullSource (y - x) : ℂ) := by ring
    _ = _ := by
      rw [hexp]
      congr 4 <;> ring

private theorem thetaCuspHorizontalAutocorrelationTangent_eq_integral
    {a : ℝ} (ha : |a| < 1) (x : ℝ) :
    thetaCuspHorizontalAutocorrelationTangent a ha x =
      ∫ y : ℝ, ((-(2 * y - x) * Real.exp (-a * (2 * y - x)) *
        thetaCuspFullSource y * thetaCuspFullSource (y - x) : ℝ) : ℂ) := by
  let u := thetaCuspRightLineSource a ha
  let v := thetaCuspRightLineTangent a ha
  have h1 := integrable_schwartz_mul_conj_shift v u x
  have h2 := integrable_schwartz_mul_conj_shift u v x
  change SchwartzMap.autocorrelationTangentSchwartz u v x = _
  rw [SchwartzMap.autocorrelationTangentSchwartz, _root_.add_apply]
  rw [SchwartzMap.crossCorrelationSchwartz, SchwartzMap.convolution_apply,
    SchwartzMap.crossCorrelationSchwartz, SchwartzMap.convolution_apply]
  rw [convolution_def, convolution_def]
  simp only [SchwartzMap.conjugateReflectionSchwartz_apply, neg_sub]
  change (∫ y : ℝ, v y * (starRingEnd ℂ) (u (y - x))) +
      (∫ y : ℝ, u y * (starRingEnd ℂ) (v (y - x))) = _
  rw [← MeasureTheory.integral_add h1 h2]
  apply integral_congr_ae
  filter_upwards with y
  dsimp only [u, v]
  convert thetaCuspHorizontalAutocorrelationTangent_integrand_eq ha x y using 1
  ring

/-- The pointwise-positive center-mixed theta density is exactly the first variation of the
canonical exponentially tilted autocorrelation path. -/
theorem thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity
    {a : ℝ} (ha : |a| < 1) (x : ℝ) :
    thetaCuspHorizontalAutocorrelationTangent a ha x =
      (thetaCuspCenterMixedDensity a (x / 2) : ℂ) := by
  let h : ℝ → ℝ := fun r =>
    thetaCuspFullSource (r / 2 + x / 2) *
      thetaCuspFullSource (r / 2 - x / 2)
  let f : ℝ → ℂ := fun r =>
    (((-r * Real.exp (-a * r) * h r : ℝ)) : ℂ)
  let H : ℝ → ℂ := fun y => f (2 * y - x)
  have hH : Integrable H := by
    let u := thetaCuspRightLineSource a ha
    let v := thetaCuspRightLineTangent a ha
    have h1 := integrable_schwartz_mul_conj_shift v u x
    have h2 := integrable_schwartz_mul_conj_shift u v x
    have hsum : Integrable (fun y : ℝ =>
        v y * (starRingEnd ℂ) (u (y - x)) +
          u y * (starRingEnd ℂ) (v (y - x))) := h1.add h2
    apply hsum.congr
    filter_upwards with y
    rw [thetaCuspHorizontalAutocorrelationTangent_integrand_eq ha x y]
    simp only [H, f, h]
    rw [show (2 * y - x) / 2 + x / 2 = y by ring,
      show (2 * y - x) / 2 - x / 2 = y - x by ring]
    ring
  have hfTwo : Integrable (fun y : ℝ => f (2 * y)) := by
    have hs := hH.comp_add_right (x / 2)
    convert hs using 1
    funext y
    simp only [H]
    congr 1
    ring
  have hf : Integrable f :=
    (integrable_comp_mul_left_iff f (by norm_num : (2 : ℝ) ≠ 0)).mp hfTwo
  have hshift : (∫ y : ℝ, H y) = ∫ y : ℝ, f (2 * y) := by
    have hs := MeasureTheory.integral_add_right_eq_self (μ := volume)
      (fun y : ℝ => f (2 * y)) (-x / 2)
    calc
      (∫ y : ℝ, H y) = ∫ y : ℝ, f (2 * (y + (-x / 2))) := by
        apply integral_congr_ae
        filter_upwards with y
        simp only [H]
        congr 1
        ring
      _ = ∫ y : ℝ, f (2 * y) := hs
  have hscale : (∫ y : ℝ, f (2 * y)) =
      (1 / 2 : ℂ) * ∫ r : ℝ, f r := by
    have hs := MeasureTheory.Measure.integral_comp_mul_left f 2
    norm_num at hs ⊢
    simpa [smul_eq_mul] using hs
  have heven : ∀ r, h (-r) = h r := by
    intro r
    simp only [h]
    rw [show -r / 2 + x / 2 = -(r / 2 - x / 2) by ring,
      show -r / 2 - x / 2 = -(r / 2 + x / 2) by ring,
      thetaCuspFullSource_neg, thetaCuspFullSource_neg]
    ring
  rw [thetaCuspHorizontalAutocorrelationTangent_eq_integral ha x]
  have hHfun : (fun y : ℝ =>
      ((-(2 * y - x) * Real.exp (-a * (2 * y - x)) *
        thetaCuspFullSource y * thetaCuspFullSource (y - x) : ℝ) : ℂ)) = H := by
    funext y
    simp only [H, f, h]
    rw [show (2 * y - x) / 2 + x / 2 = y by ring,
      show (2 * y - x) / 2 - x / 2 = y - x by ring]
    ring
  rw [hHfun]
  rw [hshift, hscale]
  have hsym := half_integral_neg_exp_mul_even_eq_sinh_Ioi a h heven hf
  rw [hsym]
  rw [thetaCuspCenterMixedDensity, ← integral_complex_ofReal]

/-- The actual center-mixed theta density is integrable on the full Fourier--Laplace aperture
`|a| < 1`, not only on the critical half-aperture. -/
theorem integrable_thetaCuspCenterMixedDensity_of_abs_lt_one
    {a : ℝ} (ha : |a| < 1) :
    Integrable (thetaCuspCenterMixedDensity a) := by
  have hcomp : Integrable (fun t : ℝ =>
      thetaCuspHorizontalAutocorrelationTangent a ha (2 * t)) :=
    (integrable_comp_mul_left_iff
      (thetaCuspHorizontalAutocorrelationTangent a ha)
      (by norm_num : (2 : ℝ) ≠ 0)).2
        (thetaCuspHorizontalAutocorrelationTangent a ha).integrable
  have heq : (fun t : ℝ =>
      thetaCuspHorizontalAutocorrelationTangent a ha (2 * t)) =
      fun t => (thetaCuspCenterMixedDensity a t : ℂ) := by
    funext t
    rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity ha]
    congr 2
    ring
  rw [heq] at hcomp
  simpa using hcomp.re

/-- The actual center-mixed theta density is continuous on the full Fourier--Laplace aperture. -/
theorem continuous_thetaCuspCenterMixedDensity_of_abs_lt_one
    {a : ℝ} (ha : |a| < 1) :
    Continuous (thetaCuspCenterMixedDensity a) := by
  have hcont : Continuous (fun t : ℝ =>
      thetaCuspHorizontalAutocorrelationTangent a ha (2 * t)) :=
    (thetaCuspHorizontalAutocorrelationTangent a ha).continuous.comp
      (continuous_const.mul continuous_id)
  have heq : thetaCuspCenterMixedDensity a = fun t =>
      (thetaCuspHorizontalAutocorrelationTangent a ha (2 * t)).re := by
    funext t
    rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity ha]
    simp
  rw [heq]
  exact Complex.continuous_re.comp hcont

/-- Throughout the critical aperture, the actual spatial autocorrelation tangent is strictly
positive pointwise.  This is the unconditional first, spatial orientation. -/
theorem thetaCuspHorizontalAutocorrelationTangent_re_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (x : ℝ) :
    0 < (thetaCuspHorizontalAutocorrelationTangent a
      (by rw [abs_of_pos ha0]; linarith) x).re := by
  rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity]
  simpa using thetaCuspCenterMixedDensity_pos ha0 ha (x / 2)

/-- The Hedenmalm tangent lies strictly inside the pointwise-positive cone while lying outside
all finite constant-coefficient differential autocorrelation-frame cones. -/
theorem thetaCuspHorizontalAutocorrelationTangent_strictlyPositive_not_finiteFrame
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    (∀ x : ℝ, 0 < (thetaCuspHorizontalAutocorrelationTangent a
      (by rw [abs_of_pos ha0]; linarith) x).re) ∧
    ¬ ∃ (n : ℕ) (p : Fin n → Polynomial ℂ),
      thetaCuspHorizontalAutocorrelationTangent a
          (by rw [abs_of_pos ha0]; linarith) =
        SchwartzMap.finitePolynomialAutocorrelationFrame p
          (thetaCuspRightLineSource a
            (by rw [abs_of_pos ha0]; linarith)) := by
  constructor
  · exact fun x => thetaCuspHorizontalAutocorrelationTangent_re_pos ha0 ha x
  · exact no_finitePolynomialAutocorrelationFrame_for_Hedenmalm_tangent
      ha0 (lt_trans ha (by norm_num))

end RHTower
