import GaloisForLFunctions.Bottcher.ModularLambdaCuspNormal
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Recovery and smoothness for the two explicit sphere charts

The existing stereographic and inverse-coordinate formulas recover every
unit vector outside their respective poles. Their denominators stay
positive, and both maps are smooth on the entire complex coordinate plane.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SphericalChartRecovery
open Bottcher
noncomputable section
abbrev Space := EuclideanSpace ℝ (Fin 3)

private theorem unit_coordinates {v : Space} (hv : ‖v‖ = 1) :
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
  have h := congrArg (fun t : ℝ => t ^ 2) hv
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three] at h
  simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h

/-- The finite chart recovers every unit vector except the north pole. -/
theorem stereo_finiteChart {v : Space} (hv : ‖v‖ = 1) (hn : v 2 ≠ 1) :
    stereo (stereoFiniteChart v) = v := by
  have hd : 1 - v 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hu := unit_coordinates hv
  let w := stereoFiniteChart v
  have hr : w.re = v 0 / (1 - v 2) := by
    simp [w, stereoFiniteChart, Complex.div_re, Complex.normSq_apply]
    field_simp [hd]
  have hi : w.im = v 1 / (1 - v 2) := by
    simp [w, stereoFiniteChart, Complex.div_im, Complex.normSq_apply]
    field_simp [hd]
  have hs : 1 + ‖w‖ ^ 2 = 2 / (1 - v 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    field_simp [hd]
    nlinarith only [hu]
  have hsq : ‖w‖ ^ 2 = 2 / (1 - v 2) - 1 := by linarith only [hs]
  change stereo w = v
  ext i
  fin_cases i
  · change 2 * w.re / (1 + ‖w‖ ^ 2) = v 0
    rw [hr, hs]
    field_simp [hd]
  · change 2 * w.im / (1 + ‖w‖ ^ 2) = v 1
    rw [hi, hs]
    field_simp [hd]
  · change (‖w‖ ^ 2 - 1) / (1 + ‖w‖ ^ 2) = v 2
    rw [hs, hsq]
    field_simp [hd]
    ring

/-- The inverse chart recovers every unit vector except the south pole. -/
theorem stereoInvExtended_inverseChart {v : Space} (hv : ‖v‖ = 1) (hn : v 2 ≠ -1) :
    stereoInvExtended (stereoInvChart v) = v := by
  have hd : 1 + v 2 ≠ 0 := by intro h; apply hn; linarith only [h]
  have hu := unit_coordinates hv
  let w := stereoInvChart v
  have hr : w.re = v 0 / (1 + v 2) := by
    simp [w, stereoInvChart, Complex.div_re, Complex.normSq_apply]
    field_simp [hd]
  have hi : w.im = -v 1 / (1 + v 2) := by
    simp [w, stereoInvChart, Complex.div_im, Complex.normSq_apply]
    field_simp [hd]
  have hs : 1 + ‖w‖ ^ 2 = 2 / (1 + v 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]
    field_simp [hd]
    nlinarith only [hu]
  have hsq : ‖w‖ ^ 2 = 2 / (1 + v 2) - 1 := by linarith only [hs]
  change stereoInvExtended w = v
  ext i
  fin_cases i
  · change 2 * w.re / (1 + ‖w‖ ^ 2) = v 0
    rw [hr, hs]
    field_simp [hd]
  · change -2 * w.im / (1 + ‖w‖ ^ 2) = v 1
    rw [hi, hs]
    field_simp [hd]
  · change (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2) = v 2
    rw [hs, hsq]
    field_simp [hd]
    ring

/-- On the unit sphere, the exceptional coordinate really is the single north pole. -/
theorem third_eq_one_iff {v : Space} (hv : ‖v‖ = 1) :
    v 2 = 1 ↔ v = northPole := by
  constructor
  · intro h
    have hu := unit_coordinates hv
    have h₀ : v 0 = 0 := by nlinarith only [hu, h, sq_nonneg (v 1)]
    have h₁ : v 1 = 0 := by nlinarith only [hu, h, sq_nonneg (v 0)]
    ext i
    fin_cases i <;> simp [northPole, h₀, h₁, h]
  · intro h
    rw [h]
    simp [northPole]

theorem norm_stereoInvExtended (z : ℂ) : ‖stereoInvExtended z‖ = 1 := by
  by_cases hz : z = 0
  · subst z
    rw [stereoInvExtended_zero]
    simp [northPole, norm_euclidean3]
  · have he : stereoInvExtended z = stereo z⁻¹ := by
      simpa only [inv_inv] using (stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)).symm
    rw [he]
    exact norm_stereo_eq_one _

/-- The inverse-coordinate chart recovers its own complex parameter, including the north pole. -/
theorem inverseChart_stereoInvExtended (z : ℂ) :
    stereoInvChart (stereoInvExtended z) = z := by
  by_cases hz : z = 0
  · subst z
    simp [stereoInvExtended_zero, northPole, stereoInvChart]
  · have he : stereoInvExtended z = stereo z⁻¹ := by
      simpa only [inv_inv] using (stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)).symm
    rw [he, stereoInvChart_stereo (inv_ne_zero hz), inv_inv]

private theorem contDiff_three {f₀ f₁ f₂ : ℂ → ℝ}
    (h₀ : ContDiff ℝ ∞ f₀) (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂) :
    ContDiff ℝ ∞ (fun z => (!₂[f₀ z, f₁ z, f₂ z] : Space)) := by
  have h : ContDiff ℝ ∞ (fun z => (![f₀ z, f₁ z, f₂ z] : Fin 3 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contDiff.comp h

theorem stereo_smooth : ContDiff ℝ ∞ stereo := by
  have hd : ContDiff ℝ ∞ (fun z : ℂ => 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℂ)
  unfold stereo
  apply contDiff_three
  · exact (contDiff_const.mul Complex.reCLM.contDiff).div hd (fun z => by positivity)
  · exact (contDiff_const.mul Complex.imCLM.contDiff).div hd (fun z => by positivity)
  · exact ((contDiff_norm_sq ℂ).sub contDiff_const).div hd (fun z => by positivity)

theorem stereoInvExtended_smooth : ContDiff ℝ ∞ stereoInvExtended := by
  have hd : ContDiff ℝ ∞ (fun z : ℂ => 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℂ)
  unfold stereoInvExtended
  apply contDiff_three
  · exact (contDiff_const.mul Complex.reCLM.contDiff).div hd (fun z => by positivity)
  · exact (contDiff_const.mul Complex.imCLM.contDiff).div hd (fun z => by positivity)
  · exact (contDiff_const.sub (contDiff_norm_sq ℂ)).div hd (fun z => by positivity)

#print axioms stereo_finiteChart
#print axioms stereoInvExtended_inverseChart
#print axioms third_eq_one_iff
#print axioms norm_stereoInvExtended
#print axioms inverseChart_stereoInvExtended
#print axioms stereo_smooth
#print axioms stereoInvExtended_smooth
end
end GaloisForLFunctions.HilbertMetric.Geometry.SphericalChartRecovery
