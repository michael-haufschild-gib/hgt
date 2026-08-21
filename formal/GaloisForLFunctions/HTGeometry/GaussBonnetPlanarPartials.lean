import Mathlib

/-!
# Partial derivatives on the plane, and interval Fubini for continuous fields

A small reusable calculus layer used by the Gauss--Bonnet development: the two coordinate partial
derivatives of a smooth function on `ℝ × ℝ`, their smoothness, the fact that they compute the
derivatives of the coordinate slices, and the interchange of two interval integrals for a
continuous field.

Nothing here is specific to Gauss--Bonnet; it is the plain multivariable-calculus interface the
orthogonal-patch curvature computation needs.
-/

open MeasureTheory intervalIntegral
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry.GaussBonnet

/-- The partial derivative of a planar field in its first coordinate. -/
noncomputable def px (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (1, 0)

/-- The partial derivative of a planar field in its second coordinate. -/
noncomputable def py (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ F p (0, 1)

variable {F : ℝ × ℝ → ℝ}

/-- The first partial derivative differentiates the first coordinate slice. -/
theorem hasDerivAt_px (hF : ContDiff ℝ ∞ F) (u v : ℝ) :
    HasDerivAt (fun t : ℝ => F (t, v)) (px F (u, v)) u := by
  have h1 : HasFDerivAt F (fderiv ℝ F (u, v)) (u, v) :=
    (hF.differentiable (by simp) _).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (t, v)) ((1 : ℝ), (0 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  have h3 := h1.comp_hasDerivAt u h2
  simpa [Function.comp_def, px] using h3

/-- The second partial derivative differentiates the second coordinate slice. -/
theorem hasDerivAt_py (hF : ContDiff ℝ ∞ F) (u v : ℝ) :
    HasDerivAt (fun t : ℝ => F (u, t)) (py F (u, v)) v := by
  have h1 : HasFDerivAt F (fderiv ℝ F (u, v)) (u, v) :=
    (hF.differentiable (by simp) _).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (u, t)) ((0 : ℝ), (1 : ℝ)) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
  have h3 := h1.comp_hasDerivAt v h2
  simpa [Function.comp_def, py] using h3

theorem contDiff_px (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (px F) := by
  unfold px
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_py (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (py F) := by
  unfold py
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem continuous_px (hF : ContDiff ℝ ∞ F) : Continuous (px F) := (contDiff_px hF).continuous

theorem continuous_py (hF : ContDiff ℝ ∞ F) : Continuous (py F) := (contDiff_py hF).continuous

/-- Slicing a continuous planar field in the first coordinate. -/
theorem continuous_sliceFst {f : ℝ × ℝ → ℝ} (hf : Continuous f) (v : ℝ) :
    Continuous fun u : ℝ => f (u, v) := by fun_prop

/-- Slicing a continuous planar field in the second coordinate. -/
theorem continuous_sliceSnd {f : ℝ × ℝ → ℝ} (hf : Continuous f) (u : ℝ) :
    Continuous fun v : ℝ => f (u, v) := by fun_prop

/-- **Interval Fubini for a continuous planar field.** -/
theorem intervalIntegral_swap {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ y in c..d, ∫ x in a..b, F x y := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
  have hK : IsCompact (Set.uIcc a b ×ˢ Set.uIcc c d) := isCompact_uIcc.prod isCompact_uIcc
  have hInt : IntegrableOn (Function.uncurry F) (Set.uIcc a b ×ˢ Set.uIcc c d) volume :=
    ContinuousOn.integrableOn_compact hK hF.continuousOn
  exact hInt.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

end GaloisForLFunctions.HTGeometry.GaussBonnet
