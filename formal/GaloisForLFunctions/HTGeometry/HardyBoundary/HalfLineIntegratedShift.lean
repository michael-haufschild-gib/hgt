import GaloisForLFunctions.HTGeometry.HardyBoundary.HalfLineShiftLaplace
import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskHalfLineCayley
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Exponential averages of causal translations

The exponential average of the causal shifts preserves every closed invariant
subspace. Its Laplace multiplier is `(1+w)⁻¹`, the resolvent needed for the
Cayley shift on disk Hardy space.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The exponential average of positive translations, extended continuously to real parameters. -/
def halfLineShiftAverageIntegrand (f : BurnolHalfLineL2) (t : ℝ) : BurnolHalfLineL2 :=
  (Real.exp (-t) : ℂ) • burnolRightShift ⟨max t 0, le_max_right _ _⟩ f

theorem continuous_halfLineShiftAverageIntegrand (f : BurnolHalfLineL2) :
    Continuous (halfLineShiftAverageIntegrand f) := by
  have hc : Continuous (fun t : ℝ => (⟨max t 0, le_max_right _ _⟩ : ℝ≥0)) :=
    (continuous_id.max continuous_const).subtype_mk _
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul
    ((continuous_burnolRightShift f).comp hc)

theorem integrableOn_halfLineShiftAverageIntegrand (f : BurnolHalfLineL2) :
    IntegrableOn (halfLineShiftAverageIntegrand f) (Ioi (0 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-t) * ‖f‖) (Ioi 0) volume := by
    have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) volume := by
      apply (exp_neg_integrableOn_Ioi (0 : ℝ) (zero_lt_one : (0 : ℝ) < 1)).congr
      exact Eventually.of_forall fun t => by
        change Real.exp (-1 * t) = Real.exp (-t)
        rw [neg_one_mul]
    exact he.mul_const ‖f‖
  apply hmaj.mono' (continuous_halfLineShiftAverageIntegrand f).aestronglyMeasurable.restrict
  exact Eventually.of_forall fun t => by
    rw [halfLineShiftAverageIntegrand, norm_smul, norm_burnolRightShift_apply,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The causal resolvent at parameter one. -/
def halfLineShiftAverage (f : BurnolHalfLineL2) : BurnolHalfLineL2 :=
  ∫ t in Ioi (0 : ℝ), halfLineShiftAverageIntegrand f t

/-- Closed translation-invariant subspaces are preserved by the exponential average. -/
theorem halfLineShiftAverage_mem (M : Submodule ℂ BurnolHalfLineL2)
    (hc : IsClosed (M : Set BurnolHalfLineL2))
    (hshift : ∀ h : ℝ≥0, ∀ f ∈ M, burnolRightShift h f ∈ M)
    {f : BurnolHalfLineL2} (hf : f ∈ M) : halfLineShiftAverage f ∈ M := by
  letI : CompleteSpace M := hc.completeSpace_coe
  have hm (t : ℝ) : halfLineShiftAverageIntegrand f t ∈ M :=
    M.smul_mem _ (hshift _ f hf)
  let g : ℝ → M := fun t => ⟨halfLineShiftAverageIntegrand f t, hm t⟩
  have hgcont : Continuous g :=
    (continuous_halfLineShiftAverageIntegrand f).subtype_mk hm
  have hg : IntegrableOn g (Ioi (0 : ℝ)) volume :=
    (integrableOn_halfLineShiftAverageIntegrand f).norm.mono'
      hgcont.aestronglyMeasurable.restrict (Eventually.of_forall fun _ => le_rfl)
  have he := M.subtypeL.integral_comp_comm hg
  change (∫ t in Ioi (0 : ℝ), halfLineShiftAverageIntegrand f t) =
    ((∫ t in Ioi (0 : ℝ), g t) : M).val at he
  rw [halfLineShiftAverage, he]
  exact (∫ t in Ioi (0 : ℝ), g t).property

/-- The averaged translations have the Cauchy resolvent multiplier. -/
theorem laplaceRay_halfLineShiftAverage (f : BurnolHalfLineL2)
    {w : ℂ} (hw : 0 < w.re) :
    laplaceRay (halfLineShiftAverage f) w = (1 + w)⁻¹ * laplaceRay f w := by
  let K : BurnolHalfLineL2 := halfLineLaplaceFeature w hw
  have hK (g : BurnolHalfLineL2) : inner ℂ K g = laplaceRay g w :=
    halfLineLaplaceTransform_eq_laplaceRay g hw
  rw [← hK (halfLineShiftAverage f), halfLineShiftAverage]
  rw [← integral_inner (integrableOn_halfLineShiftAverageIntegrand f)]
  have he : (∫ t in Ioi (0 : ℝ), inner ℂ K
      (halfLineShiftAverageIntegrand f t)) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-((1 + w) * (t : ℂ))) * laplaceRay f w := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [halfLineShiftAverageIntegrand, inner_smul_right, hK, laplaceRay_burnolRightShift]
    change (Real.exp (-t) : ℂ) *
      (Complex.exp (-w * ((max t 0 : ℝ) : ℂ)) * laplaceRay f w) = _
    rw [max_eq_left ht.le, Complex.ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, integral_mul_const]
  have h := integral_exp_mul_complex_Ioi (a := -(1 + w))
    (by simp only [neg_re, add_re, one_re]; linarith only [hw]) 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  have heexp : (fun t : ℝ => Complex.exp (-((1 + w) * (t : ℂ)))) =
      fun t : ℝ => Complex.exp (-(1 + w) * (t : ℂ)) := by
    funext t
    rw [neg_mul]
  rw [heexp, h, neg_div_neg_eq, one_div]

#print axioms halfLineShiftAverage_mem
#print axioms laplaceRay_halfLineShiftAverage

end GaloisForLFunctions.HTGeometry
