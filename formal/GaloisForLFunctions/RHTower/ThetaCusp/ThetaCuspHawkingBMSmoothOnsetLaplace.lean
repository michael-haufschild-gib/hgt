import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact transform and entire correction for the fixed smooth ingoing onset. -/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
set_option autoImplicit false
noncomputable section

/-- The actual scalar transform of the fixed smooth onset. -/
def onsetTransform (v w : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), (Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))

/-- The finite transition correction, retaining its original smooth profile. -/
def onsetCorrection (v w : ℂ) : ℂ :=
  ∫ u in Ioc (0:ℝ) 1, ((Real.smoothTransition u:ℂ)-1)*Complex.exp ((v-w)*(u:ℂ))

private def onsetDifference : ℝ → ℂ :=
  (Ioc (0:ℝ) 1).indicator (fun u => (Real.smoothTransition u:ℂ)-1)

private theorem difference_bound (u : ℝ) : ‖(Real.smoothTransition u:ℂ)-1‖ ≤ 1 := by
  have hc := Real.smoothTransition.le_one u
  have hz := Real.smoothTransition.nonneg u
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hc)]
  linarith

private theorem difference_memLp : MemLp onsetDifference 2 (volume.restrict (Ioi (0:ℝ))) := by
  rw [onsetDifference,memLp_indicator_iff_restrict measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)]
  apply MemLp.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall difference_bound

private theorem correction_trunc (v w : ℂ) :
    onsetCorrection v w = laplaceRayTrunc onsetDifference 1 (w-v) := by
  unfold onsetCorrection laplaceRayTrunc
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  rw [onsetDifference,indicator_of_mem hu]
  simp only [expRay]
  congr 2
  ring

/-- The actual compact transition contributes an entire function of frequency. -/
theorem onsetCorrection_entire (v : ℂ) : Differentiable ℂ (onsetCorrection v) := by
  have he : onsetCorrection v = fun w => laplaceRayTrunc onsetDifference 1 (w-v) :=
    funext (correction_trunc v)
  rw [he]
  exact (differentiable_laplaceRayTrunc difference_memLp (by norm_num)).comp
    (differentiable_id.sub_const v)

/-- Absolute convergence of the actual smooth-onset transform in its time chamber. -/
theorem onsetTransform_integrable (v w : ℂ) (hw : v.re < w.re) :
    IntegrableOn (fun u : ℝ => (Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))) (Ioi 0) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := v-w) (by simpa only [Complex.sub_re,sub_neg] using hw) 0
  apply h.norm.mono' (by fun_prop)
  filter_upwards with u
  rw [norm_mul]
  have hc : ‖(Real.smoothTransition u:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg u)] using
      Real.smoothTransition.le_one u
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)

/-- Smoothing the onset adds exactly the entire compact transition correction
to the original source pole; no asymptotic or numerical substitution is used. -/
theorem onsetTransform_eq (v w : ℂ) (hw : v.re < w.re) :
    onsetTransform v w = 1/(w-v)+onsetCorrection v w := by
  have hExp := integrableOn_exp_mul_complex_Ioi (a := v-w) (by simpa only [Complex.sub_re,sub_neg] using hw) 0
  have hχ := onsetTransform_integrable v w hw
  have hi : (∫ u in Ioi (0:ℝ), (Real.smoothTransition u:ℂ)*Complex.exp ((v-w)*(u:ℂ))-
      Complex.exp ((v-w)*(u:ℂ))) = onsetCorrection v w := by
    calc
      _ = ∫ u in Ioi (0:ℝ), (Ioc (0:ℝ) 1).indicator
          (fun u => ((Real.smoothTransition u:ℂ)-1)*Complex.exp ((v-w)*(u:ℂ))) u := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        by_cases h1 : u ≤ 1
        · rw [indicator_of_mem (show u ∈ Ioc (0:ℝ) 1 from ⟨hu,h1⟩)]
          ring
        · rw [indicator_of_notMem (show u ∉ Ioc (0:ℝ) 1 from fun h => h1 h.2),
            Real.smoothTransition.one_of_one_le (le_of_not_ge h1)]
          simp
      _ = onsetCorrection v w := by
        rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (show Ioc (0:ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)]
        rfl
  rw [integral_sub hχ hExp] at hi
  have hvalue : (∫ u in Ioi (0:ℝ), Complex.exp ((v-w)*(u:ℂ))) = 1/(w-v) := by
    rw [integral_exp_mul_complex_Ioi (a := v-w) (by simpa only [Complex.sub_re,sub_neg] using hw) 0]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    rw [show v-w=-(w-v) by ring,neg_div_neg_eq]
  rw [hvalue] at hi
  exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)

end
end RHTower.D4BMModularCore
