import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Differentiation of smooth integrands over a fixed compact planar set

Compact product sets provide the uniform derivative bound required to pass a
real parameter derivative through the Bochner integral.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.CompactSmoothParameterIntegral
noncomputable section

def parameterDerivative (F : ℝ × (ℝ × ℝ) → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  fderiv ℝ F p (1,(0,0))

theorem parameterDerivative_smooth {F : ℝ × (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem slice_hasDerivAt {F : ℝ × (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun s => F (s,p)) (parameterDerivative F (t,p)) t :=
  (hF.differentiable (by simp) (t,p)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))

theorem integral_hasDerivAt {F : ℝ × (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (t : ℝ) :
    HasDerivAt (fun s => ∫ p in K, F (s,p))
      (∫ p in K, deriv (fun s => F (s,p)) t) t := by
  have hD := parameterDerivative_smooth hF
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hD.continuous.continuousOn : ContinuousOn (parameterDerivative F)
      (Icc (t-1) (t+1) ×ˢ K))
  have hneigh : Ioo (t-1) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hc (s : ℝ) : Continuous (fun p => F (s,p)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hd (s : ℝ) : Continuous (fun p => parameterDerivative F (s,p)) :=
    hD.continuous.comp (continuous_const.prodMk continuous_id)
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict K) (F := fun s p => F (s,p))
    (F' := fun s p => parameterDerivative F (s,p)) (bound := fun _ => C) hneigh
    (Eventually.of_forall fun s => (hc s).aestronglyMeasurable.restrict)
    ((hc t).continuousOn.integrableOn_compact hK)
    ((hd t).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
        intro s hs
        exact hC (s,p) ⟨⟨hs.1.le,hs.2.le⟩,hp⟩)
    (integrable_const C)
    (by filter_upwards with p
        intro s _
        exact slice_hasDerivAt hF s p)).2
  have he : (fun p => deriv (fun s => F (s,p)) t) =
      fun p => parameterDerivative F (t,p) :=
    funext fun p => (slice_hasDerivAt hF t p).deriv
  simpa only [he] using h

end
end GaloisForLFunctions.HTGeometry.CompactSmoothParameterIntegral
