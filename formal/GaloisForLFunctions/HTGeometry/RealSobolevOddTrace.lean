import GaloisForLFunctions.HTGeometry.RealSobolevContinuousRepresentative
import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A Sobolev representative turns Hilbert-space oddness into an actual zero boundary trace. -/
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- An actual continuous representative inherits the reflection identity of its L² class pointwise. -/
theorem continuousRepresentative_odd (u : FourierRealL2) (hu : l2Reflection u = -u)
    (f : ℝ → ℂ) (hf : Continuous f) (ha : f =ᵐ[volume] u) : ∀ x : ℝ, f (-x) = -f x := by
  have hr : l2Reflection u =ᵐ[volume] (fun x : ℝ => u (-x)) :=
    Lp.coeFn_compMeasurePreserving u (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae ha
  have he : (fun x : ℝ => f (-x)) =ᵐ[volume] (fun x : ℝ => -f x) := by
    filter_upwards [ha,hr,hn,Lp.coeFn_neg u] with x hx hr hn hneg
    rw [hn,hx]
    rw [hu] at hr
    exact hr.symm.trans hneg
  have h := Measure.eq_of_ae_eq he (hf.comp continuous_neg) hf.neg
  exact fun x => congrFun h x

/-- Odd Sobolev data have a continuous representative whose value at the original endpoint is zero. -/
theorem real_sobolev_odd_zero_trace (u : FourierRealL2)
    (hu : l2Reflection u = -u) (s : ℝ) (hs : 1 < 2*s) (hS : MemSobolev s 2 (u : 𝓢'(ℝ,ℂ))) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[volume] u ∧ (∀ x : ℝ, f (-x) = -f x) ∧ f 0 = 0 := by
  obtain ⟨f,hf,ha⟩ := real_sobolev_continuous_representative u s hs hS
  have ho := continuousRepresentative_odd u hu f hf ha
  refine ⟨f,hf,ha,ho,?_⟩
  have h : f 0 = -f 0 := by simpa only [neg_zero] using ho 0
  have hm : (2:ℂ)*f 0 = 0 := by linear_combination h
  exact (mul_eq_zero.mp hm).resolve_left (by norm_num)

end
end GaloisForLFunctions.HTGeometry
