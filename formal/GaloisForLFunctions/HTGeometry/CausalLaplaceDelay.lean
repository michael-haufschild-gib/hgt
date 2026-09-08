import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral

/-! Translation of an actual causal function in a convergent complex Laplace integral. -/
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem causal_indicator_ae (f : ℝ → ℂ) (hf : ∀ t < 0, f t = 0) :
    (Ioi (0:ℝ)).indicator f =ᵐ[volume] f := by
  have hn : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with t ht
    simpa using ht
  filter_upwards [hn] with t ht
  by_cases hp : 0 < t
  · exact indicator_of_mem hp f
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from hp),hf t (lt_of_le_of_ne (le_of_not_gt hp) ht)]

/-- Causal support identifies the ray integral with the actual whole-line integral. -/
theorem causal_integral_ray (f : ℝ → ℂ) (hf : ∀ t < 0, f t = 0) :
    (∫ t in Ioi (0:ℝ), f t) = ∫ t, f t := by
  rw [← integral_indicator measurableSet_Ioi]
  exact integral_congr_ae (causal_indicator_ae f hf)

/-- Causal ray integrability extends to the whole time axis. -/
theorem causal_integrable_of_ray (f : ℝ → ℂ) (hf : ∀ t < 0, f t = 0)
    (hi : IntegrableOn f (Ioi 0)) : Integrable f :=
  ((integrable_indicator_iff measurableSet_Ioi).mpr hi).congr (causal_indicator_ae f hf)

private theorem delayed_weight (f : ℝ → ℂ) (w : ℂ) (d t : ℝ) :
    Complex.exp (-w*(t:ℂ))*f (t+d) = Complex.exp (w*(d:ℂ))*
      (Complex.exp (-w*((t+d:ℝ):ℂ))*f (t+d)) := by
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Delaying a causal source preserves absolute convergence of its complex Laplace transform. -/
theorem causal_laplace_delay_integrable (f : ℝ → ℂ) (hf : ∀ t < 0, f t = 0)
    (w : ℂ) (hi : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*f t) (Ioi 0))
    (d : ℝ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ))*f (t+d)) (Ioi 0) := by
  have hc := causal_integrable_of_ray _ (fun t ht => by rw [hf t ht,mul_zero]) hi
  have hd := (hc.comp_add_right d).const_mul (Complex.exp (w*(d:ℂ)))
  apply hd.integrableOn.congr
  exact Eventually.of_forall (fun t => (delayed_weight f w d t).symm)

/-- The original radial time delay gives its exact exponential factor, without retuning the source. -/
theorem causal_laplace_delay (f : ℝ → ℂ) (hf : ∀ t < 0, f t = 0)
    (w : ℂ) (d : ℝ) (hd : d ≤ 0) :
    (∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*f (t+d)) =
      Complex.exp (w*(d:ℂ))*(∫ t in Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*f t) := by
  rw [causal_integral_ray _ (fun t ht => by rw [hf (t+d) (by linarith),mul_zero])]
  simp_rw [delayed_weight f w d]
  rw [integral_const_mul,integral_add_right_eq_self (fun u : ℝ => Complex.exp (-w*(u:ℂ))*f u) d]
  rw [causal_integral_ray _ (fun t ht => by rw [hf t ht,mul_zero])]

end
end GaloisForLFunctions.HTGeometry
