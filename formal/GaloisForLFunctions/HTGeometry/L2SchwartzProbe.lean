import Mathlib.Analysis.Distribution.TemperedDistribution

/-! Continuous Schwartz probes of the original L² space and their Bochner compatibility. -/
open MeasureTheory TemperedDistribution
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Evaluation on a Schwartz test is a bounded functional of the original L² class. -/
def l2SchwartzProbe (ψ : 𝓢(ℝ,ℂ)) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ ψ).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)

theorem l2SchwartzProbe_apply (ψ : 𝓢(ℝ,ℂ)) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    l2SchwartzProbe ψ f = (f : 𝓢'(ℝ,ℂ)) ψ := rfl

/-- The native integral pairing is exactly this continuous functional. -/
theorem l2SchwartzProbe_integral (ψ : 𝓢(ℝ,ℂ)) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    l2SchwartzProbe ψ f = ∫ x : ℝ, ψ x • f x := Lp.toTemperedDistribution_apply f ψ

/-- A norm-convergent Laplace integral can be paired with a fixed spatial Schwartz test. -/
theorem l2SchwartzProbe_laplace (ψ : 𝓢(ℝ,ℂ)) (f : ℝ → Lp ℂ 2 (volume : Measure ℝ))
    (w : ℂ) (hi : IntegrableOn (fun t : ℝ => Complex.exp (-w*(t:ℂ)) • f t) (Set.Ioi 0)) :
    (∫ t in Set.Ioi (0:ℝ), Complex.exp (-w*(t:ℂ))*l2SchwartzProbe ψ (f t)) =
      l2SchwartzProbe ψ (∫ t in Set.Ioi (0:ℝ), Complex.exp (-w*(t:ℂ)) • f t) := by
  simpa only [map_smul,smul_eq_mul] using (l2SchwartzProbe ψ).integral_comp_comm hi

end
end GaloisForLFunctions.HTGeometry
