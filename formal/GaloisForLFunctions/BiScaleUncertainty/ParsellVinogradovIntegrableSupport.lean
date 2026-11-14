import GaloisForLFunctions.BiScaleUncertainty.IntegrableFourierUniqueness
import GaloisForLFunctions.BiScaleUncertainty.ParsellVinogradovFourierSupport

/-!
# Integrable sources cannot have Fourier support on a graph

Fourier continuity and uniqueness give the `p = 1` case of Bi–Sun's
support theorem. The source need not be smooth, and the graph need not
be measurable or continuous. The conclusion concerns equality in `L¹`.
-/

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ParsellVinogradov
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Graph support of the classical Fourier transform characterizes the zero `L¹` source. -/
theorem l1_fourier_support_graph_iff
    (f : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Option ι))))
    (g : (ι → ℝ) → ℝ) :
    Function.support (𝓕 (f : EuclideanSpace ℝ (Option ι) → ℂ)) ⊆
      coordinateGraph g ↔ f = 0 := by
  constructor
  · intro hs
    have hf : Integrable (f : EuclideanSpace ℝ (Option ι) → ℂ) :=
      memLp_one_iff_integrable.mp (Lp.memLp f)
    let F : C(EuclideanSpace ℝ (Option ι), ℂ) :=
      ⟨𝓕 (f : EuclideanSpace ℝ (Option ι) → ℂ),
        VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
          (innerSL ℝ).continuous₂ hf⟩
    have hF := (continuous_support_graph_iff F g).mp hs
    have hzero : 𝓕 (f : EuclideanSpace ℝ (Option ι) → ℂ) = 0 := by
      funext ξ
      exact congrArg (fun h : C(EuclideanSpace ℝ (Option ι), ℂ) => h ξ) hF
    exact (FiniteDimensionalFourier.l1_fourier_eq_zero_iff f).mp hzero
  · intro hf
    rw [(FiniteDimensionalFourier.l1_fourier_eq_zero_iff f).mpr hf]
    simp

/-- The quadratic two-variable moment surface carries no nonzero integrable Fourier source. -/
theorem l1_fourier_support_quadraticMomentSurface_iff
    (f : Lp ℂ 1 (volume : Measure (EuclideanSpace ℝ (Option (Fin 4))))) :
    Function.support (𝓕 (f : EuclideanSpace ℝ (Option (Fin 4)) → ℂ)) ⊆
      quadraticMomentSurface ↔ f = 0 := by
  constructor
  · intro hs
    exact (l1_fourier_support_graph_iff f _).mp
      (hs.trans quadraticMomentSurface_subset_graph)
  · intro hf
    rw [(FiniteDimensionalFourier.l1_fourier_eq_zero_iff f).mpr hf]
    simp

#print axioms l1_fourier_support_graph_iff
#print axioms l1_fourier_support_quadraticMomentSurface_iff

end
end GaloisForLFunctions.BiScaleUncertainty.ParsellVinogradov
