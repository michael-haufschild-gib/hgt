import GaloisForLFunctions.HTGeometry.VarianceGaugeRigidity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A continuous Gaussian L2 observable has zero variance exactly when it is constant everywhere. -/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem gaussianReal_variance_eq_zero_iff_constant
    (m : ℝ) (v : NNReal) (hv : v ≠ 0) {f : ℝ → ℝ}
    (hc : Continuous f) (hf : MemLp f 2 (gaussianReal m v)) :
    variance f (gaussianReal m v) = 0 ↔ ∀ x : ℝ, f x = f 0 := by
  rw [variance_eq_zero_iff_ae_const hf]
  constructor
  · rintro ⟨c, h⟩
    have hvol : f =ᵐ[volume] fun _ => c :=
      (gaussianReal_absolutelyContinuous' m hv).ae_eq h
    have heq : f = fun _ => c := (hc.ae_eq_iff_eq volume continuous_const).mp hvol
    intro x
    exact (congrFun heq x).trans (congrFun heq 0).symm
  · intro h
    exact ⟨f 0, Filter.Eventually.of_forall h⟩

end GaloisForLFunctions.HTGeometry
