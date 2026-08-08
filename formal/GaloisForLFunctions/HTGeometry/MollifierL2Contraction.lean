import GaloisForLFunctions.HTGeometry.YoungConvolutionL2
import GaloisForLFunctions.HTGeometry.MollifierPositionCommutator

/-!
# Mollification does not increase `L²` energy

The mollifier of this corpus is literally the line convolution, so Young's inequality applies to it
unchanged.  Against a probability density the total mass is one, and mollification becomes an `L²`
contraction — which is what makes a mollified family uniformly bounded, and hence what feeds the
weak-limit passage.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem mollify_eq_lineConvolution (ρ u : ℝ → ℝ) : mollify ρ u = lineConvolution ρ u := rfl

/-- **Young's inequality for the mollifier.** -/
theorem integral_sq_mollify_le {ρ u : ℝ → ℝ} (hρm : Measurable ρ) (hum : Measurable u)
    (hρi : Integrable (fun t => |ρ t|)) (hu2 : Integrable (fun x => u x ^ 2))
    (hconv : Integrable (fun x => mollify ρ u x ^ 2)) :
    (∫ x, mollify ρ u x ^ 2) ≤ (∫ t, |ρ t|) ^ 2 * ∫ x, u x ^ 2 := by
  rw [mollify_eq_lineConvolution] at hconv ⊢
  exact integral_sq_lineConvolution_le hρm hum hρi hu2 hconv

/-- **Mollification by a probability density is an `L²` contraction.** -/
theorem integral_sq_mollify_le_of_isProbabilityDensity {ρ u : ℝ → ℝ}
    (hρm : Measurable ρ) (hum : Measurable u)
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρi : Integrable ρ) (hρ1 : (∫ t, ρ t) = 1)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hconv : Integrable (fun x => mollify ρ u x ^ 2)) :
    (∫ x, mollify ρ u x ^ 2) ≤ ∫ x, u x ^ 2 := by
  have habs : (fun t => |ρ t|) = ρ := by
    funext t
    exact abs_of_nonneg (hρ0 t)
  have hρi' : Integrable (fun t => |ρ t|) := by rw [habs]; exact hρi
  have hmass : (∫ t, |ρ t|) = 1 := by rw [habs]; exact hρ1
  have h := integral_sq_mollify_le hρm hum hρi' hu2 hconv
  rw [hmass, one_pow, one_mul] at h
  exact h

end GaloisForLFunctions.HTGeometry
