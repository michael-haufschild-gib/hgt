import GaloisForLFunctions.HTGeometry.QuasiMeasure
import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# Integration against the quadrature measure

The quadrature measure is a finite weighted Dirac family, so every function integrates against it to
the weighted sum of its values — for vector-valued functions as much as real ones, and with no
measurability hypothesis, since a Dirac measure integrates everything.  Applied to
the Cauchy kernel this identifies the level-`n` Cauchy transform with the finite sum appearing in the
Nevanlinna identity.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Vector-valued integration against a finite weighted Dirac family.** -/
theorem integral_finsetWeightedDirac_vector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (t : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ x ∈ t, 0 ≤ w x)
    (f : ℝ → E) :
    ∫ x, f x ∂(∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y) = ∑ y ∈ t, w y • f y := by
  classical
  have hint : ∀ y ∈ t, Integrable f (ENNReal.ofReal (w y) • Measure.dirac y) := by
    intro y _
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw y hy)]

/-- **The level-`n` Cauchy transform is the finite weighted sum over the nodes.** -/
theorem integral_cauchy_quasiMeasure (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (z : ℂ) :
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(quasiMeasure s n t)
      = ∑ ξ ∈ quasiNodes s n t,
          ((quasiWeight s n t ξ : ℝ) : ℂ) * (((ξ : ℝ) : ℂ) - z)⁻¹ := by
  rw [quasiMeasure, integral_finsetWeightedDirac_vector _ _
    (fun ξ hξ => (quasiWeight_pos h n t hξ).le) _]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Complex.real_smul]

end HTGeometry
