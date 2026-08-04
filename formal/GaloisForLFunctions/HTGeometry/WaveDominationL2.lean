import GaloisForLFunctions.HTGeometry.WaveDecayingL2

/-!
# Domination by a product of square-integrable functions

The last hypothesis of the square-integrable uniqueness theorem that is not itself an `L²`
statement is the local dominating function for the time derivative of the energy density. That
derivative is a sum of products of two factors, so a dominating function for it can be assembled
from square-integrable dominating functions for the factors: the product of two square-integrable
functions is integrable, and domination transfers.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

section Domination

variable {d : ℕ}

/-- **A function dominated by a product of two square-integrable functions is integrable.** -/
theorem integrable_of_dominated_by_memLp_two {f g₁ g₂ : (Fin d → ℝ) → ℝ}
    (hg₁ : MemLp g₁ 2 (volume : Measure (Fin d → ℝ)))
    (hg₂ : MemLp g₂ 2 (volume : Measure (Fin d → ℝ)))
    (hmeas : AEStronglyMeasurable f (volume : Measure (Fin d → ℝ)))
    (hf : ∀ x : Fin d → ℝ, ‖f x‖ ≤ g₁ x * g₂ x) :
    Integrable f (volume : Measure (Fin d → ℝ)) := by
  have hprod : Integrable (fun x : Fin d → ℝ => g₁ x * g₂ x)
      (volume : Measure (Fin d → ℝ)) := MemLp.integrable_mul hg₁ hg₂
  exact Integrable.mono' hprod hmeas (Filter.Eventually.of_forall hf)

/-- The same with the dominating product written as a sum of products, which is the shape the time
derivative of the energy density has. -/
theorem integrable_of_dominated_by_sum_memLp_two {ι : Type*} (s : Finset ι)
    {f : (Fin d → ℝ) → ℝ} {g₁ g₂ : ι → (Fin d → ℝ) → ℝ}
    (hg₁ : ∀ i ∈ s, MemLp (g₁ i) 2 (volume : Measure (Fin d → ℝ)))
    (hg₂ : ∀ i ∈ s, MemLp (g₂ i) 2 (volume : Measure (Fin d → ℝ)))
    (hmeas : AEStronglyMeasurable f (volume : Measure (Fin d → ℝ)))
    (hf : ∀ x : Fin d → ℝ, ‖f x‖ ≤ ∑ i ∈ s, g₁ i x * g₂ i x) :
    Integrable f (volume : Measure (Fin d → ℝ)) := by
  have hprod : Integrable (fun x : Fin d → ℝ => ∑ i ∈ s, g₁ i x * g₂ i x)
      (volume : Measure (Fin d → ℝ)) :=
    integrable_finsetSum _ fun i hi => MemLp.integrable_mul (hg₁ i hi) (hg₂ i hi)
  exact Integrable.mono' hprod hmeas (Filter.Eventually.of_forall hf)

end Domination

end GaloisForLFunctions.HTGeometry
