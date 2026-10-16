import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Bochner integration preserves a closed positive cone -/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

theorem integral_mem_properCone {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : ProperCone ℝ E) {μ : Measure α} {f : α → E}
    (hf : Integrable f μ) (hmem : ∀ᵐ x ∂μ, f x ∈ C) :
    (∫ x, f x ∂μ) ∈ C := by
  by_contra hn
  obtain ⟨L, hL, hneg⟩ := C.hyperplane_separation_point hn
  rw [← L.integral_comp_comm hf] at hneg
  exact (not_lt_of_ge (integral_nonneg_of_ae
    (hmem.mono fun x hx => hL (f x) hx))) hneg

end GaloisForLFunctions.HTGeometry
