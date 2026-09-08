import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence

/-!
# Elementary strict order-zero/order-one Schlaefli comparison

The original integral proof, extracted from the cyclic-determinant development
with its theorem name unchanged. No meromorphic field is needed for this inequality.
-/

open Filter MeasureTheory Set Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Strict order-zero/order-one comparison, directly from the Schlaefli integral. -/
theorem realModifiedBesselKOrder_zero_lt_one {s : ℝ} (hs : 0 < s) :
    realModifiedBesselKOrder s 0 < realModifiedBesselKOrder s 1 := by
  let f : ℝ → ℝ := fun t =>
    realBesselOrderKernel s 1 t - realBesselOrderKernel s 0 t
  have h1 := integrableOn_realBesselOrderKernel hs 1
  have h0 := integrableOn_realBesselOrderKernel hs 0
  have hfint : IntegrableOn f (Ioi 0) := h1.sub h0
  have hfnonneg : ∀ t, 0 ≤ f t := by
    intro t
    simp only [f, realBesselOrderKernel, one_mul, zero_mul, Real.cosh_zero]
    exact sub_nonneg.mpr
      (mul_le_mul_of_nonneg_left (Real.one_le_cosh t) (Real.exp_pos _).le)
  have hfpos : ∀ t ∈ Ioi (0 : ℝ), 0 < f t := by
    intro t ht
    simp only [f, realBesselOrderKernel, one_mul, zero_mul, Real.cosh_zero]
    exact sub_pos.mpr
      (mul_lt_mul_of_pos_left ((Real.one_lt_cosh).2 (ne_of_gt ht)) (Real.exp_pos _))
  rw [realModifiedBesselKOrder, realModifiedBesselKOrder]
  apply sub_pos.mp
  rw [← MeasureTheory.integral_sub h1 h0]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall hfnonneg) hfint).2
  have hsupp : Function.support f ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨(hfpos t ht).ne', ht⟩
  rw [hsupp]
  simp

end
end GaloisForLFunctions.HTGeometry
