import GaloisForLFunctions.RHTower.FokasLenellsCausalComplexResolvent
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryEigenvectors

/-! Exact complex resolvent action and sharp norm for the completed causal generator. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual complex resolvent acts on every rational eigenvector by reciprocal spectral distance. -/
theorem causalComplexResolvent_leftEigenvector (z : {z : ℂ // 0 < z.re})
    (w : {w : ℂ // w.re < 0}) :
    causalComplexResolvent z (causalLeftEigenvector w).val =
      (z.val-w.val)⁻¹ • causalLeftEigenvector w := by
  have hne : z.val-w.val ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at hre
    have hz := z.property
    have hw := w.property
    linarith
  apply causalComplexGeneratorShift_injective z
  rw [causalComplexGeneratorShift_resolvent, map_smul]
  change (causalLeftEigenvector w).val = (z.val-w.val)⁻¹ •
    (z.val • (causalLeftEigenvector w).val - causalGenerator (causalLeftEigenvector w))
  rw [causalGenerator_leftEigenvector, ← sub_smul, inv_smul_smul₀ hne]

/-- The reciprocal spectral distance is realized exactly on each actual rational eigenvector. -/
theorem norm_causalComplexResolvent_leftEigenvector (z : {z : ℂ // 0 < z.re})
    (w : {w : ℂ // w.re < 0}) :
    ‖causalComplexResolvent z (causalLeftEigenvector w).val‖ =
      ‖z.val-w.val‖⁻¹ * ‖causalLeftEigenvector w‖ := by
  rw [causalComplexResolvent_leftEigenvector, norm_smul, norm_inv]

/-- The actual complex resolvent norm is precisely reciprocal real damping at every point. -/
theorem norm_causalComplexResolvent (z : {z : ℂ // 0 < z.re}) :
    ‖causalComplexResolvent z‖ = z.val.re⁻¹ := by
  apply le_antisymm (norm_causalComplexResolvent_le z)
  have hb (b : ℝ) : (z.val.re+Real.exp b)⁻¹ ≤ ‖causalComplexResolvent z‖ := by
    let w := causalBoundaryRate b z.val.im
    have he0 : z.val-w.val = ((z.val.re+Real.exp b : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [w, causalBoundaryRate]
    have he : ‖z.val-w.val‖ = z.val.re+Real.exp b := by
      rw [he0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (add_pos z.property (Real.exp_pos b))]
    have h := (causalComplexResolvent z).le_opNorm (causalLeftEigenvector w).val
    rw [norm_causalComplexResolvent_leftEigenvector, he] at h
    have hn := norm_pos_iff.mpr (causalLeftEigenvector_ne_zero w)
    change (z.val.re+Real.exp b)⁻¹ * ‖causalLeftEigenvector w‖ ≤
      ‖causalComplexResolvent z‖ * ‖causalLeftEigenvector w‖ at h
    exact (mul_le_mul_iff_of_pos_right hn).mp h
  have ht0 : Tendsto (fun b : ℝ => z.val.re+Real.exp b) atBot (𝓝 z.val.re) := by
    simpa only [add_zero] using tendsto_const_nhds.add Real.tendsto_exp_atBot
  exact le_of_tendsto (ht0.inv₀ z.property.ne') (Eventually.of_forall hb)

/-- Changing the spectral parameter obeys the exact resolvent identity on the actual domain. -/
theorem causalComplexResolvent_identity (z w : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    causalComplexResolvent z u - causalComplexResolvent w u =
      (w.val-z.val) • causalComplexResolvent z (causalComplexResolvent w u).val := by
  apply causalComplexGeneratorShift_injective z
  rw [map_sub, map_smul, causalComplexGeneratorShift_resolvent,
    causalComplexGeneratorShift_resolvent]
  change u - (z.val • (causalComplexResolvent w u).val -
    causalGenerator (causalComplexResolvent w u)) = _
  rw [causalGenerator_complexResolvent]
  module

end
end RHTower.FokasLenells
