import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.CutoffGramKernel
import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture
import GaloisForLFunctions.RHTower.UnitaryResolventOffCircle

/-!
# Unitary dilation of the cutoff cusp model

Cusp cutoffs are genuine square-integrable vectors. Normalized dilation moves
the cutoff and multiplies by the corresponding complex power. Factoring a
unitary plus its inverse gives a frequency-independent residual gap.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- The elementary cusp cutoff defines an actual `L²` vector. -/
theorem cuspCutoff_memLp {u : ℂ} (hu : u.re < 0) {Y : ℝ} (hY : 0 ≤ Y) :
    MemLp (cuspCutoff u Y) 2 volume := by
  have hm : Measurable (cuspCutoff u Y) :=
    Measurable.ite measurableSet_Ioc
      (measurable_const.mul (Complex.measurable_ofReal.pow_const _)) measurable_const
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := (integrable_cusp_product hu hu hY hY).norm
  exact hi.congr (Eventually.of_forall fun y => by simp only [norm_mul, norm_conj, pow_two])

/-- Normalized dilation acts on a cusp cutoff by a height shift. -/
theorem cuspCutoff_dilation (u : ℂ) (Y : ℝ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    (Real.sqrt r : ℂ) * cuspCutoff u Y (r * y) =
      (r : ℂ) ^ (-u) * cuspCutoff u (Y / r) y := by
  have hm : r * y ∈ Ioc 0 Y ↔ y ∈ Ioc 0 (Y / r) := by
    simp only [mem_Ioc, mul_pos_iff_of_pos_left hr, le_div_iff₀ hr]
    rw [mul_comm y r]
  by_cases hy : y ∈ Ioc 0 (Y / r)
  · rw [cuspCutoff, cuspCutoff, if_pos (hm.mpr hy), if_pos hy]
    have hs : (Real.sqrt r : ℂ) = (r : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
      norm_num
    have hp := Complex.mul_cpow_ofReal_nonneg hr.le hy.1.le (-u - 1 / 2)
    rw [Complex.ofReal_mul, hp, hs]
    have he : (r : ℂ) ^ (1 / 2 : ℂ) * (r : ℂ) ^ (-u - 1 / 2) = (r : ℂ) ^ (-u) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
      congr 1
      ring
    calc
      _ = ((r : ℂ) ^ (1 / 2 : ℂ) * (r : ℂ) ^ (-u - 1 / 2)) *
          (msB u * (y : ℂ) ^ (-u - 1 / 2)) := by ring
      _ = _ := by rw [he]
  · simp only [cuspCutoff, if_neg hy, if_neg (fun h => hy (hm.mp h)), mul_zero]

/-- A unitary plus its inverse cannot approach its off-circle spectral parameter.
The bound follows by factoring into two unitary-minus-scalar factors. -/
theorem unitary_pair_gap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) {q : ℂ} (hq : q ≠ 0) (f : H) :
    (‖q‖ + ‖q‖⁻¹ - 2) * ‖f‖ ≤ ‖U f + U.symm f - (q + q⁻¹) • f‖ := by
  let g := U.symm f - q • f
  let R := U f + U.symm f - (q + q⁻¹) • f
  have he : U g - q • g = -q • R := by
    dsimp [g, R]
    simp only [map_sub, map_smul, LinearIsometryEquiv.apply_symm_apply,
      smul_sub, smul_add, smul_smul, neg_mul, mul_add, mul_inv_cancel₀ hq,
      neg_smul, one_smul, add_smul]
    module
  have h₁ := norm_sub_smul_lower_bound U q g
  have h₂ := norm_sub_smul_lower_bound U.symm q f
  change |‖q‖ - 1| * ‖g‖ ≤ ‖U g - q • g‖ at h₁
  change |‖q‖ - 1| * ‖f‖ ≤ ‖g‖ at h₂
  rw [he, norm_smul, norm_neg] at h₁
  have hmul := mul_le_mul_of_nonneg_left h₂ (abs_nonneg (‖q‖ - 1))
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hid : ‖q‖ * (‖q‖ + ‖q‖⁻¹ - 2) = |‖q‖ - 1| ^ 2 := by
    rw [sq_abs]
    field_simp
    ring
  apply (mul_le_mul_left hr).mp
  calc
    ‖q‖ * ((‖q‖ + ‖q‖⁻¹ - 2) * ‖f‖) = |‖q‖ - 1| * (|‖q‖ - 1| * ‖f‖) := by
      rw [← mul_assoc, hid]
      ring
    _ ≤ ‖q‖ * ‖R‖ := hmul.trans h₁

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
