import GaloisForLFunctions.BiScaleUncertainty.SuccessorSequenceHilbert
import GaloisForLFunctions.BiScaleUncertainty.SobolevLogarithmicTransport

/-!
# Infinite integer-hat interpolation

Unit-cell synthesis applied to the discrete gradient gives the actual physical
L² extension of every square-summable positive-integer trace sequence. The
adjacent energy and competitor identity retain every trace mismatch explicitly.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem orthonormal_unitCell : Orthonormal ℝ unitCell := by
  rw [orthonormal_iff_ite]
  exact inner_unitCell

def unitCellSynthesis : TraceData →ₗᵢ[ℝ] Velocity :=
  orthonormal_unitCell.orthogonalFamily.linearIsometry

theorem unitCellSynthesis_single (k : ℕ) (a : ℝ) :
    unitCellSynthesis (lp.single 2 k a) = a • unitCell k :=
  orthonormal_unitCell.orthogonalFamily.linearIsometry_apply_single a

def integerHat (k : ℕ) : Velocity := unitCell k - unitCell (k + 1)

def integerExtension : TraceData →L[ℝ] Velocity :=
  unitCellSynthesis.toContinuousLinearMap ∘L
    (ContinuousLinearMap.id ℝ TraceData - (sequenceRightShift ℝ).toContinuousLinearMap)

theorem integerExtension_apply (v : TraceData) :
    integerExtension v = unitCellSynthesis (v - sequenceRightShift ℝ v) := rfl

theorem integerExtension_single (k : ℕ) (a : ℝ) :
    integerExtension (lp.single 2 k a) = a • integerHat k := by
  rw [integerExtension_apply, sequenceRightShift_single, map_sub,
    unitCellSynthesis_single, unitCellSynthesis_single, integerHat, smul_sub]

theorem hasSum_integerExtension (v : TraceData) :
    HasSum (fun k => v k • integerHat k) (integerExtension v) := by
  have h := integerExtension.hasSum (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) v)
  simpa only [integerExtension_single] using h

theorem inner_prefixCell_integerHat (n k : ℕ) :
    ⟪prefixCell n, integerHat k⟫ = if n = k + 1 then 1 else 0 := by
  simp only [integerHat, inner_sub_right, inner_prefixCell_unitCell]
  split_ifs <;> first | omega | norm_num

theorem primitive_integerExtension_succ (n : ℕ) (v : TraceData) :
    primitive (integerExtension v) (n + 1) = v n := by
  have h := (innerSL ℝ (prefixCell (n + 1))).hasSum (hasSum_integerExtension v)
  simp only [innerSL_apply_apply, real_inner_smul_right, inner_prefixCell_integerHat,
    Nat.add_right_cancel_iff, mul_ite, mul_one, mul_zero] at h
  rw [inner_prefixCell] at h
  have ht := h.tsum_eq.symm
  simpa using ht

theorem log_integerExtension (n : ℕ) (v : TraceData) :
    logPrimitive (integerExtension v) (Real.log ((n : ℝ) + 1)) = v n := by
  rw [logPrimitive, Real.exp_log (by positivity), primitive_integerExtension_succ]

theorem hasSum_adjacentTraceProduct (v : TraceData) :
    HasSum (fun k => v k * v (k + 1)) ⟪v, sequenceRightShift ℝ v⟫ := by
  have h := lp.hasSum_inner (𝕜 := ℝ) (sequenceLeftShift ℝ v) v
  have hi := (sequenceRightShift ℝ).toContinuousLinearMap.adjoint_inner_left v v
  change ⟪sequenceLeftShift ℝ v, v⟫ = ⟪v, sequenceRightShift ℝ v⟫ at hi
  rw [hi] at h
  simpa [sequenceLeftShift_apply, mul_comm] using h

theorem integerExtension_energy (v : TraceData) :
    ‖integerExtension v‖ ^ 2 = 2 * ‖v‖ ^ 2 - 2 * ∑' k, v k * v (k + 1) := by
  rw [integerExtension_apply, unitCellSynthesis.norm_map, norm_sub_sq_real,
    (sequenceRightShift ℝ).norm_map, (hasSum_adjacentTraceProduct v).tsum_eq]
  ring

def integerTraceCurvature (q : Velocity) (k : ℕ) : ℝ :=
  2 * primitive q ((k : ℝ) + 1) - primitive q k - primitive q ((k : ℝ) + 2)

theorem inner_integerHat_velocity (k : ℕ) (q : Velocity) :
    ⟪integerHat k, q⟫ = integerTraceCurvature q k := by
  simp only [integerHat, inner_sub_left, inner_unitCell_velocity, Nat.cast_add,
    Nat.cast_one, integerTraceCurvature]
  rw [show (k : ℝ) + 1 + 1 = k + 2 by ring]
  ring

theorem hasSum_integerExtension_curvature (v : TraceData) (q : Velocity) :
    HasSum (fun k => v k * integerTraceCurvature q k) ⟪integerExtension v, q⟫ := by
  have h := (innerSL ℝ q).hasSum (hasSum_integerExtension v)
  have he (k : ℕ) : ⟪q, v k • integerHat k⟫ = v k * integerTraceCurvature q k := by
    rw [real_inner_smul_right, real_inner_comm, inner_integerHat_velocity]
  simpa only [innerSL_apply_apply, he, real_inner_comm] using h

theorem integerExtension_competitor_energy (v : TraceData) (q : Velocity) :
    ‖q‖ ^ 2 = ‖integerExtension v‖ ^ 2 + ‖q - integerExtension v‖ ^ 2 +
      2 * ∑' k, v k * integerTraceCurvature (q - integerExtension v) k := by
  rw [(hasSum_integerExtension_curvature v _).tsum_eq]
  have h := norm_add_sq_real (integerExtension v) (q - integerExtension v)
  have he : integerExtension v + (q - integerExtension v) = q := by abel
  rw [he] at h
  linarith only [h]

theorem integerExtension_minimum_energy_defect (v : TraceData) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (integerExtension v) k) :
    ‖q‖ ^ 2 = ‖integerExtension v‖ ^ 2 + ‖q - integerExtension v‖ ^ 2 := by
  have hz (k : ℕ) : primitive (q - integerExtension v) k = 0 := by
    rw [← inner_prefixCell, inner_sub_right, inner_prefixCell, inner_prefixCell, h, sub_self]
  have hc (k : ℕ) : integerTraceCurvature (q - integerExtension v) k = 0 := by
    unfold integerTraceCurvature
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_cast,
      show (k : ℝ) + 2 = ((k + 2 : ℕ) : ℝ) by norm_cast, hz, hz, hz]
    ring
  rw [integerExtension_competitor_energy v q]
  simp only [hc, mul_zero, tsum_zero, add_zero]

theorem integerExtension_minimum_energy (v : TraceData) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (integerExtension v) k) :
    ‖integerExtension v‖ ^ 2 ≤ ‖q‖ ^ 2 := by
  rw [integerExtension_minimum_energy_defect v q h]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem integerExtension_minimum_energy_eq_iff (v : TraceData) (q : Velocity)
    (h : ∀ k : ℕ, primitive q k = primitive (integerExtension v) k) :
    ‖q‖ ^ 2 = ‖integerExtension v‖ ^ 2 ↔ q = integerExtension v := by
  rw [integerExtension_minimum_energy_defect v q h]
  simp only [add_eq_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
