import GaloisForLFunctions.BiScaleUncertainty.DivisorComponentCharge
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCellAveraging

/-!
# Explicit arithmetic projection of every physical velocity

Cell integration followed by finite-component mean subtraction constructs the
unique nearest completed divisor state. The exact error separates noncellular
variation from a convergent arithmetic component charge. The negative half-line
and the first inactive cell are accounted for explicitly.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorPhysicalData (d : ℕ) (D : Set ℕ) (q : Velocity) : DivisorEnergyData d D :=
  divisorCenteredData d D (unitCellAnalysis q)

def divisorPhysicalProjection (d : ℕ) (D : Set ℕ) : Velocity →L[ℝ] Velocity :=
  unitCellSynthesis.toContinuousLinearMap ∘L
    ((divisorCellSpace d D).starProjection ∘L unitCellAnalysis)

theorem divisorPhysicalProjection_apply (d : ℕ) (D : Set ℕ) (q : Velocity) :
    divisorPhysicalProjection d D q = divisorEnergyExtension d D (divisorPhysicalData d D q) := by
  change unitCellSynthesis ((divisorCellSpace d D).starProjection (unitCellAnalysis q)) =
    unitCellSynthesis (divisorCenteredData d D (unitCellAnalysis q)).1
  rw [divisorCenteredData_eq_projection]

theorem divisorPhysicalProjection_coefficients (d : ℕ) (D : Set ℕ) (q : Velocity) :
    unitCellAnalysis (divisorPhysicalProjection d D q) = (divisorPhysicalData d D q).1 := by
  rw [divisorPhysicalProjection_apply, divisorEnergyExtension_apply, unitCellAnalysis_synthesis]

theorem divisorPhysicalProjection_cell (d : ℕ) (D : Set ℕ) (q : Velocity) (k : ℕ) :
    unitCellAnalysis (divisorPhysicalProjection d D q) k =
      unitCellAnalysis q k - divisorComponentMean d D (unitCellAnalysis q) k := by
  rw [divisorPhysicalProjection_coefficients]
  exact divisorCenteredData_apply d D (unitCellAnalysis q) k

theorem primitive_divisorPhysicalProjection (d : ℕ) (D : Set ℕ) (q : Velocity) (n : ℕ) :
    primitive (divisorPhysicalProjection d D q) n =
      cellPrefixL n (divisorPhysicalData d D q).1 := by
  rw [divisorPhysicalProjection_apply, primitive_divisorEnergyExtension]

theorem log_divisorPhysicalProjection (d : ℕ) (D : Set ℕ) (q : Velocity) (k : ℕ) :
    logPrimitive (divisorPhysicalProjection d D q) (Real.log ((k : ℝ)+1)) =
      cellPrefixL (k+1) (divisorPhysicalData d D q).1 := by
  rw [divisorPhysicalProjection_apply, log_divisorEnergyExtension]

theorem divisorPhysicalProjection_first_cell (d : ℕ) (D : Set ℕ) (q : Velocity) :
    unitCellAnalysis (divisorPhysicalProjection d D q) 0 = 0 := by
  rw [divisorPhysicalProjection_coefficients]
  have h := (divisorPhysicalData d D q).2 0 (not_divisorGridActive_zero d D)
  simpa only [cellPrefixL_succ, cellPrefixL_zero, zero_add] using h

theorem divisorPhysicalProjection_first_trace (d : ℕ) (D : Set ℕ) (q : Velocity) :
    primitive (divisorPhysicalProjection d D q) 1 = 0 := by
  have h := divisorPhysicalProjection_first_cell d D q
  simpa only [unitCellAnalysis_apply, Nat.cast_zero, zero_add, primitive,
    intervalIntegral.integral_same, sub_zero] using h

theorem divisorPhysicalProjection_extension (d : ℕ) (D : Set ℕ) (v : DivisorEnergyData d D) :
    divisorPhysicalProjection d D (divisorEnergyExtension d D v) = divisorEnergyExtension d D v := by
  change unitCellSynthesis ((divisorCellSpace d D).starProjection
    (unitCellAnalysis (unitCellSynthesis v.1))) = unitCellSynthesis v.1
  rw [unitCellAnalysis_synthesis, Submodule.starProjection_mem_subspace_eq_self v]

theorem divisorPhysicalProjection_idempotent (d : ℕ) (D : Set ℕ) (q : Velocity) :
    divisorPhysicalProjection d D (divisorPhysicalProjection d D q) =
      divisorPhysicalProjection d D q := by
  rw [divisorPhysicalProjection_apply d D q, divisorPhysicalProjection_extension]

theorem range_divisorPhysicalProjection (d : ℕ) (D : Set ℕ) :
    Set.range (divisorPhysicalProjection d D) = closure (Set.range (divisorGridExtension d D)) := by
  rw [closure_range_divisorGridExtension]
  ext q
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨divisorPhysicalData d D q, (divisorPhysicalProjection_apply d D q).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨divisorEnergyExtension d D v, divisorPhysicalProjection_extension d D v⟩

theorem inner_divisorPhysicalProjection_residual (d : ℕ) (D : Set ℕ)
    (v : DivisorEnergyData d D) (q : Velocity) :
    ⟪divisorEnergyExtension d D v, q-divisorPhysicalProjection d D q⟫ = 0 := by
  rw [inner_sub_right]
  change ⟪unitCellSynthesis v.1, q⟫ - ⟪unitCellSynthesis v.1,
    unitCellSynthesis ((divisorCellSpace d D).starProjection (unitCellAnalysis q))⟫ = 0
  rw [inner_unitCellSynthesis_analysis, unitCellSynthesis.inner_map_map]
  have h := (Submodule.mem_orthogonal _ _).mp
    (Submodule.sub_starProjection_mem_orthogonal (K := divisorCellSpace d D) (unitCellAnalysis q))
    v.1 v.2
  simpa only [inner_sub_right] using h

/-- Exact competitor defect for every completed datum, without a run bound. -/
theorem divisorPhysicalProjection_best (d : ℕ) (D : Set ℕ) (q : Velocity)
    (v : DivisorEnergyData d D) :
    ‖q-divisorEnergyExtension d D v‖^2 = ‖q-divisorPhysicalProjection d D q‖^2 +
      ‖divisorPhysicalData d D q-v‖^2 := by
  have hl : divisorEnergyExtension d D (divisorPhysicalData d D q-v) =
      divisorPhysicalProjection d D q-divisorEnergyExtension d D v := by
    rw [map_sub, ← divisorPhysicalProjection_apply]
  have ho := inner_divisorPhysicalProjection_residual d D (divisorPhysicalData d D q-v) q
  rw [hl] at ho
  have he : q-divisorEnergyExtension d D v = (q-divisorPhysicalProjection d D q) +
      (divisorPhysicalProjection d D q-divisorEnergyExtension d D v) := by abel
  rw [he, norm_add_sq_real, real_inner_comm, ho, ← hl, (divisorEnergyExtension d D).norm_map]
  ring

theorem divisorPhysicalProjection_minimum (d : ℕ) (D : Set ℕ) (q : Velocity)
    (v : DivisorEnergyData d D) :
    ‖q-divisorPhysicalProjection d D q‖^2 ≤ ‖q-divisorEnergyExtension d D v‖^2 := by
  rw [divisorPhysicalProjection_best]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem divisorPhysicalProjection_unique (d : ℕ) (D : Set ℕ) (q : Velocity)
    (v : DivisorEnergyData d D) :
    ‖q-divisorEnergyExtension d D v‖^2 = ‖q-divisorPhysicalProjection d D q‖^2 ↔
      v = divisorPhysicalData d D q := by
  rw [divisorPhysicalProjection_best]
  constructor
  · intro h
    have hz : ‖divisorPhysicalData d D q-v‖^2 = 0 := by linarith only [h]
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  · rintro rfl
    simp

def divisorPhysicalCharge (d : ℕ) (D : Set ℕ) (q : Velocity) (j : ℕ) : ℝ :=
  if divisorGridActive d D j then 0 else
    (primitive q ((j+1 : ℕ) : ℝ)-primitive q (divisorCellStart d D j))^2 /
      (divisorComponentLength d D j : ℝ)

theorem divisorPhysicalCharge_eq (d : ℕ) (D : Set ℕ) (q : Velocity) (j : ℕ) :
    divisorPhysicalCharge d D q j = divisorComponentCharge d D (unitCellAnalysis q) j := by
  unfold divisorPhysicalCharge divisorComponentCharge
  by_cases h : divisorGridActive d D j
  · simp only [if_pos h]
  · simp only [if_neg h]
    rw [cellPrefixL_interval _ _ (by have := divisorCellStart_le d D j; omega),
      cellPrefixL_unitCellAnalysis, cellPrefixL_unitCellAnalysis]

theorem hasSum_divisorPhysicalCharge (d : ℕ) (D : Set ℕ) (q : Velocity) :
    HasSum (divisorPhysicalCharge d D q) (‖divisorMeanCurrent d D (unitCellAnalysis q)‖^2) :=
  (hasSum_divisorComponentCharge d D (unitCellAnalysis q)).congr_fun
    (divisorPhysicalCharge_eq d D q)

theorem divisorPhysicalProjection_cellular_difference (d : ℕ) (D : Set ℕ) (q : Velocity) :
    cellularProjection q-divisorPhysicalProjection d D q =
      unitCellSynthesis (divisorMeanCurrent d D (unitCellAnalysis q)) := by
  rw [divisorPhysicalProjection_apply, divisorEnergyExtension_apply, cellularProjection_apply]
  change unitCellSynthesis (unitCellAnalysis q) -
    unitCellSynthesis (unitCellAnalysis q-divisorMeanCurrent d D (unitCellAnalysis q)) = _
  rw [← map_sub]
  congr 1
  abel

/-- Every arithmetic charge is instantiated by a physical component integral. -/
theorem divisorPhysicalProjection_error (d : ℕ) (D : Set ℕ) (q : Velocity) :
    ‖q-divisorPhysicalProjection d D q‖^2 = ‖q-cellularProjection q‖^2 +
      ∑' j, divisorPhysicalCharge d D q j := by
  have he : q-divisorPhysicalProjection d D q = (q-cellularProjection q) +
      unitCellSynthesis (divisorMeanCurrent d D (unitCellAnalysis q)) := by
    rw [← divisorPhysicalProjection_cellular_difference]
    abel
  have ho := inner_cellular_residual (divisorMeanCurrent d D (unitCellAnalysis q)) q
  rw [he, norm_add_sq_real, real_inner_comm, ho, unitCellSynthesis.norm_map,
    (hasSum_divisorPhysicalCharge d D q).tsum_eq]
  ring

theorem divisorPhysicalProjection_energy (d : ℕ) (D : Set ℕ) (q : Velocity) :
    ‖divisorPhysicalProjection d D q‖^2 + ‖q-divisorPhysicalProjection d D q‖^2 = ‖q‖^2 := by
  have hi := inner_divisorPhysicalProjection_residual d D (divisorPhysicalData d D q) q
  rw [← divisorPhysicalProjection_apply, inner_sub_right, real_inner_self_eq_norm_sq] at hi
  rw [norm_sub_sq_real, real_inner_comm, sub_eq_zero.mp hi]
  ring

theorem divisorPhysicalProjection_energy_le (d : ℕ) (D : Set ℕ) (q : Velocity) :
    ‖divisorPhysicalProjection d D q‖^2 ≤ ‖q‖^2 := by
  have h := divisorPhysicalProjection_energy d D q
  linarith only [h, sq_nonneg ‖q-divisorPhysicalProjection d D q‖]

theorem divisorPhysicalProjection_negative (d : ℕ) (D : Set ℕ) (q : Velocity) :
    divisorPhysicalProjection d D (negativePhysicalVelocity q) = 0 := by
  change unitCellSynthesis ((divisorCellSpace d D).starProjection
    (unitCellAnalysis (negativePhysicalVelocity q))) = 0
  rw [unitCellAnalysis_negative, map_zero, map_zero]

/-- Exact three-part error, including the entire negative physical half-line. -/
theorem divisorPhysicalProjection_error_negative_split (d : ℕ) (D : Set ℕ) (q : Velocity) :
    ‖q-divisorPhysicalProjection d D q‖^2 = (∫ t in Iic (0 : ℝ), (q t)^2) +
      ‖q-negativePhysicalVelocity q-cellularProjection q‖^2 +
      ∑' j, divisorPhysicalCharge d D q j := by
  rw [divisorPhysicalProjection_error, cellular_residual_negative_split,
    norm_sq_negativePhysicalVelocity]

theorem divisorMeanCurrent_univ (d : ℕ) (w : TraceData) :
    divisorMeanCurrent d Set.univ w = lp.single 2 0 (w 0) := by
  apply lp.ext
  funext k
  cases k with
  | zero =>
      simp [divisorMeanCurrent_apply, divisorComponentMean, divisorCellHasEnd_univ_iff,
        divisorCellEnd_zero, divisorEndpointMean, divisorComponentLength, divisorCellStart,
        lp.single_apply]
  | succ k =>
      simp [divisorMeanCurrent_apply, divisorComponentMean, divisorCellHasEnd_univ_iff,
        lp.single_apply]

theorem divisorPhysicalProjection_univ (d : ℕ) (q : Velocity) :
    divisorPhysicalProjection d Set.univ q =
      cellularProjection q - (unitCellAnalysis q 0) • unitCell 0 := by
  rw [divisorPhysicalProjection_apply, divisorEnergyExtension_apply]
  change unitCellSynthesis (unitCellAnalysis q-divisorMeanCurrent d Set.univ (unitCellAnalysis q)) = _
  rw [divisorMeanCurrent_univ, map_sub, unitCellSynthesis_single, ← cellularProjection_apply]

theorem divisorPhysicalProjection_univ_error (d : ℕ) (q : Velocity) :
    ‖q-divisorPhysicalProjection d Set.univ q‖^2 =
      ‖q-cellularProjection q‖^2 + (unitCellAnalysis q 0)^2 := by
  rw [divisorPhysicalProjection_error, (hasSum_divisorPhysicalCharge d Set.univ q).tsum_eq,
    divisorMeanCurrent_univ]
  simp [Real.norm_eq_abs, sq_abs]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
