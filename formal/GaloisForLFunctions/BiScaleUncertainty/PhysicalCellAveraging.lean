import GaloisForLFunctions.BiScaleUncertainty.CellPrefixHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Actual physical cell averages and the negative half-line

The adjoint of unit-cell synthesis constructs square-summable physical cell
integrals. Its residual is orthogonal to every cellular velocity. Measurable
truncation separates the exact negative-half-line contribution to this error.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def unitCellAnalysis : Velocity →L[ℝ] TraceData :=
  unitCellSynthesis.toContinuousLinearMap.adjoint

theorem inner_unitCellSynthesis_analysis (w : TraceData) (q : Velocity) :
    ⟪unitCellSynthesis w, q⟫ = ⟪w, unitCellAnalysis q⟫ :=
  (unitCellSynthesis.toContinuousLinearMap.adjoint_inner_right w q).symm

theorem unitCellAnalysis_inner (q : Velocity) (k : ℕ) :
    unitCellAnalysis q k = ⟪unitCell k, q⟫ := by
  have h := unitCellSynthesis.toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 k (1 : ℝ)) q
  change ⟪lp.single 2 k (1 : ℝ), unitCellAnalysis q⟫ =
    ⟪unitCellSynthesis (lp.single 2 k 1), q⟫ at h
  simpa only [lp.inner_single_left, Real.inner_apply, one_mul,
    unitCellSynthesis_single, one_smul] using h

theorem unitCellAnalysis_apply (q : Velocity) (k : ℕ) :
    unitCellAnalysis q k = primitive q (k+1) - primitive q k := by
  rw [unitCellAnalysis_inner, inner_unitCell_velocity]

theorem unitCellAnalysis_integral (q : Velocity) (k : ℕ) :
    unitCellAnalysis q k = ∫ t in Ioc (k : ℝ) (k+1), q t := by
  rw [unitCellAnalysis_inner, unitCell, L2.inner_indicatorConstLp_one]

theorem unitCellAnalysis_synthesis (w : TraceData) :
    unitCellAnalysis (unitCellSynthesis w) = w :=
  congrArg (fun A : TraceData →L[ℝ] TraceData => A w) unitCellSynthesis.adjoint_comp_self

theorem cellPrefixL_unitCellAnalysis (q : Velocity) (n : ℕ) :
    cellPrefixL n (unitCellAnalysis q) = primitive q n := by
  induction n with
  | zero => simp [cellPrefixL_zero, primitive]
  | succ n ih =>
      rw [cellPrefixL_succ, ih, unitCellAnalysis_apply]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

def cellularProjection : Velocity →L[ℝ] Velocity :=
  unitCellSynthesis.toContinuousLinearMap ∘L unitCellAnalysis

theorem cellularProjection_apply (q : Velocity) :
    cellularProjection q = unitCellSynthesis (unitCellAnalysis q) := rfl

theorem inner_cellular_residual (w : TraceData) (q : Velocity) :
    ⟪unitCellSynthesis w, q-cellularProjection q⟫ = 0 := by
  rw [inner_sub_right, cellularProjection_apply, unitCellSynthesis.inner_map_map,
    inner_unitCellSynthesis_analysis, sub_self]

theorem cellularProjection_energy (q : Velocity) :
    ‖unitCellAnalysis q‖^2 + ‖q-cellularProjection q‖^2 = ‖q‖^2 := by
  have hi : ⟪q, cellularProjection q⟫ = ‖unitCellAnalysis q‖^2 := by
    rw [real_inner_comm, cellularProjection_apply, inner_unitCellSynthesis_analysis,
      real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, hi, cellularProjection_apply, unitCellSynthesis.norm_map]
  ring

theorem unitCellAnalysis_cellularProjection (q : Velocity) :
    unitCellAnalysis (cellularProjection q) = unitCellAnalysis q :=
  unitCellAnalysis_synthesis (unitCellAnalysis q)

def negativePhysicalVelocity (q : Velocity) : Velocity :=
  (MemLp.indicator measurableSet_Iic (Lp.memLp q)).toLp
    ((Iic (0 : ℝ)).indicator (q : ℝ → ℝ))

theorem ae_negativePhysicalVelocity (q : Velocity) :
    negativePhysicalVelocity q =ᵐ[volume] (Iic (0 : ℝ)).indicator (q : ℝ → ℝ) :=
  MemLp.coeFn_toLp _

theorem unitCellAnalysis_negative (q : Velocity) :
    unitCellAnalysis (negativePhysicalVelocity q) = 0 := by
  apply lp.ext
  funext k
  change unitCellAnalysis (negativePhysicalVelocity q) k = 0
  rw [unitCellAnalysis_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (ae_negativePhysicalVelocity q),
    ae_restrict_mem (measurableSet_Ioc (a := (k : ℝ)) (b := k+1))] with t ht hs
  rw [ht]
  have hn : t ∉ Iic (0 : ℝ) := not_le.mpr (lt_of_le_of_lt (Nat.cast_nonneg k) hs.1)
  exact indicator_of_notMem hn _

theorem cellularProjection_negative (q : Velocity) :
    cellularProjection (negativePhysicalVelocity q) = 0 := by
  rw [cellularProjection_apply, unitCellAnalysis_negative, map_zero]

theorem norm_sq_negativePhysicalVelocity (q : Velocity) :
    ‖negativePhysicalVelocity q‖^2 = ∫ t in Iic (0 : ℝ), (q t)^2 := by
  rw [norm_sq_velocity, ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [ae_negativePhysicalVelocity q] with t ht
  rw [ht]
  by_cases h : t ∈ Iic (0 : ℝ) <;> simp [h]

theorem inner_negativePhysicalVelocity (q : Velocity) :
    ⟪negativePhysicalVelocity q, q⟫ = ‖negativePhysicalVelocity q‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_negativePhysicalVelocity q] with t ht
  simp only [Real.inner_apply, ht]
  by_cases h : t ∈ Iic (0 : ℝ) <;> simp [h]

/-- The negative half-line is retained as an explicit orthogonal error term. -/
theorem cellular_residual_negative_split (q : Velocity) :
    ‖q-cellularProjection q‖^2 = ‖negativePhysicalVelocity q‖^2 +
      ‖q-negativePhysicalVelocity q-cellularProjection q‖^2 := by
  have hc : ⟪negativePhysicalVelocity q, cellularProjection q⟫ = 0 := by
    rw [real_inner_comm, cellularProjection_apply, inner_unitCellSynthesis_analysis,
      unitCellAnalysis_negative, inner_zero_right]
  have ho : ⟪negativePhysicalVelocity q,
      q-negativePhysicalVelocity q-cellularProjection q⟫ = 0 := by
    rw [inner_sub_right, inner_sub_right, inner_negativePhysicalVelocity,
      real_inner_self_eq_norm_sq, hc]
    ring
  have he : q-cellularProjection q = negativePhysicalVelocity q +
      (q-negativePhysicalVelocity q-cellularProjection q) := by abel
  rw [he, norm_add_sq_real, ho]
  ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
