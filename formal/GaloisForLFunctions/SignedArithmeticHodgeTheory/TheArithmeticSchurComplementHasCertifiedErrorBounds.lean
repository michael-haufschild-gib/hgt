import GaloisForLFunctions.ArithmeticIndexDescent.TheUnboundedCellCarrierHasAWeilProjection

/-!
# Certified errors for the actual arithmetic Schur complement

The stationarity defect is the source Weil operator restricted to the fixed
arithmetic carrier. It bounds the error of any trial correction, including every
mixed entry. All constants are uniform on the unbounded carrier. The signed
complement and its null radical are retained.
-/

noncomputable section

open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticIndexDescent

/-- The complete source remaining after removal of the paid arithmetic carrier. -/
def arithmeticResidual : SourceGraph →L[ℝ] SourceGraph :=
  ContinuousLinearMap.id ℝ SourceGraph - fixedLogCellWeilProjection

/-- The mixed source charge seen by the paid arithmetic carrier. -/
def arithmeticStationarity : SourceGraph →L[ℝ] closedFixedLogCellGraph :=
  closedFixedLogCellGraph.orthogonalProjectionOnto.comp graphWeilOperator

theorem arithmeticResidual_apply (x : SourceGraph) :
    arithmeticResidual x = x - fixedLogCellWeilProjection x := rfl

theorem inner_arithmeticStationarity (x : SourceGraph) (u : closedFixedLogCellGraph) :
    inner ℝ (arithmeticStationarity x) u = weilBilin x u := by
  change inner ℝ (closedFixedLogCellGraph.orthogonalProjectionOnto
    (graphWeilOperator x)) u = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, inner_graphWeilOperator]

private theorem projection_sub_section (x : SourceGraph) (u : closedFixedLogCellGraph) :
    fixedLogCellWeilProjection (x - u) = fixedLogCellWeilProjection x - u := by
  rw [map_sub, fixedLogCellWeilProjection_fixes u.2]

private theorem residual_sub_section (x : SourceGraph) (u : closedFixedLogCellGraph) :
    arithmeticResidual (x - u) = arithmeticResidual x := by
  rw [arithmeticResidual_apply, arithmeticResidual_apply, projection_sub_section]
  abel

private theorem projection_energy_nonneg (x : SourceGraph) :
    0 ≤ weilForm (fixedLogCellWeilProjection x) := by
  have h := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  change ‖fixedLogCellWeilProjection x‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x) at h
  linarith only [h, sq_nonneg ‖fixedLogCellWeilProjection x‖]

/-- Only the restriction of the Weil operator to the carrier is charged. -/
theorem projection_energy_le_stationarity (x : SourceGraph) :
    weilForm (fixedLogCellWeilProjection x) ≤ 2 * ‖arithmeticStationarity x‖ ^ 2 := by
  let p : closedFixedLogCellGraph :=
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  have hcoer := norm_closedFixedLogCellGraph_le_weil p
  have hinner : weilForm (fixedLogCellWeilProjection x) =
      inner ℝ (arithmeticStationarity x) p := by
    rw [inner_arithmeticStationarity, weilForm_fixedLogCellWeilProjection,
      inner_graphWeilOperator]
  have hupper : weilForm (fixedLogCellWeilProjection x) ≤
      ‖arithmeticStationarity x‖ * ‖p‖ := by
    rw [hinner]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  change ‖p‖ ^ 2 ≤ 2 * weilForm (fixedLogCellWeilProjection x) at hcoer
  nlinarith only [hcoer, hupper, sq_nonneg (‖p‖ - 2 * ‖arithmeticStationarity x‖)]

theorem norm_projection_le_stationarity (x : SourceGraph) :
    ‖fixedLogCellWeilProjection x‖ ≤ 2 * ‖arithmeticStationarity x‖ := by
  have h := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  change ‖fixedLogCellWeilProjection x‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x) at h
  nlinarith only [h, projection_energy_le_stationarity x,
    norm_nonneg (fixedLogCellWeilProjection x), norm_nonneg (arithmeticStationarity x)]

/-- A trial correction has an exact signed residual plus one positive error. -/
theorem arithmetic_trial_energy_decomposition (x : SourceGraph)
    (u : closedFixedLogCellGraph) :
    weilForm (x - u) = weilForm (arithmeticResidual x) +
      weilForm (fixedLogCellWeilProjection x - u) := by
  have h := weilBilin_fixedLogCellResidual (x - u) (x - u)
  change weilBilin (arithmeticResidual (x - u)) (arithmeticResidual (x - u)) = _ at h
  rw [residual_sub_section, projection_sub_section] at h
  simp only [← weilForm_eq_weilBilin] at h
  linarith only [h]

/-- Every trial supplies a rigorous interval for the full signed residual energy. -/
theorem arithmetic_trial_energy_bounds (x : SourceGraph) (u : closedFixedLogCellGraph) :
    weilForm (x - u) - 2 * ‖arithmeticStationarity (x - u)‖ ^ 2 ≤
        weilForm (arithmeticResidual x) ∧
      weilForm (arithmeticResidual x) + (1 / 2 : ℝ) *
        ‖fixedLogCellWeilProjection x - u‖ ^ 2 ≤ weilForm (x - u) := by
  have hupper := projection_energy_le_stationarity (x - u)
  rw [projection_sub_section] at hupper
  have hfloor := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x - u,
      closedFixedLogCellGraph.sub_mem (fixedLogCellWeilProjection_mem x) u.2⟩
  change ‖fixedLogCellWeilProjection x - u‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x - u) at hfloor
  have he := arithmetic_trial_energy_decomposition x u
  constructor <;> linarith only [hupper, hfloor, he]

/-- Stationarity measures graph error, without assuming positivity of the complement. -/
theorem arithmetic_trial_graph_error (x : SourceGraph) (u : closedFixedLogCellGraph) :
    ‖fixedLogCellWeilProjection x - u‖ ≤
      2 * ‖arithmeticStationarity (x - u)‖ := by
  simpa only [projection_sub_section] using norm_projection_le_stationarity (x - u)

/-- The exact arithmetic correction is the unique energy minimizer on its affine fibre. -/
theorem arithmetic_trial_energy_eq_iff (x : SourceGraph) (u : closedFixedLogCellGraph) :
    weilForm (x - u) = weilForm (arithmeticResidual x) ↔
      (u : SourceGraph) = fixedLogCellWeilProjection x := by
  constructor
  · intro he
    have h := (arithmetic_trial_energy_bounds x u).2
    rw [he] at h
    have hz : ‖fixedLogCellWeilProjection x - u‖ ^ 2 = 0 := by
      nlinarith only [h, sq_nonneg ‖fixedLogCellWeilProjection x - u‖]
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  · intro he
    rw [he, arithmeticResidual_apply]

private theorem abs_projection_pair_le (x y : SourceGraph) :
    |weilBilin (fixedLogCellWeilProjection x) (fixedLogCellWeilProjection y)| ≤
      2 * ‖arithmeticStationarity x‖ * ‖arithmeticStationarity y‖ := by
  let p : closedFixedLogCellGraph :=
    ⟨fixedLogCellWeilProjection y, fixedLogCellWeilProjection_mem y⟩
  have horth := fixedLogCellWeilProjection_orthogonal x p.2
  rw [weilBilin_sub_right, weilBilin_comm (p : SourceGraph) x,
    weilBilin_comm (p : SourceGraph) (fixedLogCellWeilProjection x)] at horth
  have hp : weilBilin (fixedLogCellWeilProjection x) (fixedLogCellWeilProjection y) =
      inner ℝ (arithmeticStationarity x) p := by
    rw [inner_arithmeticStationarity]
    exact (sub_eq_zero.mp horth).symm
  rw [hp]
  calc
    |inner ℝ (arithmeticStationarity x) p| ≤ ‖arithmeticStationarity x‖ * ‖p‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖arithmeticStationarity x‖ * (2 * ‖arithmeticStationarity y‖) :=
      mul_le_mul_of_nonneg_left (norm_projection_le_stationarity y) (norm_nonneg _)
    _ = _ := by ring

/-- Every mixed Schur entry has a joint defect bound in the original source topology. -/
theorem arithmetic_trial_mixed_error (x y : SourceGraph)
    (u v : closedFixedLogCellGraph) :
    |weilBilin (x - u) (y - v) -
        weilBilin (arithmeticResidual x) (arithmeticResidual y)| ≤
      2 * ‖arithmeticStationarity (x - u)‖ * ‖arithmeticStationarity (y - v)‖ := by
  have h := weilBilin_fixedLogCellResidual (x - u) (y - v)
  change weilBilin (arithmeticResidual (x - u)) (arithmeticResidual (y - v)) = _ at h
  rw [residual_sub_section, residual_sub_section] at h
  have he : weilBilin (x - u) (y - v) -
      weilBilin (arithmeticResidual x) (arithmeticResidual y) =
      weilBilin (fixedLogCellWeilProjection (x - u))
        (fixedLogCellWeilProjection (y - v)) := by linarith only [h]
  rw [he]
  exact abs_projection_pair_le (x - u) (y - v)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.arithmetic_trial_energy_bounds
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.arithmetic_trial_graph_error
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.arithmetic_trial_energy_eq_iff
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.arithmetic_trial_mixed_error
