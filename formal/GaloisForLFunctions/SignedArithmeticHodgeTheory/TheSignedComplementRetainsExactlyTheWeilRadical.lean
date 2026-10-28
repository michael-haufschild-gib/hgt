import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticSchurComplementHasCertifiedErrorBounds

/-!
# The radical of the signed arithmetic complement

The complement is the kernel of the actual Weil projection, equivalently the
kernel of the stationarity map. Its bilinear radical is exactly the radical of
the original full Weil form. The arithmetic theta family gives infinitely many
independent vectors in this radical.
-/

noncomputable section

open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticIndexDescent

/-- The signed source complement of the fixed positive arithmetic carrier. -/
def arithmeticComplement : Submodule ℝ SourceGraph :=
  fixedLogCellWeilProjection.ker

/-- The radical of the original full Weil form, before any section is removed. -/
def arithmeticWeilRadical : Submodule ℝ SourceGraph :=
  graphWeilOperator.ker

theorem arithmeticResidual_mem_complement (x : SourceGraph) :
    arithmeticResidual x ∈ arithmeticComplement := by
  change fixedLogCellWeilProjection (x - fixedLogCellWeilProjection x) = 0
  rw [map_sub, fixedLogCellWeilProjection_idempotent, sub_self]

theorem arithmeticResidual_fixes_complement (r : arithmeticComplement) :
    arithmeticResidual r = r := by
  rw [arithmeticResidual_apply, show fixedLogCellWeilProjection r = 0 from r.2, sub_zero]

/-- Zero stationarity is an exact source-space condition, not an energy sign. -/
theorem stationarity_eq_zero_iff_mem_complement (x : SourceGraph) :
    arithmeticStationarity x = 0 ↔ x ∈ arithmeticComplement := by
  constructor
  · intro hx
    have h := norm_projection_le_stationarity x
    rw [hx] at h
    change ‖fixedLogCellWeilProjection x‖ ≤ 2 * ‖(0 : SourceGraph)‖ at h
    rw [norm_zero, mul_zero] at h
    change fixedLogCellWeilProjection x = 0
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  · intro hx
    apply ext_inner_right ℝ
    intro u
    rw [inner_arithmeticStationarity]
    change weilBilin x u = inner ℝ (0 : SourceGraph) (u : SourceGraph)
    rw [inner_zero_left, weilBilin_comm]
    have h := fixedLogCellWeilProjection_orthogonal x u.2
    change fixedLogCellWeilProjection x = 0 at hx
    simpa only [hx, sub_zero] using h

theorem arithmeticStationarity_residual (x : SourceGraph) :
    arithmeticStationarity (arithmeticResidual x) = 0 :=
  (stationarity_eq_zero_iff_mem_complement _).mpr (arithmeticResidual_mem_complement x)

/-- Global null directions lie in the signed complement and cost no correction. -/
theorem arithmeticWeilRadical_le_complement :
    arithmeticWeilRadical ≤ arithmeticComplement := by
  intro z hz
  apply (stationarity_eq_zero_iff_mem_complement z).mp
  change closedFixedLogCellGraph.orthogonalProjectionOnto (graphWeilOperator z) = 0
  change graphWeilOperator z = 0 at hz
  rw [hz, map_zero]

/-- Restricting to the complement creates no new bilinear radical. -/
theorem complement_radical_iff (r : arithmeticComplement) :
    (r : SourceGraph) ∈ arithmeticWeilRadical ↔
      ∀ s : arithmeticComplement, weilBilin r s = 0 := by
  constructor
  · intro hr s
    change graphWeilOperator r = 0 at hr
    rw [← inner_graphWeilOperator, hr, inner_zero_left]
  · intro hr
    change graphWeilOperator r = 0
    apply ext_inner_right ℝ
    intro x
    rw [inner_graphWeilOperator, inner_zero_left]
    have hpair := hr ⟨arithmeticResidual x, arithmeticResidual_mem_complement x⟩
    have horth := fixedLogCellWeilProjection_orthogonal (r : SourceGraph)
      (fixedLogCellWeilProjection_mem x)
    rw [show fixedLogCellWeilProjection r = 0 from r.2, sub_zero, weilBilin_comm] at horth
    change weilBilin (r : SourceGraph) (arithmeticResidual x) = 0 at hpair
    rw [arithmeticResidual_apply, weilBilin_sub_right, horth, sub_zero] at hpair
    exact hpair

/-- The section correction is invariant under adding a genuine full-form null source. -/
theorem projection_add_radical (x : SourceGraph) (z : arithmeticWeilRadical) :
    fixedLogCellWeilProjection (x + z) = fixedLogCellWeilProjection x := by
  have hz : fixedLogCellWeilProjection z = 0 :=
    arithmeticWeilRadical_le_complement z.2
  rw [map_add, hz, add_zero]

/-- Null source information remains in the residual rather than being deleted. -/
theorem residual_add_radical (x : SourceGraph) (z : arithmeticWeilRadical) :
    arithmeticResidual (x + z) = arithmeticResidual x + z := by
  rw [arithmeticResidual_apply, projection_add_radical, arithmeticResidual_apply]
  abel

/-- The radical contains the actual independent theta family on the complete graph. -/
theorem exists_infinite_arithmeticWeilRadical :
    ∃ z : ℕ → SourceGraph, LinearIndependent ℝ z ∧
      ∀ n, z n ∈ arithmeticWeilRadical ∧ arithmeticResidual (z n) = z n := by
  refine ⟨CHMDThetaTranslate.sequence, CHMDThetaTranslate.sequence_linearIndependent, ?_⟩
  intro n
  have hz : CHMDThetaTranslate.sequence n ∈ arithmeticWeilRadical := by
    change graphWeilOperator (CHMDThetaTranslate.sequence n) = 0
    apply ext_inner_right ℝ
    intro q
    rw [inner_graphWeilOperator, inner_zero_left]
    exact graphWeilPair_critical _ _ q
  exact ⟨hz, arithmeticResidual_fixes_complement
    ⟨CHMDThetaTranslate.sequence n, arithmeticWeilRadical_le_complement hz⟩⟩

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.complement_radical_iff
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_infinite_arithmeticWeilRadical
