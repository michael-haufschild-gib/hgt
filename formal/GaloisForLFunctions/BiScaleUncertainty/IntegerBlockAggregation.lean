import GaloisForLFunctions.BiScaleUncertainty.PhysicalDilation

/-!
# Integer dilation as an actual infinite block-sum operator

Cell analysis after physical dilation constructs bounded block aggregation.
Prefix identities prove the coordinate formula, semigroup law and exact
intertwining for arbitrary physical velocities, without summability premises.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem norm_unitCellAnalysis_le (q : Velocity) : ‖unitCellAnalysis q‖ ≤ ‖q‖ := by
  have h := cellularProjection_energy q
  nlinarith only [h, sq_nonneg ‖q-cellularProjection q‖,
    norm_nonneg (unitCellAnalysis q), norm_nonneg q]

def integerBlockSum (m : ℕ) : TraceData →L[ℝ] TraceData :=
  unitCellAnalysis ∘L ((physicalDilation m) ∘L unitCellSynthesis.toContinuousLinearMap)

theorem integerBlockSum_apply (m : ℕ) (w : TraceData) :
    integerBlockSum m w = unitCellAnalysis (physicalDilation m (unitCellSynthesis w)) := rfl

theorem cellPrefixL_integerBlockSum (m n : ℕ) (w : TraceData) :
    cellPrefixL n (integerBlockSum m w) = cellPrefixL (m*n) w := by
  rw [integerBlockSum_apply, cellPrefixL_unitCellAnalysis, primitive_physicalDilation]
  simpa only [Nat.cast_mul] using primitive_unitCellSynthesis (m*n) w

theorem integerBlockSum_prefix_difference (m : ℕ) (w : TraceData) (j : ℕ) :
    integerBlockSum m w j = cellPrefixL (m*(j+1)) w-cellPrefixL (m*j) w := by
  have h := cellPrefixL_succ j (integerBlockSum m w)
  rw [cellPrefixL_integerBlockSum, cellPrefixL_integerBlockSum] at h
  linarith only [h]

theorem integerBlockSum_coordinate (m : ℕ) (w : TraceData) (j : ℕ) :
    integerBlockSum m w j = ∑ k ∈ Finset.Ico (m*j) (m*(j+1)), w k := by
  rw [cellPrefixL_interval _ _ (Nat.mul_le_mul_left m (Nat.le_succ j)),
    integerBlockSum_prefix_difference]

theorem integerBlockSum_range (m : ℕ) (w : TraceData) (j : ℕ) :
    integerBlockSum m w j = ∑ r ∈ Finset.range m, w (m*j+r) := by
  rw [integerBlockSum_coordinate, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_left]

theorem integerBlockSum_zero (w : TraceData) : integerBlockSum 0 w = 0 := by
  rw [integerBlockSum_apply, Nat.cast_zero, physicalDilation_zero, map_zero]

theorem integerBlockSum_one (w : TraceData) : integerBlockSum 1 w = w := by
  rw [integerBlockSum_apply, Nat.cast_one, physicalDilation_one, unitCellAnalysis_synthesis]

theorem integerBlockSum_comp (m n : ℕ) (w : TraceData) :
    integerBlockSum m (integerBlockSum n w) = integerBlockSum (m*n) w := by
  apply lp.ext
  funext j
  rw [integerBlockSum_prefix_difference, cellPrefixL_integerBlockSum,
    cellPrefixL_integerBlockSum, integerBlockSum_prefix_difference]
  rw [show n*(m*(j+1)) = (m*n)*(j+1) by ring,
    show n*(m*j) = (m*n)*j by ring]

theorem unitCellAnalysis_physicalDilation (m : ℕ) (q : Velocity) :
    unitCellAnalysis (physicalDilation m q) = integerBlockSum m (unitCellAnalysis q) := by
  apply lp.ext
  funext j
  simp only [unitCellAnalysis_apply, primitive_physicalDilation,
    integerBlockSum_prefix_difference, cellPrefixL_unitCellAnalysis,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]

theorem norm_integerBlockSum_le (m : ℕ) (w : TraceData) :
    ‖integerBlockSum m w‖ ≤ Real.sqrt (m : ℝ)*‖w‖ := by
  rw [integerBlockSum_apply]
  calc
    _ ≤ ‖physicalDilation m (unitCellSynthesis w)‖ := norm_unitCellAnalysis_le _
    _ = _ := by
      rw [physicalDilation_norm, unitCellSynthesis.norm_map,
        abs_of_nonneg (Nat.cast_nonneg m)]

theorem mem_integerBlock_iff (m j k : ℕ) (hm : 0 < m) :
    k ∈ Finset.Ico (m*j) (m*(j+1)) ↔ k/m = j := by
  rw [Finset.mem_Ico]
  constructor
  · intro h
    exact Nat.div_eq_of_lt_le (by simpa only [Nat.mul_comm] using h.1)
      (by simpa only [Nat.mul_comm] using h.2)
  · rintro rfl
    exact ⟨by simpa only [Nat.mul_comm] using Nat.div_mul_le_self k m,
      Nat.lt_mul_div_succ k hm⟩

theorem integerBlockSum_single (m k : ℕ) (hm : 0 < m) (a : ℝ) :
    integerBlockSum m (lp.single 2 k a) = lp.single 2 (k/m) a := by
  classical
  apply lp.ext
  funext j
  rw [integerBlockSum_coordinate]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [mem_integerBlock_iff m j k hm, eq_comm (a := k/m) (b := j)]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
