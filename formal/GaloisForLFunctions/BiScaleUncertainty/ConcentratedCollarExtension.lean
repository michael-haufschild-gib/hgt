import GaloisForLFunctions.BiScaleUncertainty.RightNodeCollarPartition

/-!
# Concentrated extension of physical collar partitions

Preserve every old physical share and fill the added interval by its right
logarithmic nodes. The new signed density is supported in an inverse-cutoff
origin-offset interval. Endpoints retain the exact physical partition law.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem log_four_lt_collarEndpoint {n : ℕ} (hn : 6 ≤ n) :
    Real.log 4 < logarithmicCollarEndpoint n :=
  Real.log_lt_log (by norm_num) (by exact_mod_cast (show 4 < n + 2 by omega))

namespace PhysicalCollarPartition
variable {n m : ℕ}

/-- Splice actual partitions along an arbitrary measurable physical region. -/
def splice (ρ η : PhysicalCollarPartition n) (S : Set ℝ) (hS : MeasurableSet S) :
    PhysicalCollarPartition n where
  share k x := if x ∈ S then ρ.share k x else η.share k x
  measurable_share k := Measurable.ite hS (ρ.measurable_share k) (η.measurable_share k)
  nonneg := by intro k x; split_ifs <;> first | exact ρ.nonneg k x | exact η.nonneg k x
  supported := by intro k x hx; split_ifs <;> first | exact ρ.supported k x hx | exact η.supported k x hx
  partition := by
    intro x
    by_cases hx : x ∈ S
    · simpa only [if_pos hx] using ρ.partition x
    · simpa only [if_neg hx] using η.partition x

def concentratedExtend (ρ : PhysicalCollarPartition n) (hm : n ≤ m) :
    PhysicalCollarPartition m :=
  (ρ.extend hm).splice (rightNode m) (Iio (logarithmicCollarEndpoint n)) measurableSet_Iio

/-- The exact added density; this depends only on the two cutoffs. -/
def rightTailWeight (m n : ℕ) (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  if logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarEndpoint n
  then 0 else (rightNode m).weight σ k y

theorem rightTailWeight_nonneg (m n : ℕ) (σ : Bool) (k : ℕ) (y : ℝ) :
    0 ≤ rightTailWeight m n σ k y := by
  unfold rightTailWeight
  split_ifs
  · exact le_rfl
  · exact (rightNode m).weight_nonneg σ k y

theorem rightTailWeight_le (m n : ℕ) (σ : Bool) (k : ℕ) (y : ℝ) :
    rightTailWeight m n σ k y ≤ (rightNode m).weight σ k y := by
  unfold rightTailWeight
  split_ifs
  · exact (rightNode m).weight_nonneg σ k y
  · exact le_rfl

theorem concentratedExtend_weight (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    (ρ.concentratedExtend hm).weight σ k y =
      collarArrayPad n (fun σ k => ρ.weight σ k y) σ k + rightTailWeight m n σ k y := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  by_cases hx : x < logarithmicCollarEndpoint n
  · by_cases hk : k < n + 1 <;>
      simp only [concentratedExtend, weight, density, splice, extend, mem_Iio,
        collarArrayPad, rightTailWeight, if_pos hx, if_pos hk, if_neg hk, zero_mul, add_zero]
  · have hz : ρ.weight σ k y = 0 := by
      have hs := ρ.supported k x (fun hc => hx hc.2.2)
      change ρ.share k x * archLevySinhWeight x = 0
      rw [hs, zero_mul]
    by_cases hk : k < n + 1 <;>
      simp only [concentratedExtend, weight, density, splice, mem_Iio, collarArrayPad,
        rightTailWeight, if_neg hx, if_pos hk, if_neg hk, hz, zero_add]

theorem pad_weight_le_concentratedExtend (ρ : PhysicalCollarPartition n) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    collarArrayPad n (fun σ k => ρ.weight σ k y) σ k ≤
      (ρ.concentratedExtend hm).weight σ k y := by
  rw [ρ.concentratedExtend_weight hm]
  exact le_add_of_nonneg_right (rightTailWeight_nonneg m n σ k y)

/-- Every nonzero added fibre obeys both the node mesh and the cutoff mesh. -/
theorem rightTailWeight_nonzero {σ : Bool} {k : ℕ} {y : ℝ}
    (hn : 6 ≤ n) (hy : 0 < y) (hw : rightTailWeight m n σ k y ≠ 0) :
    σ = false ∧ ((k + 1 : ℕ) : ℝ) * y ≤ 1 ∧
      y ≤ 1 / ((n + 2 : ℕ) : ℝ) := by
  have hx : logarithmicCollarEndpoint n ≤ logarithmicCollarNode k + collarSignedOffset σ y := by
    by_contra h
    exact hw (if_pos (lt_of_not_ge h))
  have hw' : (rightNode m).weight σ k y ≠ 0 := by
    simpa only [rightTailWeight, if_neg (not_lt.mpr hx)] using hw
  have h := rightNode_weight_nonzero hy ((log_four_lt_collarEndpoint hn).trans_le hx) hw'
  refine ⟨h.1, h.2.2, h.2.1.trans ?_⟩
  have he := Real.exp_le_exp.mpr (neg_le_neg hx)
  simpa only [logarithmicCollarEndpoint, Real.exp_neg,
    Real.exp_log (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ)), one_div] using he

theorem rightTailWeight_zero_above_mesh {σ : Bool} {k : ℕ} {y : ℝ}
    (hn : 6 ≤ n) (hy : 1 / ((n + 2 : ℕ) : ℝ) < y) :
    rightTailWeight m n σ k y = 0 := by
  by_contra hw
  have h := rightTailWeight_nonzero hn (lt_trans (by positivity) hy) hw
  exact (not_lt_of_ge h.2.2) hy

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
