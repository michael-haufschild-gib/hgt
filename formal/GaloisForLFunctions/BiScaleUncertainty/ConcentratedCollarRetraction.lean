import GaloisForLFunctions.BiScaleUncertainty.ConcentratedCollarExtension

/-!
# Concentrated repair of a physical collar restriction

Retain every available old-node share in the smaller physical window. Assign
exactly its missing fraction to the right-node partition. Missing mass is
confined to the physical cutoff boundary; its fibres consequently lie within
twice the inverse cutoff of the origin.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem log_four_lt_collarRetention {n : ℕ} (hn : 6 ≤ n) :
    Real.log 4 < logarithmicCollarRetention n := by
  have hlog : Real.log 4 + Real.log 2 ≤ logarithmicCollarEndpoint n := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    apply Real.log_le_log (by norm_num)
    norm_num
    exact_mod_cast (show 8 ≤ n + 2 by omega)
  have hd : logarithmicCollarRadius < Real.log 2 := by
    unfold logarithmicCollarRadius
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  unfold logarithmicCollarRetention
  linarith

theorem exp_neg_collarRetention_le (n : ℕ) :
    Real.exp (-logarithmicCollarRetention n) ≤ 2 / ((n + 2 : ℕ) : ℝ) := by
  have he : Real.exp (logarithmicCollarRadius) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    unfold logarithmicCollarRadius
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  rw [show -logarithmicCollarRetention n =
    logarithmicCollarRadius - logarithmicCollarEndpoint n by
      unfold logarithmicCollarRetention; ring, Real.exp_sub,
    show Real.exp (logarithmicCollarEndpoint n) = ((n + 2 : ℕ) : ℝ) from
      Real.exp_log (by positivity)]
  exact div_le_div_of_nonneg_right he (by positivity)

namespace PhysicalCollarPartition
variable {n m : ℕ}

def oldShareSum (η : PhysicalCollarPartition m) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), η.share k x

theorem measurable_oldShareSum (η : PhysicalCollarPartition m) (n : ℕ) :
    Measurable (η.oldShareSum n) :=
  (Finset.range (n + 1)).measurable_sum (fun k _ => η.measurable_share k)

theorem oldShareSum_nonneg (η : PhysicalCollarPartition m) (n : ℕ) (x : ℝ) :
    0 ≤ η.oldShareSum n x :=
  Finset.sum_nonneg (fun k _ => η.nonneg k x)

theorem oldShareSum_le_one (η : PhysicalCollarPartition m) (hm : n ≤ m) (x : ℝ) :
    η.oldShareSum n x ≤ 1 := by
  have hs : η.oldShareSum n x ≤ ∑ k ∈ Finset.range (m + 1), η.share k x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
    · exact fun k _ _ => η.nonneg k x
  rw [η.partition] at hs
  by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint m)
  · simpa only [indicator_of_mem hx] using hs
  · rw [indicator_of_notMem hx] at hs
    exact hs.trans zero_le_one

theorem oldShareSum_eq_one_below_retention (η : PhysicalCollarPartition m) (hm : n ≤ m)
    {x : ℝ} (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))
    (hr : x < logarithmicCollarRetention n) : η.oldShareSum n x = 1 := by
  have heq : η.oldShareSum n x = ∑ k ∈ Finset.range (m + 1), η.share k x := by
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
    · intro k _ hk
      exact η.extra_share_zero_below_retention (by
        simpa only [Finset.mem_range, not_lt] using hk) hr
  rw [heq, η.partition, indicator_of_mem
    (show x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint m) from
      ⟨hx.1, hx.2.trans_le (logarithmicCollarEndpoint_monotone hm)⟩)]

/-- Fill exactly the missing old-window mass, without moving retained shares. -/
def concentratedRetract (η : PhysicalCollarPartition m) (hm : n ≤ m) :
    PhysicalCollarPartition n where
  share k x := if x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) then
    η.share k x + (1 - η.oldShareSum n x) * (rightNode n).share k x else 0
  measurable_share k := Measurable.ite measurableSet_Ioo
    ((η.measurable_share k).add
      ((measurable_const.sub (η.measurable_oldShareSum n)).mul
        ((rightNode n).measurable_share k))) measurable_const
  nonneg := by
    intro k x
    split_ifs
    · exact add_nonneg (η.nonneg k x)
        (mul_nonneg (sub_nonneg.mpr (η.oldShareSum_le_one hm x)) ((rightNode n).nonneg k x))
    · exact le_rfl
  supported := by
    intro k x hx
    split_ifs with hwin
    · have hz : η.share k x = 0 := η.supported k x (fun hc =>
        hx ⟨hc.1, logarithmicCollarRadius_pos.trans hwin.1, hwin.2⟩)
      rw [hz, (rightNode n).supported k x hx, mul_zero, add_zero]
    · rfl
  partition := by
    intro x
    by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
    · simp only [if_pos hx, Finset.sum_add_distrib, ← Finset.mul_sum,
        (rightNode n).partition x, indicator_of_mem hx, mul_one]
      change η.oldShareSum n x + (1 - η.oldShareSum n x) = 1
      ring
    · simp only [if_neg hx, Finset.sum_const_zero, indicator_of_notMem hx]

def rightRepairWeight (η : PhysicalCollarPartition m) (n : ℕ)
    (σ : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  (1 - η.oldShareSum n (logarithmicCollarNode k + collarSignedOffset σ y)) *
    (rightNode n).weight σ k y

theorem rightRepairWeight_nonneg (η : PhysicalCollarPartition m) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ) : 0 ≤ η.rightRepairWeight n σ k y :=
  mul_nonneg (sub_nonneg.mpr (η.oldShareSum_le_one hm _)) ((rightNode n).weight_nonneg σ k y)

theorem rightRepairWeight_le (η : PhysicalCollarPartition m) (n : ℕ)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    η.rightRepairWeight n σ k y ≤ (rightNode n).weight σ k y :=
  mul_le_of_le_one_left ((rightNode n).weight_nonneg σ k y)
    (sub_le_self 1 (η.oldShareSum_nonneg n _))

theorem concentratedRetract_weight_le (η : PhysicalCollarPartition m) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    (η.concentratedRetract hm).weight σ k y ≤ η.weight σ k y + η.rightRepairWeight n σ k y := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
  · change (if x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) then
        η.share k x + (1 - η.oldShareSum n x) * (rightNode n).share k x else 0) *
        archLevySinhWeight x ≤ _
    rw [if_pos hx]
    unfold rightRepairWeight weight density
    dsimp [x]
    ring_nf
    exact le_rfl
  · change (if x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) then
        η.share k x + (1 - η.oldShareSum n x) * (rightNode n).share k x else 0) *
        archLevySinhWeight x ≤ _
    rw [if_neg hx, zero_mul]
    exact add_nonneg (η.weight_nonneg σ k y) (η.rightRepairWeight_nonneg hm σ k y)

theorem rightRepairWeight_nonzero (η : PhysicalCollarPartition m) (hm : n ≤ m)
    {σ : Bool} {k : ℕ} {y : ℝ} (hk : k ∈ Finset.range (n + 1))
    (hn : 6 ≤ n) (hy : 0 < y) (hw : η.rightRepairWeight n σ k y ≠ 0) :
    σ = false ∧ y ≤ 2 / ((n + 2 : ℕ) : ℝ) := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  have hw' : (rightNode n).weight σ k y ≠ 0 := by
    intro hz
    exact hw (by unfold rightRepairWeight; rw [hz, mul_zero])
  have hr : logarithmicCollarRetention n ≤ x := by
    by_contra hr
    have hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) := by
      by_contra hx
      apply hw'
      change (rightNode n).share k x * archLevySinhWeight x = 0
      rw [(rightNode n).share_zero_outside k hk hx, zero_mul]
    have hsum := η.oldShareSum_eq_one_below_retention hm hx (lt_of_not_ge hr)
    apply hw
    change (1 - η.oldShareSum n x) * (rightNode n).weight σ k y = 0
    rw [hsum, sub_self, zero_mul]
  have h := rightNode_weight_nonzero hy ((log_four_lt_collarRetention hn).trans_le hr) hw'
  exact ⟨h.1, h.2.1.trans
    ((Real.exp_le_exp.mpr (neg_le_neg hr)).trans (exp_neg_collarRetention_le n))⟩

theorem rightRepairWeight_zero_above_mesh (η : PhysicalCollarPartition m) (hm : n ≤ m)
    {σ : Bool} {k : ℕ} {y : ℝ} (hk : k ∈ Finset.range (n + 1))
    (hn : 6 ≤ n) (hy : 2 / ((n + 2 : ℕ) : ℝ) < y) :
    η.rightRepairWeight n σ k y = 0 := by
  by_contra hw
  have h := η.rightRepairWeight_nonzero hm hk hn (lt_trans (by positivity) hy) hw
  exact (not_lt_of_ge h.2) hy

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
