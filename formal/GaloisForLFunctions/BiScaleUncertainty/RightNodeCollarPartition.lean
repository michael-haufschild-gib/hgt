import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffStability
import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridTailRigidity
import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurable right-node collar allocation

Above log 4, assign each physical point to the first logarithmic node at or to
its right. The finite window remains open at its upper endpoint. The existing
partition fills the bounded initial interval, where one-sided collars need not
cover. The mesh estimate gives quantitative concentration of every tail fibre.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem quarter_le_logarithmicCollarRadius : (1 / 4 : ℝ) ≤ logarithmicCollarRadius := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  unfold logarithmicCollarRadius
  linarith

theorem measurable_logarithmicCeilNode : Measurable logarithmicCeilNode :=
  Real.continuous_exp.measurable.nat_ceil

def rightNodeCell (n k : ℕ) : Set ℝ :=
  Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) ∩
    {x | logarithmicCeilNode x = k + 2}

theorem measurableSet_rightNodeCell (n k : ℕ) : MeasurableSet (rightNodeCell n k) :=
  measurableSet_Ioo.inter ((measurableSet_singleton (k + 2)).preimage
    measurable_logarithmicCeilNode)

theorem rightNodeCell_subset_collar {n k : ℕ} {x : ℝ}
    (hx : x ∈ rightNodeCell n k) (hhigh : Real.log 4 < x) :
    x ∈ logarithmicPhysicalCollar n k := by
  have hlag := logarithmicCeilLag_bounds x
  have he : Real.exp (-x) < (1 / 4 : ℝ) := by
    have h := Real.exp_lt_exp.mpr (neg_lt_neg hhigh)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4),
      one_div] using h
  have hn : Real.log (logarithmicCeilNode x : ℝ) = logarithmicCollarNode k := by
    rw [hx.2]
    rfl
  unfold logarithmicCeilLag at hlag
  rw [hn] at hlag
  exact ⟨⟨by linarith [quarter_le_logarithmicCollarRadius],
    by linarith [logarithmicCollarRadius_pos]⟩,
    logarithmicCollarRadius_pos.trans hx.1.1, hx.1.2⟩

namespace PhysicalCollarPartition

/-- One-sided nearest-node allocation beyond a fixed bounded initial interval. -/
def rightNode (n : ℕ) : PhysicalCollarPartition n where
  share k x := if x ≤ Real.log 4 then (equalMultiplicity n).share k x
    else (rightNodeCell n k).indicator (fun _ => 1) x
  measurable_share k :=
    Measurable.ite measurableSet_Iic ((equalMultiplicity n).measurable_share k)
      (measurable_const.indicator (measurableSet_rightNodeCell n k))
  nonneg := by
    intro k x
    split_ifs
    · exact (equalMultiplicity n).nonneg k x
    · exact indicator_nonneg (fun _ _ => zero_le_one) x
  supported := by
    intro k x hx
    split_ifs with h
    · exact (equalMultiplicity n).supported k x hx
    · exact indicator_of_notMem (fun hc => hx (rightNodeCell_subset_collar hc (lt_of_not_ge h))) _
  partition := by
    intro x
    by_cases hhigh : x ≤ Real.log 4
    · simp only [if_pos hhigh]
      exact (equalMultiplicity n).partition x
    · simp only [if_neg hhigh]
      by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)
      · rw [indicator_of_mem hx]
        have htwo : 2 ≤ logarithmicCeilNode x :=
          logarithmicCeilNode_ge_two (logarithmicCollarRadius_pos.trans hx.1)
        have hcap : logarithmicCeilNode x ≤ n + 2 := by
          apply Nat.ceil_le.mpr
          have h := Real.exp_le_exp.mpr hx.2.le
          simpa only [logarithmicCollarEndpoint, Real.exp_log (by positivity :
            (0 : ℝ) < ((n + 2 : ℕ) : ℝ))] using h
        let j := logarithmicCeilNode x - 2
        have hj : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by dsimp [j]; omega)
        have hnode : logarithmicCeilNode x = j + 2 := by dsimp [j]; omega
        rw [Finset.sum_eq_single j]
        · have hc : x ∈ rightNodeCell n j := ⟨hx, hnode⟩
          exact indicator_of_mem hc _
        · intro k _ hkj
          apply indicator_of_notMem (s := rightNodeCell n k) (a := x)
          intro hc
          have hkn : logarithmicCeilNode x = k + 2 := hc.2
          exact hkj (by omega)
        · intro h
          exact (h hj).elim
      · rw [indicator_of_notMem hx]
        apply Finset.sum_eq_zero
        intro k _
        exact indicator_of_notMem (fun hc => hx hc.1) _

theorem rightNode_share_of_high (n k : ℕ) {x : ℝ} (hx : Real.log 4 < x) :
    (rightNode n).share k x = (rightNodeCell n k).indicator (fun _ => 1) x := by
  simp only [rightNode, if_neg (not_le.mpr hx)]

theorem rightNode_share_nonzero {n k : ℕ} {x : ℝ} (hx : Real.log 4 < x)
    (h : (rightNode n).share k x ≠ 0) : x ∈ rightNodeCell n k := by
  by_contra hc
  rw [rightNode_share_of_high n k hx, indicator_of_notMem hc] at h
  exact h rfl

/-- A nonzero high-cell fibre is left-sided and has inverse-node mesh width. -/
theorem rightNode_weight_nonzero {n k : ℕ} {σ : Bool} {y : ℝ} (hy : 0 < y)
    (hx : Real.log 4 < logarithmicCollarNode k + collarSignedOffset σ y)
    (hw : (rightNode n).weight σ k y ≠ 0) :
    σ = false ∧
    y ≤ Real.exp (-(logarithmicCollarNode k + collarSignedOffset σ y)) ∧
    ((k + 1 : ℕ) : ℝ) * y ≤ 1 := by
  let x := logarithmicCollarNode k + collarSignedOffset σ y
  have hs : (rightNode n).share k x ≠ 0 := by
    intro hz
    apply hw
    change (rightNode n).share k x * archLevySinhWeight x = 0
    rw [hz, zero_mul]
  have hc := rightNode_share_nonzero hx hs
  have hlag := logarithmicCeilLag_bounds x
  have hn : Real.log (logarithmicCeilNode x : ℝ) = logarithmicCollarNode k := by
    rw [hc.2]
    rfl
  unfold logarithmicCeilLag at hlag
  rw [hn] at hlag
  have hσ : σ = false := by
    cases σ
    · rfl
    · simp only [x, collarSignedOffset, ↓reduceIte] at hlag
      linarith [hlag.1]
  subst σ
  have he : y ≤ Real.exp (-x) := by
    simpa only [x, collarSignedOffset, Bool.false_eq_true, ↓reduceIte,
      ← sub_eq_add_neg, sub_sub_cancel] using hlag.2
  refine ⟨rfl, he, ?_⟩
  have hu := Nat.ceil_lt_add_one (Real.exp_pos x).le
  change (logarithmicCeilNode x : ℝ) < Real.exp x + 1 at hu
  rw [hc.2] at hu
  have hnode : ((k + 1 : ℕ) : ℝ) ≤ Real.exp x := by
    push_cast at hu ⊢
    linarith
  calc
    ((k + 1 : ℕ) : ℝ) * y ≤ Real.exp x * Real.exp (-x) :=
      mul_le_mul hnode he hy.le (Real.exp_pos x).le
    _ = 1 := by rw [← Real.exp_add]; simp

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
