import GaloisForLFunctions.RHTower.WeilLogShiftMomentBarycentric
import Mathlib.Tactic.Linarith

/-! Exact nodal-weight ratios and strict alternation on ordered real nodes. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilMomentWeights_ratio {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (i j : Fin (n + 1)) (hij : i ≠ j) :
    finiteWeilMomentWeights h j / finiteWeilMomentWeights h i =
      -∏ l ∈ (Finset.univ.erase i).erase j, (h i - h l) / (h j - h l) := by
  have hi : (h i - h j) * ∏ l ∈ (Finset.univ.erase i).erase j, (h i - h l) =
      ∏ l ∈ Finset.univ.erase i, (h i - h l) :=
    Finset.mul_prod_erase (Finset.univ.erase i) (fun l => h i - h l)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  have hj : (h j - h i) * ∏ l ∈ (Finset.univ.erase i).erase j, (h j - h l) =
      ∏ l ∈ Finset.univ.erase j, (h j - h l) := by
    rw [Finset.erase_right_comm]
    exact Finset.mul_prod_erase (Finset.univ.erase j) (fun l => h j - h l)
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  have hne : h i - h j ≠ 0 := sub_ne_zero.mpr (fun heq => hij (hinj heq))
  simp only [finiteWeilMomentWeights, Lagrange.nodalWeight, Finset.prod_inv_distrib]
  rw [inv_div_inv, ← hi, ← hj, Finset.prod_div_distrib]
  rw [show h j - h i = -(h i - h j) by ring, neg_mul, div_neg,
    mul_div_mul_left _ _ hne]

theorem finiteWeilNormalizedMomentDual_ratio {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (i j : Fin (n + 1)) (hij : i ≠ j) :
    finiteWeilNormalizedMomentDual h j / finiteWeilNormalizedMomentDual h i =
      -∏ l ∈ (Finset.univ.erase i).erase j, (h i - h l) / (h j - h l) := by
  change (‖finiteWeilMomentWeights h‖⁻¹ * finiteWeilMomentWeights h j) /
    (‖finiteWeilMomentWeights h‖⁻¹ * finiteWeilMomentWeights h i) = _
  rw [mul_div_mul_left _ _ (inv_ne_zero (finiteWeilMomentWeights_norm_pos h hinj).ne')]
  exact finiteWeilMomentWeights_ratio h hinj i j hij

theorem finiteWeilNormalizedMomentDual_adjacent_ratio_neg {n : ℕ}
    (h : Fin (n + 1) → ℝ) (hmono : StrictMono h) (i : Fin n) :
    finiteWeilNormalizedMomentDual h i.succ /
      finiteWeilNormalizedMomentDual h i.castSucc < 0 := by
  have hne : i.castSucc ≠ i.succ := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp at hv
    omega
  rw [finiteWeilNormalizedMomentDual_ratio h hmono.injective _ _ hne]
  have hp : 0 < ∏ j ∈ (Finset.univ.erase i.castSucc).erase i.succ,
      (h i.castSucc - h j) / (h i.succ - h j) := by
    apply Finset.prod_pos
    intro j hj
    have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    have hjb := Finset.ne_of_mem_erase hj
    have hja' : (j : ℕ) ≠ (i : ℕ) := fun heq => hja (Fin.ext heq)
    have hjb' : (j : ℕ) ≠ (i : ℕ) + 1 := fun heq => hjb (Fin.ext heq)
    by_cases hlt : (j : ℕ) < (i : ℕ)
    · exact div_pos (sub_pos.mpr (hmono (show j < i.castSucc by exact hlt)))
        (sub_pos.mpr (hmono (show j < i.succ by change (j : ℕ) < (i : ℕ) + 1; omega)))
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (hmono (show i.castSucc < j by change (i : ℕ) < (j : ℕ); omega)))
        (sub_neg.mpr (hmono (show i.succ < j by change (i : ℕ) + 1 < (j : ℕ); omega)))
  linarith only [hp]

theorem finiteWeilNormalizedMomentDual_adjacent_mul_neg {n : ℕ}
    (h : Fin (n + 1) → ℝ) (hmono : StrictMono h) (i : Fin n) :
    finiteWeilNormalizedMomentDual h i.castSucc *
      finiteWeilNormalizedMomentDual h i.succ < 0 := by
  rcases div_neg_iff.mp (finiteWeilNormalizedMomentDual_adjacent_ratio_neg h hmono i) with
    ⟨hb, ha⟩ | ⟨hb, ha⟩
  · exact mul_neg_of_neg_of_pos ha hb
  · exact mul_neg_of_pos_of_neg ha hb

theorem finiteWeilNormalizedMomentDual_last_pos {n : ℕ}
    (h : Fin (n + 1) → ℝ) (hmono : StrictMono h) :
    0 < finiteWeilNormalizedMomentDual h (Fin.last n) := by
  change 0 < ‖finiteWeilMomentWeights h‖⁻¹ *
    ∏ j ∈ Finset.univ.erase (Fin.last n), (h (Fin.last n) - h j)⁻¹
  apply mul_pos (inv_pos.mpr (finiteWeilMomentWeights_norm_pos h hmono.injective))
  apply Finset.prod_pos
  intro j hj
  apply inv_pos.mpr
  apply sub_pos.mpr
  apply hmono
  have hne : (j : ℕ) ≠ n := fun heq => (Finset.ne_of_mem_erase hj) (Fin.ext heq)
  change (j : ℕ) < n
  have := j.isLt
  omega

end RHTower
