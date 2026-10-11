import GaloisForLFunctions.RHTower.WeilLogShiftNodalPrefix
import Mathlib.Order.Interval.Finset.Fin

/-! Every proper cumulative nodal sum has its forced strict alternating sign. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilMomentWeights_prefix_pos {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hmono : StrictMono h) (i : Fin n) :
    0 < (-1 : ℝ) ^ (n - (i : ℕ)) *
      ∑ j ∈ Finset.Iic i.castSucc, finiteWeilMomentWeights h j := by
  have hproper : Finset.Iic i.castSucc ≠ (Finset.univ : Finset (Fin (n + 1))) := by
    intro e
    have ht : Fin.last n ∈ Finset.Iic i.castSucc := by rw [e]; exact Finset.mem_univ _
    have ht' := Finset.mem_Iic.mp ht
    have ht'' : n ≤ (i : ℕ) := ht'
    omega
  have hp := finiteWeilNodalPrefix_pos Finset.univ (Finset.Iic i.castSucc) h
    hmono.injective.injOn (Finset.subset_univ _)
    ⟨i.castSucc, Finset.mem_Iic.mpr le_rfl⟩ hproper (by
      intro a ha b hb hnot
      simp only [Finset.mem_Iic] at ha hnot
      exact hmono (lt_of_le_of_lt ha (lt_of_not_ge hnot)))
  simpa [finiteWeilMomentWeights, Fin.card_Iic] using hp

theorem finiteWeilNormalizedMomentDual_prefix_pos {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hmono : StrictMono h) (i : Fin n) :
    0 < (-1 : ℝ) ^ (n - (i : ℕ)) *
      ∑ j ∈ Finset.Iic i.castSucc, finiteWeilNormalizedMomentDual h j := by
  change 0 < (-1 : ℝ) ^ (n - (i : ℕ)) *
    ∑ j ∈ Finset.Iic i.castSucc, ‖finiteWeilMomentWeights h‖⁻¹ * finiteWeilMomentWeights h j
  rw [← Finset.mul_sum]
  have hp := mul_pos (inv_pos.mpr (finiteWeilMomentWeights_norm_pos h hmono.injective))
    (finiteWeilMomentWeights_prefix_pos h hmono i)
  simpa only [mul_left_comm] using hp

theorem finiteWeilMomentWeights_prefix_adjacent_mul_neg {n : ℕ}
    (h : Fin (n + 2) → ℝ) (hmono : StrictMono h) (i : Fin n) :
    (∑ j ∈ Finset.Iic i.castSucc.castSucc, finiteWeilMomentWeights h j) *
      (∑ j ∈ Finset.Iic i.succ.castSucc, finiteWeilMomentWeights h j) < 0 := by
  have hleft := finiteWeilMomentWeights_prefix_pos h hmono i.castSucc
  have hright := finiteWeilMomentWeights_prefix_pos h hmono i.succ
  have he : n + 1 - (i.castSucc : ℕ) = n + 1 - (i.succ : ℕ) + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  rw [he, pow_succ] at hleft
  rcases neg_one_pow_eq_or ℝ (n + 1 - (i.succ : ℕ)) with hp | hp
  · rw [hp] at hleft hright
    nlinarith
  · rw [hp] at hleft hright
    nlinarith

end RHTower
