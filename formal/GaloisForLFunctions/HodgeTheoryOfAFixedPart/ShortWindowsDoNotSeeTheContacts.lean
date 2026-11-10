import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheHodgeIndexHoldsAtEveryScaleOnShortWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts

/-!
# Short windows do not see the contacts

A window of ratio at most `2` contains no pair of degree points in divisibility. On such a window
the pairing of the normal form is the same for every system of contact weights
(`combFormW_eq_combForm_of_window`), and the inequality of Castelnuovo and Severi at finite scale
on short windows holds for all of them (`combFormW_ge_of_short`): for the square, for an
integer-norm system, for the weights of a configuration with zeros off the line.

So the inequality on short windows is not selective. A statement of the field that separates the
integers from a fake has to involve a window with a contact, or the flat tail.

The statements at finite scale are statements on windows at a scale: at the bottom of the comb
the counterterm `log(n/2π)` is negative, and the single divisor `γ_2` already has
`2 d₁ d₂ − D·D < 0` (`combForm_singleton_two_neg`).
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-- Two distinct degree points of a window of ratio at most `2` have no contact, for any
weights. -/
theorem contactW_eq_zero_of_window (w : ℕ → ℝ) {N M m n : ℕ} (hM : M ≤ N)
    (hm : m ∈ Ioc N (N + M)) (hn : n ∈ Ioc N (N + M)) (hmn : m ≠ n) : contactW w m n = 0 := by
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have key : ∀ a b : ℕ, N < a → N < b → b ≤ N + M → a ≠ b → ¬ a ∣ b := by
    rintro a b ha hb hb2 hab ⟨k, rfl⟩
    have hk1 : k ≠ 1 := fun h => hab (by rw [h, mul_one])
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have h2 : a * 2 ≤ a * k := Nat.mul_le_mul_left a (by omega)
    omega
  rw [contactW, if_neg (key m n hm1 hn1 hn2 hmn), if_neg (key n m hn1 hm1 hm2 (Ne.symm hmn)),
    add_zero]

/-- **On a window of ratio at most `2` Weil's form on the comb does not depend on the contact
weights.** -/
theorem combFormW_eq_combForm_of_window (w : ℕ → ℝ) {N M : ℕ} (hM : M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) : combFormW w S c = combForm S c := by
  rw [combFormW_eq, Finset.sum_eq_zero fun n hn => Finset.sum_eq_zero fun m hm => by
    rw [contactW_eq_zero_of_window _ hM (hS (Finset.mem_of_mem_erase hm)) (hS hn)
      (Finset.ne_of_mem_erase hm), mul_zero], sub_zero]

/-- **The inequality on short windows holds for every system of contact weights.** -/
theorem combFormW_ge_of_short (w : ℕ → ℝ) {N M : ℕ} (hNM : 18 * M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) : 1 / 50 * ∑ n ∈ S, c n ^ 2 ≤ combFormW w S c := by
  rw [combFormW_eq_combForm_of_window w (by omega) hS c]
  exact combForm_ge_of_short hNM hS c

/-! ### The bottom of the comb -/

/-- **The normal form is not nonnegative on every finite set.** The divisor `c·γ_2` has
`2 d₁ d₂ − D·D = c²(1 − log π) < 0`. -/
theorem combForm_singleton_two_neg {c : ℝ} (hc : c ≠ 0) :
    combForm {2} (fun _ => c) < 0 := by
  have hπ : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    exact lt_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)) Real.pi_gt_three
  have hlog : Real.log ((2 : ℝ) / (2 * Real.pi)) = -Real.log Real.pi := by
    rw [show (2 : ℝ) / (2 * Real.pi) = Real.pi⁻¹ by field_simp, Real.log_inv]
  have h1 : combForm {2} (fun _ => c) = c ^ 2 * (1 - Real.log Real.pi) := by
    rw [combForm, combPairing, degOne, degTwo, Finset.sum_singleton, Finset.sum_singleton,
      Finset.sum_singleton, Finset.sum_singleton, Finset.erase_singleton, Finset.sum_empty,
      counterterm]
    push_cast
    rw [hlog]
    ring
  rw [h1]
  have hc2 : 0 < c ^ 2 := by positivity
  nlinarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
