import Mathlib

/-! # Isolating one unit-circle frequency from consecutive samples -/
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
variable {I : Type*} [DecidableEq I]

private def differences (J S : Finset I) (c z : I → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ J, c j * z j ^ n * ∏ l ∈ S, (z j-z l)

private theorem difference_bound (J S : Finset I) (c z : I → ℂ) (δ : ℝ)
    (hz : ∀ j, ‖z j‖ ≤ 1) (n : ℕ)
    (hs : ∀ q ≤ S.card, ‖∑ j ∈ J, c j*z j^(n+q)‖ ≤ δ) :
    ‖differences J S c z n‖ ≤ 2^S.card * δ := by
  induction S using Finset.induction_on generalizing n with
  | empty => simpa [differences] using hs 0 (by simp)
  | @insert l S hl ih =>
    have ha := ih n (fun q hq => hs q (by rw [Finset.card_insert_of_notMem hl]; omega))
    have hb := ih (n+1) (fun q hq => by
      have h := hs (q+1) (by rw [Finset.card_insert_of_notMem hl]; omega)
      simpa only [show n+1+q=n+(q+1) by omega] using h)
    have hid : differences J (insert l S) c z n =
        differences J S c z (n+1) - z l*differences J S c z n := by
      simp only [differences,Finset.prod_insert hl,Finset.mul_sum,←Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
    rw [hid,Finset.card_insert_of_notMem hl,pow_succ]
    have hm : ‖z l*differences J S c z n‖ ≤ 2^S.card*δ := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hz l)).trans ha
    exact (norm_sub_le _ _).trans (by linarith only [hb,hm])

/-- Applying the shifts S−zⱼ at all competing frequencies isolates the
chosen coefficient. Each shift costs a factor of at most two. -/
theorem consecutive_sample_bound (J : Finset I) (c z : I → ℂ) {i : I} (hi : i∈J)
    (hz : ∀ j, ‖z j‖ ≤ 1) {δ : ℝ}
    (hs : ∀ q < J.card, ‖∑ j ∈ J, c j*z j^q‖ ≤ δ) :
    ‖c i‖ * ∏ l ∈ J.erase i, ‖z i-z l‖ ≤ 2^(J.card-1) * δ := by
  have hb := difference_bound J (J.erase i) c z δ hz 0 (fun q hq => by
    rw [Finset.card_erase_of_mem hi] at hq
    simpa only [zero_add] using hs q (by have := Finset.card_pos.mpr ⟨i,hi⟩; omega))
  have he : differences J (J.erase i) c z 0=c i*∏ l ∈ J.erase i, (z i-z l) := by
    simp only [differences,pow_zero,mul_one]
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji,hj⟩) (sub_self (z j)),mul_zero]
    · exact fun h => (h hi).elim
  simpa only [he,norm_mul,norm_prod,Finset.card_erase_of_mem hi] using hb

#print axioms consecutive_sample_bound
end
end GaloisForLFunctions.HTGeometry.ExactContacts
