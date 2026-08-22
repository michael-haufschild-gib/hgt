import GaloisForLFunctions.HTGeometry.FinitePhaseCharacterTransfer
import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionVariance

/-!
# Products of character combinations and the size of quartic frequencies

The product of two finite character combinations is again one, with frequencies added and
coefficients multiplied, both on the continuous phase torus and in the eighth-root phase model.  The
frequencies occurring in the quartic collision are supported on at most four Boolean points with
entries of absolute value at most two, so those occurring in its square are supported on at most
eight points with entries of absolute value at most four: small enough to be detected modulo eight,
and few enough for fifteen-wise independence.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Product

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {κ κ' : Type*}

theorem finiteTrigLift_mul (P : Finset κ) (Q : Finset κ') (ν : κ → d → ℤ) (μ : κ' → d → ℤ)
    (a : κ → ℂ) (b : κ' → ℂ) (x : d → ℝ) :
    trigLift P ν a x * trigLift Q μ b x =
      trigLift (P ×ˢ Q) (fun pq => ν pq.1 + μ pq.2) (fun pq => a pq.1 * b pq.2) x := by
  rw [trigLift, trigLift, trigLift, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [charLift_add_index]
  ring

end Product

section FiniteProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ κ' : Type*}

theorem charFinite_add_index {m : ℕ} (n n' : (ι → Bool) → ℤ) (c : MonLe ι m → ZMod 8) :
    charFinite (n + n') c = charFinite n c * charFinite n' c := by
  rw [charFinite, charFinite, charFinite, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.add_apply, Int.cast_add]
  ring

theorem trigFinite_mul {m : ℕ} (P : Finset κ) (Q : Finset κ')
    (ν : κ → ((ι → Bool) → ℤ)) (μ : κ' → ((ι → Bool) → ℤ))
    (a : κ → ℂ) (b : κ' → ℂ) (c : MonLe ι m → ZMod 8) :
    trigFinite P ν a c * trigFinite Q μ b c =
      trigFinite (P ×ˢ Q) (fun pq => ν pq.1 + μ pq.2) (fun pq => a pq.1 * b pq.2) c := by
  rw [trigFinite, trigFinite, trigFinite, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [charFinite_add_index]
  ring

end FiniteProduct

section FrequencySize

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem quarticFreq_apply (p : (α × α) × (α × α)) (a : α) :
    quarticFreq p a =
      -(if a = p.1.1 then 1 else 0) - (if a = p.1.2 then 1 else 0) +
        ((if a = p.2.1 then 1 else 0) + (if a = p.2.2 then 1 else 0)) := by
  rw [quarticFreq]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
  ring

theorem ite_zero_one_bounds (P : Prop) [Decidable P] :
    (0 : ℤ) ≤ (if P then 1 else 0) ∧ (if P then (1 : ℤ) else 0) ≤ 1 := by
  split <;> constructor <;> norm_num

theorem abs_quarticFreq_le (p : (α × α) × (α × α)) (a : α) : |quarticFreq p a| ≤ 2 := by
  rw [quarticFreq_apply, abs_le]
  have b1 := ite_zero_one_bounds (a = p.1.1)
  have b2 := ite_zero_one_bounds (a = p.1.2)
  have b3 := ite_zero_one_bounds (a = p.2.1)
  have b4 := ite_zero_one_bounds (a = p.2.2)
  omega

theorem support_quarticFreq_subset (p : (α × α) × (α × α)) :
    (Finset.univ.filter fun a : α => quarticFreq p a ≠ 0) ⊆
      {p.1.1, p.1.2, p.2.1, p.2.2} := by
  intro a ha
  rw [Finset.mem_filter] at ha
  by_contra hcon
  refine ha.2 ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
  rw [quarticFreq_apply]
  rw [if_neg hcon.1, if_neg hcon.2.1, if_neg hcon.2.2.1, if_neg hcon.2.2.2]
  ring

theorem card_support_quarticFreq_le (p : (α × α) × (α × α)) :
    (Finset.univ.filter fun a : α => quarticFreq p a ≠ 0).card ≤ 4 := by
  refine le_trans (Finset.card_le_card (support_quarticFreq_subset p)) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h2 := Finset.card_insert_le p.1.2 ({p.2.1, p.2.2} : Finset α)
  have h3 := Finset.card_insert_le p.2.1 ({p.2.2} : Finset α)
  have h4 : ({p.2.2} : Finset α).card = 1 := Finset.card_singleton _
  omega

theorem support_add_subset (n n' : α → ℤ) :
    (Finset.univ.filter fun a : α => (n + n') a ≠ 0) ⊆
      (Finset.univ.filter fun a : α => n a ≠ 0) ∪
        (Finset.univ.filter fun a : α => n' a ≠ 0) := by
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_contra hcon
  simp only [not_or, not_and, not_not] at hcon
  have h1 : n a = 0 := hcon.1 (Finset.mem_univ a)
  have h2 : n' a = 0 := hcon.2 (Finset.mem_univ a)
  exact ha.2 (by rw [Pi.add_apply, h1, h2, add_zero])

theorem card_support_add_quarticFreq_le (p q : (α × α) × (α × α)) :
    (Finset.univ.filter fun a : α => (quarticFreq p + quarticFreq q) a ≠ 0).card ≤ 8 := by
  refine le_trans (Finset.card_le_card (support_add_subset _ _)) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_support_quarticFreq_le p
  have h2 := card_support_quarticFreq_le q
  omega

theorem abs_add_quarticFreq_le (p q : (α × α) × (α × α)) (a : α) :
    |(quarticFreq p + quarticFreq q) a| ≤ 4 := by
  rw [Pi.add_apply, abs_le]
  have h1 := abs_quarticFreq_le p a
  have h2 := abs_quarticFreq_le q a
  rw [abs_le] at h1 h2
  omega

end FrequencySize

section ModEight

theorem eq_zero_of_abs_le_seven_of_cast_eq_zero {v : ℤ} (hv : |v| ≤ 7)
    (h : ((v : ℤ) : ZMod 8) = 0) : v = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨t, rfl⟩ := h
  rw [abs_le] at hv
  omega

end ModEight

end GaloisForLFunctions.HTGeometry
