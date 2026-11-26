import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Collision

/-! # The marked coordinates of independent finite draws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset _root_.RHTower
variable {α : Type*} [Fintype α] [DecidableEq α]

def pattern {m : ℕ} (H : Finset α) (y : Fin m → α) := univ.filter fun i => y i ∈ H

/-- Binomial atom, with zero mass outside the count range. -/
def bin (m j : ℕ) (p : ℝ) := (m.choose j:ℝ)*p^j*(1-p)^(m-j)

def binEvent (m : ℕ) (B : Finset ℕ) (p : ℝ) := ∑ j ∈ B, bin m j p

def counts (m : ℕ) (H : Finset α) (B : Finset ℕ) : Finset (Fin m → α) :=
  univ.filter fun y => (pattern H y).card ∈ B

private theorem pattern_mass (q : α → ℝ) (hn : ∑ x, q x = 1) (H : Finset α) {m : ℕ} (A : Finset (Fin m)) :
    (∑ y : Fin m → α, if pattern H y = A then tupleWeight q y else 0) =
      (∑ x ∈ H,q x)^A.card*(1-∑ x ∈ H,q x)^(m-A.card) := by
  classical
  let g (i : Fin m) (x : α) := if (i ∈ A ↔ x ∈ H) then q x else 0
  have hp (y : Fin m → α) : (∏ i, g i (y i)) = if pattern H y = A then tupleWeight q y else 0 := by
    simp only [g,prod_ite_zero,mem_univ,forall_const,tupleWeight]
    have he : (∀ i, i ∈ A ↔ y i ∈ H) ↔ pattern H y = A := by
      rw [Finset.ext_iff]
      simp only [pattern,mem_filter,mem_univ,true_and]
      exact forall_congr' fun _ => Iff.comm
    simp only [he]
  have outside : (∑ x ∈ univ \ H,q x) = 1-∑ x ∈ H,q x := by
    have h := sum_sdiff (f := q) (subset_univ H)
    linarith only [h,hn]
  have hs (i : Fin m) : (∑ x, g i x) = if i ∈ A then ∑ x ∈ H,q x else 1-∑ x ∈ H,q x := by
    by_cases hi : i ∈ A
    · simp [g,hi]
    · rw [if_neg hi,← outside,sdiff_eq_filter,sum_filter]
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ H <;> simp [g,hi,hx]
  have ha : univ.filter (· ∈ A) = A := by ext; simp
  have hb : univ.filter (fun i => i ∉ A) = univ \ A := by ext; simp
  calc
    _ = ∑ y : Fin m → α, ∏ i, g i (y i) := sum_congr rfl fun y _ => (hp y).symm
    _ = ∏ i, ∑ x, g i x := (Fintype.prod_sum g).symm
    _ = _ := by
      simp only [hs,prod_ite,ha,hb,prod_const,card_sdiff_of_subset (subset_univ A),card_univ,Fintype.card_fin]

/-- The probability for any event in the number of upper positions is exactly binomial. -/
theorem iid_count (q : α → ℝ) (hn : ∑ x, q x = 1) (H : Finset α) (m : ℕ) (B : Finset ℕ) :
    (∑ y ∈ counts m H B, tupleWeight q y) = binEvent m B (∑ x ∈ H,q x) := by
  classical
  have one (j : ℕ) : (∑ y : Fin m → α, if (pattern H y).card = j then tupleWeight q y else 0) =
      bin m j (∑ x ∈ H,q x) := by
    let P := (univ : Finset (Fin m)).powersetCard j
    have grouped y : (∑ A ∈ P, if pattern H y = A then tupleWeight q y else 0) =
        if (pattern H y).card = j then tupleWeight q y else 0 := by
      simp [P,mem_powersetCard]
    rw [← sum_congr rfl (fun y _ => grouped y),sum_comm]
    calc _ = ∑ A ∈ P, (∑ x ∈ H,q x)^j*(1-∑ x ∈ H,q x)^(m-j) := by
               apply sum_congr rfl
               intro A hA
               rw [pattern_mass q hn H A,(mem_powersetCard.mp hA).2]
         _ = _ := by simp [P,bin,mul_assoc]
  unfold binEvent
  simp only [← one,counts,sum_filter,sum_comm (s := B) (t := univ)]
  apply sum_congr rfl
  intro y _
  simp

#print axioms iid_count

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
