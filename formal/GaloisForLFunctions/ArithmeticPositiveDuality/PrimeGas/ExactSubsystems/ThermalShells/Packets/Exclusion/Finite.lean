import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Sampling

/-! # The upper occupation of a squarefree pair -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion

open Finset _root_.RHTower Occupation
variable {α : Type*}

private theorem two_injective (y : Fin 2 → α) : Function.Injective y ↔ y 0 ≠ y 1 := by
  constructor
  · intro h he
    exact Fin.zero_ne_one (h he)
  · intro h i j he
    fin_cases i <;> fin_cases j <;> first | rfl | exact (h he).elim | exact (h he.symm).elim

variable [Fintype α] [LinearOrder α]

/-- Removing the equal-label diagonal gives twice the unordered pair partition. -/
theorem pair_partition (w : α → ℝ) :
    2*(∑ R : BreadthSubset 2 α, productWeight w R) = (∑ x, w x)^2-∑ x, w x^2 := by
  let d (y : Fin 2 → α) := if y 0=y 1 then tupleWeight w y else 0
  have diag : (∑ y, d y) = ∑ x, w x^2 := by
    have h := Fintype.sum_equiv (finTwoArrowEquiv α) d
      (fun v : α × α => if v.1=v.2 then w v.1*w v.2 else 0)
      (fun y => by simp only [d,tupleWeight,Fin.prod_univ_two]; rfl)
    rw [h,Fintype.sum_prod_type]
    simp only [sum_ite_eq,mem_univ,if_true,sq]
  have off (y : Fin 2 → α) : injectiveTupleWeight w y = tupleWeight w y-d y := by
    by_cases he : y 0 = y 1 <;> simp [injectiveTupleWeight,two_injective,d,he]
  have h := (sum_injectiveTupleWeight 2 α w).symm
  rw [sum_congr rfl (fun y _ => off y),sum_sub_distrib,sum_tupleWeight,diag] at h
  simpa only [productWeight,show ((2:ℕ).factorial:ℝ)=2 by norm_num] using h

private def masked (H : Finset α) (q : α → ℝ) (x : α) := if x ∈ H then q x else 0

private theorem masked_sum (H : Finset α) (q : α → ℝ) :
    (∑ x, masked H q x) = ∑ x ∈ H,q x := by
  simp only [masked,← sum_filter,filter_mem_eq_inter,univ_inter]

private theorem masked_sq (H : Finset α) (q : α → ℝ) :
    (∑ x, masked H q x^2) = ∑ x ∈ H,q x^2 := by
  have eqv x : masked H q x^2 = masked H (fun y => q y^2) x := by
    by_cases hx : x ∈ H <;> simp [masked,hx]
  rw [sum_congr rfl (fun x _ => eqv x),masked_sum]

omit [Fintype α] in
private theorem mask_prod (H : Finset α) (q : α → ℝ) (R : BreadthSubset 2 α) :
    productWeight (masked H q) R = if R.val ⊆ H then productWeight q R else 0 := by
  unfold productWeight masked
  exact prod_ite_zero

/-- The mean count equals the probability of at least one upper occupation plus the
probability of two. Its numerator loses exactly the repeated upper pairs. -/
theorem pair_mean (q : α → ℝ) (hn : ∑ x,q x=1) (H : Finset α) :
    subsetRead q H 2 {1,2} + subsetRead q H 2 {2} =
      2*((∑ x ∈ H,q x)-(∑ x ∈ H,q x^2))/(1-∑ x,q x^2) := by
  have top (R : BreadthSubset 2 α) : upperCount H R ∈ ({2}:Finset ℕ) ↔ R.val ⊆ H := by
    rw [mem_singleton]
    exact (show upperCount H R=2 ↔ upperCount H R=R.val.card by rw [R.property]).trans card_filter_eq_iff
  have low (R : BreadthSubset 2 α) : upperCount H R = 0 ↔ R.val ⊆ Hᶜ := by
    exact card_filter_eq_zero_iff.trans
      ⟨fun he _ hx => mem_compl.mpr (he _ hx),fun he _ hx => mem_compl.mp (he hx)⟩
  have a2 (R : BreadthSubset 2 α) :
      (if upperCount H R ∈ ({2}:Finset ℕ) then productWeight q R else 0) = productWeight (masked H q) R := by
    simp only [mask_prod,top R]
  have a12 (R : BreadthSubset 2 α) :
      (if upperCount H R ∈ ({1,2}:Finset ℕ) then productWeight q R else 0) =
        productWeight q R-productWeight (masked Hᶜ q) R := by
    have hj : upperCount H R ≤ 2 := (card_filter_le _ _).trans_eq R.property
    simp only [mask_prod,← low R,mem_insert,mem_singleton]
    rcases (show upperCount H R=0 ∨ upperCount H R=1 ∨ upperCount H R=2 by omega) with h | h | h <;> simp [h]
  have upperPart := pair_partition (masked H q)
  have lowerPart := pair_partition (masked Hᶜ q)
  rw [masked_sum,masked_sq] at upperPart lowerPart
  have outside (f : α → ℝ) : (∑ x ∈ Hᶜ,f x) = (∑ x,f x)-∑ x ∈ H,f x := by
    have hc : Hᶜ = univ \ H := by ext; simp
    rw [hc]
    linarith only [sum_sdiff (f := f) (subset_univ H)]
  rw [outside q,outside (fun x => q x^2),hn] at lowerPart
  have whole := pair_partition q
  rw [hn,one_pow] at whole
  unfold subsetRead
  rw [sum_congr rfl (fun R _ => a12 R),sum_sub_distrib,sum_congr rfl (fun R _ => a2 R),← add_div,
    ← mul_div_mul_left _ _ (two_ne_zero : (2:ℝ)≠0),mul_add,mul_sub,whole,lowerPart,upperPart]
  congr 1
  ring

#print axioms pair_partition
#print axioms pair_mean

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion
