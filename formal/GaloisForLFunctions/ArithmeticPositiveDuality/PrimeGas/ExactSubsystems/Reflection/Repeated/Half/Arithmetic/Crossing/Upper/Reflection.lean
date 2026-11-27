import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Upper.Variation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow

/-! # The sharp upper bound for strictly ordered centered energy levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper

open Finset Real Set

variable {n : ℕ}

private def mirror (A : Fin (n+1) → ℝ) (i : Fin (n+1)) := -A i.rev

private theorem palindrome (A : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    side A (mirror A) i.rev=side A (mirror A) i := by
  have flip : -A i < A i.rev ↔ -A i.rev < A i := by
    constructor <;> intro h <;> linarith only [h]
  simp only [side,mirror,Fin.rev_rev,flip]
  split_ifs <;> rfl

/-- For even dimension the two middle displacements have equal orientation. -/
private theorem edge_bound (A : Fin (n+1) → ℝ) : (edges A (mirror A)).card ≤ 2*(n/2) := by
  by_cases even : n%2=0
  · have le := card_le_univ (edges A (mirror A))
    rw [Fintype.card_fin] at le
    omega
  · let j : Fin n := ⟨n/2,by omega⟩
    have mid : j.castSucc.rev=j.succ := by
      apply Fin.ext
      simp only [Fin.val_rev,Fin.val_castSucc,Fin.val_succ,j]
      omega
    have no : j∉edges A (mirror A) := by
      intro h
      exact (mem_filter.mp h).2 (mid ▸ (palindrome A j.castSucc).symm)
    have sub : edges A (mirror A) ⊆ univ.erase j := by
      intro i hi; exact mem_erase.mpr ⟨fun eq => no (eq ▸ hi),mem_univ _⟩
    have le := Finset.card_le_card sub
    rw [card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin] at le
    omega

private theorem sum_mirror (A : Fin (n+1) → ℝ) (f : ℝ → ℝ) :
    (∑ i, f (mirror A i))=∑ i, f (-A i) := Equiv.sum_comp Fin.revPerm (fun i => f (-A i))

private theorem odd_neg (A : Fin (n+1) → ℝ) (t : ℝ) : oddTrace A (-t)= -oddTrace A t := by
  simp only [oddTrace,oddTerm,neg_neg,← sum_neg_distrib,neg_sub]

private theorem equal_at {A : Fin (n+1) → ℝ} (mean : ∑ i, A i=0) {t : ℝ} (hz : oddTrace A t=0) :
    (∑ i, primitive t (A i))=∑ i, primitive t (mirror A i) := by
  rw [sum_mirror A (primitive t)]
  by_cases h : t=0
  · subst t; simp [primitive,sum_neg_distrib,mean]
  · simp only [primitive,if_neg h,← sum_div]
    congr 1
    simp only [oddTrace,oddTerm,sum_sub_distrib,sub_eq_zero] at hz
    simpa only [mul_neg,neg_mul] using hz

/-- A strictly increasing centered asymmetric spectrum of \(N\) distinct real
levels cannot have \(\lfloor(N-1)/2\rfloor\) distinct positive blind temperatures. -/
theorem reflected_bound (A : Fin (n+1) → ℝ) (ha : StrictMono A) (mean : ∑ i, A i=0)
    {u : ℝ} (detected : oddTrace A u ≠ 0) (Z : Finset ℝ) (hZ : ∀ t ∈ Z, 0 < t ∧ oddTrace A t=0) :
    Z.card+1 ≤ n/2 := by
  classical
  have mono : StrictMono (mirror A) := fun _ _ h => neg_lt_neg (ha (Fin.rev_lt_rev.mpr h))
  have unequal : A ≠ mirror A := by
    intro eq
    have reverse := sum_mirror A (oddTerm u)
    rw [← eq] at reverse
    have antisym (x : ℝ) : oddTerm u (-x)= -oddTerm u x := by
      simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
    simp only [antisym,sum_neg_distrib] at reverse
    exact detected (show (∑ i, oddTerm u (A i))=0 by linarith only [reverse])
  let neg := Z.image (fun t => -t)
  let T := insert 0 (Z ∪ neg)
  have hn {t : ℝ} (h : t∈neg) : t < 0 ∧ oddTrace A t=0 := by
    obtain ⟨w,hw,rfl⟩ := mem_image.mp h
    exact ⟨neg_neg_of_pos (hZ w hw).1,by rw [odd_neg,(hZ w hw).2,neg_zero]⟩
  have dis : Disjoint Z neg := Finset.disjoint_left.mpr fun _ h₁ h₂ => (hn h₂).1.not_gt (hZ _ h₁).1
  have zero : 0∉Z ∪ neg := fun h => (mem_union.mp h).elim
    (fun h₁ => lt_irrefl _ (hZ _ h₁).1) (fun h₂ => lt_irrefl _ (hn h₂).1)
  have count : T.card=2*Z.card+1 := by
    rw [show T=insert 0 (Z∪neg) from rfl,card_insert_of_notMem zero,card_union_eq_card_add_card.mpr dis,
      show neg.card=Z.card from card_image_of_injective _ neg_injective,two_mul]
  have bound := variation ha mono unequal T (fun t ht => equal_at mean (by
    rcases mem_insert.mp ht with rfl | h
    · exact odd_zero A
    · exact (mem_union.mp h).elim (fun h₁ => (hZ t h₁).2) (fun h₂ => (hn h₂).2)))
  have upper := edge_bound A
  omega

#print axioms reflected_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper
