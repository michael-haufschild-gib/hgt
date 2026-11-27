import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Upper.Cuts
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Upper.Separator

/-! # Number of coincident heat probes from oriented quantile intervals -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper

open Finset Real Set
open GaloisForLFunctions.HTGeometry (expSum)

variable {n : ℕ}

/-- A derivative with the displacement's sign makes each nonempty interval
contribute strictly positively to the difference of the two sums. -/
private theorem positive_difference {A B : Fin (n+1) → ℝ} {F D : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt F (D x) x) (i : Fin (n+1))
    (orient : ∀ x ∈ Ioo (min (A i) (B i)) (top A B i), 0 < side A B i*D x)
    (hne : A i ≠ B i) : 0 < F (A i)-F (B i) := by
  have cont : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨x,hx,sl⟩ := exists_hasDerivAt_eq_slope F D h cont.continuousOn (fun y _ => hd y)
    have sign := orient x (by simpa only [top,min_eq_left h.le,max_eq_right h.le] using hx)
    simp only [side,if_neg h.not_gt,neg_one_mul,neg_pos] at sign
    rw [sl] at sign
    have m := mul_neg_of_neg_of_pos sign (sub_pos.mpr h)
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')] at m
    exact sub_pos.mpr (sub_neg.mp m)
  · obtain ⟨x,hx,sl⟩ := exists_hasDerivAt_eq_slope F D h cont.continuousOn (fun y _ => hd y)
    have sign := orient x (by simpa only [top,min_eq_right h.le,max_eq_left h.le] using hx)
    simp only [side,if_pos h,one_mul] at sign
    rw [sl] at sign
    have m := mul_pos sign (sub_pos.mpr h)
    rwa [div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')] at m

/-- Coincident primitive heat probes cannot outnumber the sign changes of the
ordered displacements between two different strictly increasing equal-weight lists. -/
theorem variation {A B : Fin (n+1) → ℝ} (ha : StrictMono A) (hb : StrictMono B) (different : A ≠ B)
    (T : Finset ℝ) (equal : ∀ t ∈ T, ∑ i, primitive t (A i)=∑ i, primitive t (B i)) :
    T.card ≤ (edges A B).card := by
  classical
  by_contra! few
  let C := edges A B
  let a (j : Fin C.card) := top A B ((C.orderEmbOfFin rfl) j).castSucc
  have ordered : StrictMono a := fun _ _ h => top_mono ha hb ((C.orderEmbOfFin rfl).strictMono h)
  obtain ⟨U,sub,size⟩ := T.exists_subset_card_eq (show C.card+1 ≤ T.card from few)
  let t := U.orderEmbOfFin size
  obtain ⟨c,sign⟩ := separator a t ordered t.strictMono
  let F (x : ℝ) := side A B 0*∑ j, c j*primitive (t j) x
  let D (x : ℝ) := side A B 0*expSum c t x
  have deriv (x : ℝ) : HasDerivAt F (D x) x :=
    (HasDerivAt.fun_sum (u := univ) fun j _ => (primitive_deriv (t j) x).const_mul (c j)).const_mul _
  have orient (i : Fin (n+1)) (x : ℝ) (hx : x∈Ioo (min (A i) (B i)) (top A B i)) :
      0 < side A B i*D x := by
    let P := ∏ j, (a j-x)
    have product : P=∏ j ∈ C, (top A B j.castSucc-x) := by
      exact ((C.orderIsoOfFin rfl).toEquiv.prod_comp (fun j : C => top A B j.val.castSucc-x)).trans
        (prod_coe_sort C (fun j => top A B j.castSucc-x))
    have hp := cut_sign ha hb i hx
    rw [← product] at hp
    have outside : x∉Set.range a := by
      rintro ⟨j,rfl⟩
      have zero : P=0 := prod_eq_zero (mem_univ j) (sub_self _)
      rw [zero,mul_zero] at hp
      exact (lt_irrefl _ hp)
    have combine : 0 < (side A B i*D x)*(P*P) := by
      calc
        0 < (expSum c t x*P)*((side A B 0*side A B i)*P) := mul_pos (sign x outside) hp
        _ = _ := by unfold D; ring
    exact pos_of_mul_pos_left combine (mul_self_nonneg _)
  obtain ⟨i,unequal⟩ : ∃ i, A i ≠ B i := by
    by_contra! same
    exact different (funext same)
  have pos (j) (h : A j ≠ B j) := positive_difference deriv j (orient j) h
  have total : 0 < ∑ j, (F (A j)-F (B j)) := by
    refine sum_pos' (fun j _ => ?_) ⟨i,mem_univ i,pos i unequal⟩
    by_cases h : A j=B j
    · rw [h,sub_self]
    · exact (pos j h).le
  have evaluate (Y : Fin (n+1) → ℝ) : (∑ i, F (Y i))=side A B 0*∑ j, c j*∑ i, primitive (t j) (Y i) := by
    simp only [F,← mul_sum]
    congr 1
    rw [sum_comm]
    simp only [mul_sum]
  rw [sum_sub_distrib,evaluate,evaluate] at total
  have heq (j) := equal (t j) (sub (U.orderEmbOfFin_mem size j))
  simp only [heq,sub_self,lt_irrefl] at total

#print axioms variation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Upper
