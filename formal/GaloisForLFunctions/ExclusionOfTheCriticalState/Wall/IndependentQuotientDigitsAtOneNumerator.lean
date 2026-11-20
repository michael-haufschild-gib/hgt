import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePeriodGramOfOddPrimeQuotients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.BigOperators.Field

/-!
# Independent quotient digits at a common numerator

Choose one denominator 2ⁱdᵢ at each dyadic order and an odd common
multiple U of the dᵢ. On each progression H+qU, the q-bit at position i
reverses the i-th quotient sign and preserves all lower ones. The signs
are therefore independent and fair over a single block of 2ᵏ values of q,
with any initial numerator H.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open Finset
noncomputable section
open scoped Classical

/-- Toggling a numerator bit reverses its own quotient digit and preserves all lower ones. -/
theorem quotientSign_dyadic_translate {U d i j : ℕ} (hu : Odd U) (hd : d∣U) (hij : i≤j) (H q : ℕ) :
    quotientSign (2^i*d) (H+(2^j+q)*U) =
      if i=j then -quotientSign (2^i*d) (H+q*U) else quotientSign (2^i*d) (H+q*U) := by
  obtain ⟨v,hv⟩ := hd
  have hU : 0<U := by obtain ⟨l,hl⟩ := hu; omega
  have hdp : 0<d := Nat.pos_of_dvd_of_pos ⟨v,hv⟩ hU
  have hvodd : Odd v := by
    rw [hv] at hu
    exact (Nat.odd_mul.mp hu).2
  have hpow : 2^j=2^i*2^(j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  have shift : H+(2^j+q)*U=(H+q*U)+(2^i*d)*(2^(j-i)*v) := by rw [hv,hpow]; ring
  rw [shift,quotientSign_add_multiple (by positivity : 0<2^i*d)]
  by_cases he : i=j
  · subst j
    simp [hvodd.neg_one_pow]
  · obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (show j-i≠0 by omega)
    have even : Even (2^(j-i)*v) := ⟨2^l*v,by rw [hl,pow_succ]; ring⟩
    simp [he,even.neg_one_pow]

/-- Exact product law for arbitrary observables of the quotient signs.
It holds separately for every starting numerator and odd step U. -/
theorem quotientSign_product_law {R : Type*} [CommSemiring R] (k H U : ℕ)
    (d : ℕ → ℕ) (hu : Odd U) (hd : ∀ i<k, d i∣U) (F : ℕ → ℝ → R) :
    ∑ q ∈ range (2^k), ∏ i ∈ range k, F i (quotientSign (2^i*d i) (H+q*U)) =
      ∏ i ∈ range k, (F i 1 + F i (-1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let z (i q : ℕ) := quotientSign (2^i*d i) (H+q*U)
    let W (q : ℕ) := ∏ i ∈ range k, F i (z i q)
    have hs (q : ℕ) : W (2^k+q)=W q := by
      refine prod_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      have he := quotientSign_dyadic_translate hu (hd i (by omega)) hi'.le H q
      rw [if_neg hi'.ne] at he
      exact congrArg (F i) he
    have hl (q : ℕ) : z k (2^k+q)= -z k q := by
      exact (quotientSign_dyadic_translate hu (hd k (Nat.lt_succ_self _)) (le_refl k) H q).trans
        (if_pos (rfl : k=k))
    have values (q : ℕ) : z k q=1 ∨ z k q= -1 := by
      unfold z quotientSign
      rw [neg_one_pow_eq_pow_mod_two]
      have h := Nat.mod_lt ((H+q*U)/(2^k*d k)) (by decide : 0<2)
      rcases (show ((H+q*U)/(2^k*d k))%2=0 ∨ ((H+q*U)/(2^k*d k))%2=1 by omega) with he|he <;> simp [he]
    have fold (q : ℕ) : W q*F k (z k q) + W (2^k+q)*F k (z k (2^k+q)) =
        W q*(F k 1+F k (-1)) := by
      rw [hs,hl,mul_add]
      rcases values q with h|h
      · rw [h]
      · rw [h,neg_neg,add_comm]
    rw [pow_succ,Nat.mul_two,sum_range_add]
    simp only [prod_range_succ]
    change (∑ q ∈ range (2^k), W q*F k (z k q)) +
      (∑ q ∈ range (2^k), W (2^k+q)*F k (z k (2^k+q))) = _
    rw [← sum_add_distrib,sum_congr rfl (fun q _ => fold q),← sum_mul]
    exact congrArg (fun t => t*(F k 1+F k (-1))) (ih (fun i hi => hd i (by omega)))


/-- Unspecified dyadic orders supply exactly one free binary choice each.
The specified signs can be observed at widely separated dyadic orders. -/
theorem quotientSign_selected_product {R : Type*} [CommSemiring R] (k H U : ℕ)
    (d : ℕ → ℕ) (hu : Odd U) (hd : ∀ i<k, d i∣U) {A : Finset ℕ}
    (ha : A ⊆ range k) (F : ℕ → ℝ → R) :
    ∑ q ∈ range (2^k), ∏ i ∈ A, F i (quotientSign (2^i*d i) (H+q*U)) =
      (2:R)^(k-A.card)*∏ i ∈ A, (F i 1+F i (-1)) := by
  let G (i : ℕ) (x : ℝ) : R := if i∈A then F i x else 1
  have h := quotientSign_product_law k H U d hu hd G
  have trim (x : ℕ → ℝ) : (∏ i ∈ range k, G i (x i)) = ∏ i ∈ A, F i (x i) := by
    have outside (i : ℕ) (_ : i∈range k) (hi : i∉A) : G i (x i)=1 := if_neg hi
    rw [← prod_subset ha outside]
    exact prod_congr rfl fun i hi => if_pos hi
  have inner (q : ℕ) : (∏ i ∈ range k, G i (quotientSign (2^i*d i) (H+q*U))) =
      ∏ i ∈ A, F i (quotientSign (2^i*d i) (H+q*U)) := trim _
  rw [sum_congr rfl (fun q _ => inner q)] at h
  refine h.trans ?_
  let f (i : ℕ) := G i 1+G i (-1)
  have hs : (∏ i ∈ range k \ A, f i)*(∏ i ∈ A, f i)=∏ i ∈ range k, f i := prod_sdiff ha
  change (∏ i ∈ range k, f i) = _
  rw [← hs,prod_congr rfl (show ∀ i∈range k \ A, f i=(2:R) from fun i hi => by
    norm_num [f,G,(mem_sdiff.mp hi).2]),prod_const,card_sdiff_of_subset ha,card_range]
  congr 1
  exact prod_congr rfl fun i hi => by simp [f,G,hi]

/-- Every prescribed vector of quotient parities occurs at exactly one
common numerator in each 2ᵏ-term progression, including after arbitrary shifts. -/
theorem quotientSign_pattern_count (k H U : ℕ) (d : ℕ → ℕ) (hu : Odd U)
    (hd : ∀ i<k, d i∣U) (s : ℕ → Bool) :
    ((range (2^k)).filter fun q => ∀ i∈range k,
      quotientSign (2^i*d i) (H+q*U)=(if s i then -1 else 1)).card = 1 := by
  let F (i : ℕ) (x : ℝ) : ℕ := if x=(if s i then -1 else 1) then 1 else 0
  have h := quotientSign_product_law k H U d hu hd F
  have unit (i : ℕ) : F i 1+F i (-1)=1 := by cases he : s i <;> norm_num [F,he]
  simp only [unit,prod_const_one] at h
  let hit (q : ℕ) := ∀ i∈range k, quotientSign (2^i*d i) (H+q*U)=(if s i then -1 else 1)
  have ht (q : ℕ) : (∏ i ∈ range k, F i (quotientSign (2^i*d i) (H+q*U))) = if hit q then 1 else 0 := by
    by_cases hh : hit q
    · rw [if_pos hh]
      exact prod_eq_one fun i hi => if_pos (hh i hi)
    · rw [if_neg hh]
      change ¬ ∀ i∈range k, quotientSign (2^i*d i) (H+q*U)=(if s i then -1 else 1) at hh
      push Not at hh
      obtain ⟨i,hi,hne⟩ := hh
      exact prod_eq_zero hi (if_neg hne)
  rw [sum_congr rfl (fun q _ => ht q)] at h
  exact (sum_boole (R:=ℕ) hit (range (2^k))).symm.trans h

/-- Exponential moment of an arbitrary signed combination of the quotient
digits at their common numerator. The left side retains all coefficients. -/
theorem quotientSign_exp_moment (k H U : ℕ) (d : ℕ → ℕ) (hu : Odd U)
    (hd : ∀ i<k, d i∣U) (a : ℕ → ℝ) :
    ∑ q ∈ range (2^k), Real.exp (∑ i ∈ range k, a i*quotientSign (2^i*d i) (H+q*U)) =
      ∏ i ∈ range k, (Real.exp (a i)+Real.exp (-a i)) := by
  have h := quotientSign_product_law k H U d hu hd (fun i x => Real.exp (a i*x))
  simpa only [Real.exp_sum,mul_one,mul_neg_one] using h

/-- A signed sum of quotient digits along the odd progression. -/
def progressionQuotientSum (k H U : ℕ) (d : ℕ → ℕ) (a : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i ∈ range k, a i*quotientSign (2^i*d i) (H+q*U)

private theorem quotientExp_sum_le (k H U : ℕ) (d : ℕ → ℕ) (hu : Odd U)
    (hd : ∀ i<k, d i∣U) (a : ℕ → ℝ) :
    ∑ q ∈ range (2^k), Real.exp (progressionQuotientSum k H U d a q) ≤
      (2:ℝ)^k * Real.exp ((∑ i ∈ range k, (a i)^2)/2) := by
  rw [show (∑ q ∈ range (2^k), Real.exp (progressionQuotientSum k H U d a q)) = _
    from quotientSign_exp_moment k H U d hu hd a]
  calc
    _ ≤ ∏ i ∈ range k, 2*Real.exp ((a i)^2/2) := by
      refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
      have h := Real.cosh_le_exp_half_sq (a i)
      rw [Real.cosh_eq] at h
      linarith only [h]
    _ = _ := by rw [prod_mul_distrib,prod_const,card_range,← Real.exp_sum,← sum_div]

private theorem quotient_tail_from_exp (k H U : ℕ) (d : ℕ → ℕ) (hu : Odd U)
    (hd : ∀ i<k, d i∣U) (a : ℕ → ℝ) (b : ℝ) :
    (((range (2^k)).filter fun q => b≤progressionQuotientSum k H U d a q).card : ℝ) ≤
      (2:ℝ)^k*Real.exp ((∑ i ∈ range k, (a i)^2)/2-b) := by
  let S := (range (2^k)).filter fun q => b≤progressionQuotientSum k H U d a q
  have h : (S.card:ℝ)*Real.exp b ≤ (2:ℝ)^k * Real.exp ((∑ i ∈ range k, (a i)^2)/2) := calc
    _ = ∑ _ ∈ S, Real.exp b := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ q ∈ S, Real.exp (progressionQuotientSum k H U d a q) :=
      sum_le_sum fun q hq => Real.exp_le_exp.mpr (mem_filter.mp hq).2
    _ ≤ ∑ q ∈ range (2^k), Real.exp (progressionQuotientSum k H U d a q) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (Real.exp_pos _).le
    _ ≤ _ := quotientExp_sum_le k H U d hu hd a
  rw [Real.exp_sub,←mul_div_assoc]
  exact (le_div_iff₀ (Real.exp_pos b)).mpr h

/-- Two opposite excursions at the very same numerator. The cost is the
squared norm of the signed difference of the two coefficient vectors,
so overlapping support and its covariance remain in the estimate. -/
theorem same_numerator_opposite_quotient_tail (k H U : ℕ) (d : ℕ → ℕ) (hu : Odd U)
    (hd : ∀ i<k, d i∣U) (a b : ℕ → ℝ) (s t : ℝ) {l v : ℝ} (hl : 0≤l) (hv : 0≤v) :
    (((range (2^k)).filter fun q => s≤progressionQuotientSum k H U d a q ∧
      progressionQuotientSum k H U d b q≤ -t).card : ℝ) ≤
      (2:ℝ)^k * Real.exp ((∑ i ∈ range k, (l*a i-v*b i)^2)/2-(l*s+v*t)) := by
  let c (i : ℕ) := l*a i-v*b i
  have linear (q : ℕ) : progressionQuotientSum k H U d c q =
      l*progressionQuotientSum k H U d a q-v*progressionQuotientSum k H U d b q := by
    simp only [progressionQuotientSum,c,mul_sum,← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  apply le_trans _ (quotient_tail_from_exp k H U d hu hd c (l*s+v*t))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro q hq
  obtain ⟨hmem,ha,hb⟩ := mem_filter.mp hq
  apply mem_filter.mpr ⟨hmem,?_⟩
  rw [linear]
  linarith only [mul_le_mul_of_nonneg_left ha hl,mul_le_mul_of_nonneg_left hb hv]

#print axioms same_numerator_opposite_quotient_tail

#print axioms quotientSign_product_law
#print axioms quotientSign_selected_product
#print axioms quotientSign_pattern_count
#print axioms quotientSign_exp_moment
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
