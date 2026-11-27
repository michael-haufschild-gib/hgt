import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Greedy

/-! # Optimal occupations on a pinned coordinate and its adjacent half-spaces -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {c : I → ℕ} {m : ℕ}

def reserve (i : I) (k : ℕ) (j : I) := if i=j then k else 0

def limit (c : I → ℕ) (i : I) (k : ℕ) (j : I) := if i=j then k else c j

def ordinary (e : I → ℝ) (c : I → ℕ) (m : ℕ) (i : I) := min (c i) (m-before e c i)

def sliceCost (e : I → ℝ) (c : I → ℕ) (m : ℕ) (i : I) (k : ℕ) :=
  boxCost e (reserve i k) (limit c i k) m

theorem original_fill (e : I → ℝ) (c : I → ℕ) (m : ℕ) :
    fillCount e 0 c m = ordinary e c m := by
  funext i
  simp [fillCount,ordinary]

theorem original_minimum (e : I → ℝ) (he : Function.Injective e) (w : State c m) :
    ∃ x : State c m, count x = ordinary e c m ∧
      ∀ y : State c m, linearCost e (count x) ≤ linearCost e (count y) := by
  have allFit (y : State c m) : Fits 0 c y := fun j => ⟨Nat.zero_le _,count_cap y j⟩
  obtain ⟨x,_,hfill,hcost,hh⟩ := greedy_minimum e he 0 c (fun _ => le_rfl) w (allFit w)
  exact ⟨x,hfill.trans (original_fill e c m),fun y => hcost.le.trans (hh y (allFit y))⟩

omit [Fintype I] in
private theorem bound_limit {i : I} {k : ℕ} (h : k ≤ c i) (j : I) : limit c i k j ≤ c j := by
  by_cases hj : i=j
  · subst j; simpa [limit] using h
  · simp only [limit,if_neg hj,le_rfl]

private theorem fits_reserve (x : State c m) (i : I) (k : ℕ) (h : k ≤ count x i) :
    Fits (reserve i k) c x := by
  intro j
  refine ⟨?_,count_cap x j⟩
  by_cases hj : i=j
  · subst j; simpa [reserve] using h
  · simp only [reserve,if_neg hj,Nat.zero_le]

private theorem fits_limit (x : State c m) (i : I) (k : ℕ) (h : count x i ≤ k) :
    Fits 0 (limit c i k) x := by
  intro j
  refine ⟨Nat.zero_le _,?_⟩
  by_cases hj : i=j
  · subst j; simpa [limit] using h
  · simpa only [limit,if_neg hj] using count_cap x j

/-- Both the attained energy and the extremal bound of a pinned slice come from its fill formula. -/
theorem slice_minimum (e : I → ℝ) (he : Function.Injective e) (x : State c m) (i : I) (k : ℕ)
    (h : count x i = k) :
    ∃ y : State c m, count y i = k ∧ linearCost e (count y) = sliceCost e c m i k ∧
      sliceCost e c m i k ≤ linearCost e (count x) := by
  have hcap := bound_limit (c := c) (h ▸ count_cap x i)
  have valid : Fits (reserve i k) (limit c i k) x := fun j =>
    ⟨(fits_reserve x i k h.ge j).1,(fits_limit x i k h.le j).2⟩
  obtain ⟨y,hy,_,hcost,hmin⟩ := greedy_minimum e he _ _ hcap x valid
  have eqy := hy i
  simp [reserve,limit] at eqy
  exact ⟨y,le_antisymm eqy.2 eqy.1,hcost,hmin x valid⟩

private theorem before_ext (e : I → ℝ) (f d : I → ℕ) (i : I) (h : ∀ j, j ≠ i → f j = d j) :
    before e f i = before e d i :=
  sum_congr rfl fun j hj => h j (mem_erase.mp (mem_filter.mp hj).1).1

/-- Raising a floor past the original minimizer pins the new minimizer exactly at that floor. -/
theorem above_wall (e : I → ℝ) (he : Function.Injective e) (x : State c m) (i : I) (k : ℕ)
    (hfree : ordinary e c m i < k) (hx : k ≤ count x i) :
    ∃ y : State c m, count y i = k ∧ linearCost e (count y) ≤ linearCost e (count x) := by
  have valid := fits_reserve x i k hx
  obtain ⟨y,_,hf,hcost,hmin⟩ := greedy_minimum e he _ _ (fun _ => le_rfl) x valid
  refine ⟨y,?_,hcost.le.trans (hmin x valid)⟩
  have pref := before_ext e (fun j => c j-reserve i k j) c i
    (fun j hj => by simp only [reserve,if_neg hj.symm,Nat.sub_zero])
  have eqy := congrFun hf i
  have cap := hx.trans (count_cap x i)
  have sz : (∑ j, reserve i k j) = k := by simp only [reserve,sum_ite_eq,mem_univ,if_true]
  rw [fillCount,pref,sz] at eqy
  simp [reserve] at eqy
  unfold ordinary at hfree
  omega

/-- Lowering a ceiling below the original minimizer pins the new minimizer at that ceiling. -/
theorem below_wall (e : I → ℝ) (he : Function.Injective e) (x : State c m) (i : I) (k : ℕ)
    (hfree : k < ordinary e c m i) (hx : count x i ≤ k) :
    ∃ y : State c m, count y i = k ∧ linearCost e (count y) ≤ linearCost e (count x) := by
  have valid := fits_limit x i k hx
  have cap : k ≤ c i := hfree.le.trans (min_le_left _ _)
  obtain ⟨y,_,hf,hcost,hmin⟩ := greedy_minimum e he _ _ (bound_limit cap) x valid
  refine ⟨y,?_,hcost.le.trans (hmin x valid)⟩
  have pref := before_ext e (limit c i k) c i (fun j hj => by rw [limit,if_neg hj.symm])
  have eqy := congrFun (hf.trans (original_fill _ _ _)) i
  rw [ordinary,pref,limit,if_pos rfl] at eqy
  unfold ordinary at hfree
  omega

#print axioms original_minimum
#print axioms slice_minimum
#print axioms above_wall
#print axioms below_wall

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
