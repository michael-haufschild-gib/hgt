import GaloisForLFunctions.HTGeometry.PauliLabelDictionary

/-!
# Orthogonality of subset sign characters

The sign of the sum of a sign pattern over a subset is a character of the group of sign patterns.
Two such characters agree only for equal subsets, so summing their product over all sign patterns
gives the number of patterns when the subsets coincide and zero otherwise.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

private theorem sum_zmodTwo (f : ZMod 2 → ℂ) : (∑ z : ZMod 2, f z) = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

theorem sum_signOf_mul (m : ZMod 2) :
    (∑ z : ZMod 2, signOf (m * z)) = if m = 0 then 2 else 0 := by
  rw [sum_zmodTwo]
  rcases zmodTwo_cases m with rfl | rfl
  · rw [if_pos rfl]
    have h1 : (0 : ZMod 2) * 0 = 0 := by decide
    have h2 : (0 : ZMod 2) * 1 = 0 := by decide
    rw [h1, h2, signOf, if_pos rfl]
    norm_num
  · rw [if_neg (by decide)]
    simp +decide [signOf]

theorem signOf_finsetSum (ε : Fin n → ZMod 2) (m : Fin n → ZMod 2) :
    signOf (∑ i, m i * ε i) = ∏ i, signOf (m i * ε i) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp [signOf]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, signOf_add, ih]

theorem subsetSum_eq_indicator (ε : Fin n → ZMod 2) (S : Finset (Fin n)) :
    (∑ i ∈ S, ε i) = ∑ i, (if i ∈ S then (1 : ZMod 2) else 0) * ε i := by
  classical
  have h : ∀ i, (if i ∈ S then (1 : ZMod 2) else 0) * ε i = if i ∈ S then ε i else 0 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Orthogonality of subset sign characters.** -/
theorem sum_signOf_subsetSum_mul (S T : Finset (Fin n)) :
    (∑ ε : Fin n → ZMod 2, signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) =
      if S = T then (2 : ℂ) ^ n else 0 := by
  classical
  set m : Fin n → ZMod 2 :=
    fun i => (if i ∈ S then (1 : ZMod 2) else 0) + (if i ∈ T then (1 : ZMod 2) else 0) with hm
  have hpt : ∀ ε : Fin n → ZMod 2,
      signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i) = ∏ i, signOf (m i * ε i) := by
    intro ε
    rw [← signOf_add, subsetSum_eq_indicator ε S, subsetSum_eq_indicator ε T,
      ← Finset.sum_add_distrib]
    have hcongr : (∑ i, ((if i ∈ S then (1 : ZMod 2) else 0) * ε i +
        (if i ∈ T then (1 : ZMod 2) else 0) * ε i)) = ∑ i, m i * ε i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hm]
      ring
    rw [hcongr, signOf_finsetSum]
  have hpi : (Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset (ZMod 2))) =
      Finset.univ := by
    ext w
    simp
  have hfact : (∏ i : Fin n, ∑ z : ZMod 2, signOf (m i * z)) =
      ∑ ε : Fin n → ZMod 2, ∏ i, signOf (m i * ε i) := by
    rw [Finset.prod_univ_sum, hpi]
  simp only [hpt]
  rw [← hfact]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    have hm0 : ∀ i, m i = 0 := by
      intro i
      simp only [hm]
      by_cases hi : i ∈ S
      · simp only [if_pos hi]
        decide
      · simp only [if_neg hi]
        decide
    calc (∏ i : Fin n, ∑ z : ZMod 2, signOf (m i * z))
        = ∏ _i : Fin n, (2 : ℂ) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [sum_signOf_mul, if_pos (hm0 i)]
      _ = (2 : ℂ) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hST]
    obtain ⟨i₀, hi₀⟩ : ∃ i, m i ≠ 0 := by
      by_contra hcon
      refine hST (Finset.ext fun i => ?_)
      have hmi : m i = 0 := not_not.mp fun h => hcon ⟨i, h⟩
      simp only [hm] at hmi
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
      · exact ⟨fun _ => hiT, fun _ => hiS⟩
      · rw [if_pos hiS, if_neg hiT] at hmi
        exact absurd hmi (by decide)
      · rw [if_neg hiS, if_pos hiT] at hmi
        exact absurd hmi (by decide)
      · exact ⟨fun h => absurd h hiS, fun h => absurd h hiT⟩
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [sum_signOf_mul, if_neg hi₀]

end GaloisForLFunctions.HTGeometry
