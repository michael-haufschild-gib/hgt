import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CommonCoordinate

/-!
# Integral inverse contents of actual digit prefixes

Every proper part has positive integral inverse content. Summing these
vectors realizes the inverse content of each actual prefix, starting at
zero and increasing by at least one in every coordinate per added part.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- Every proper part has a positive integral inverse-content vector. -/
theorem exists_integral_inverse_parts (C : DigitComposition p s (m + 1) S) (hp : 2 ≤ p) :
    ∃ a : Fin m → ZMod s → ℤ, (∀ i h, 1 ≤ a i h) ∧
      ∀ i, cyclicDifference (p : ℤ) (a i) = C.content i.castSucc := by
  have hex (i : Fin m) : ∃ a : ZMod s → ℤ, (∀ h, 1 ≤ a h) ∧
      cyclicDifference (p : ℤ) a = C.content i.castSucc := by
    have hi : i.castSucc.val + 1 < m + 1 := by
      simpa only [Fin.val_castSucc, Nat.add_lt_add_iff_right] using i.isLt
    have hJ : DivisibleContent p (C.content i.castSucc) :=
      (divisibleContent_tokens_iff p hp Prod.fst (C.parts i.castSucc)).mpr
        ⟨C.nonempty _, C.divisible _ hi⟩
    obtain ⟨a, ha⟩ := (exists_cyclicDifference_eq_iff p hp (C.content i.castSucc)).mpr hJ.2
    have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
    have hpow : (p : ℚ) ^ s ≠ 1 := ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))
    have hE : cyclicDifference (p : ℚ) (fun h => (a h : ℚ)) =
        fun h => (C.content i.castSucc h : ℚ) := by
      funext h
      have hh := congrFun ha h
      dsimp only [cyclicDifference] at hh ⊢
      exact_mod_cast hh
    have hinv : inverseContent (p : ℚ) (fun h => (C.content i.castSucc h : ℚ)) =
        fun h => (a h : ℚ) := by
      rw [← hE, inverseContent_cyclicDifference _ hpow]
    refine ⟨a, fun h => ?_, ha⟩
    have hge := C.inverseContent_part_ge_one hp i.castSucc hi h
    rw [hinv] at hge
    dsimp only at hge
    exact_mod_cast hge
  choose a ha hE using hex
  exact ⟨a, ha, hE⟩

/-- Actual proper-prefix contents admit integral inverse rows starting at zero
and increasing by at least one in every coordinate at each added part. -/
theorem exists_integral_inverse_prefixes (C : DigitComposition p s (m + 1) S) (hp : 2 ≤ p) :
    ∃ w : ℕ → ZMod s → ℤ,
      (∀ h, w 0 h = 0) ∧
      (∀ j < m, ∀ h, w j h + 1 ≤ w (j + 1) h) ∧
      (∀ j ≤ m, cyclicDifference (p : ℤ) (w j) =
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j)) := by
  obtain ⟨a, ha, hE⟩ := C.exists_integral_inverse_parts hp
  let w : ℕ → ZMod s → ℤ := fun j h => ∑ i ∈ univ.filter (fun i : Fin m => i.val < j), a i h
  refine ⟨w, ?_, ?_, ?_⟩
  · intro h
    simp only [w, Nat.not_lt_zero, filter_false, sum_empty]
  · intro j hj h
    let t : Fin m := ⟨j, hj⟩
    have hset : univ.filter (fun i : Fin m => i.val < j + 1) =
        insert t (univ.filter fun i : Fin m => i.val < j) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hi
        by_cases he : i.val = j
        · exact Or.inl (Fin.ext he)
        · exact Or.inr (by omega)
      · rintro (rfl | hi)
        · exact Nat.lt_succ_self _
        · omega
    have hnot : t ∉ univ.filter (fun i : Fin m => i.val < j) := by
      simp only [mem_filter, mem_univ, true_and, t, lt_self_iff_false, not_false_eq_true]
    change (∑ i ∈ univ.filter (fun i : Fin m => i.val < j), a i h) + 1 ≤ _
    change _ ≤ ∑ i ∈ univ.filter (fun i : Fin m => i.val < j + 1), a i h
    rw [hset, sum_insert hnot]
    have hh := ha t h
    omega
  · intro j hj
    funext h
    have hec : cyclicDifference (p : ℤ) (w j) h =
        ∑ i ∈ univ.filter (fun i : Fin m => i.val < j), C.content i.castSucc h := by
      simp only [cyclicDifference, w, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => congrFun (hE i) h
    rw [hec, C.content_prefix, sum_filter, sum_filter, Fin.sum_univ_castSucc]
    have hlast : ¬ (Fin.last m).val < j := by simp only [Fin.val_last]; omega
    simp only [Fin.val_castSucc, if_neg hlast, add_zero]
    rfl

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_integral_inverse_prefixes
