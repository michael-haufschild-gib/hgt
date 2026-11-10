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

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Positive integral prefix increments give the number-of-parts lower bound. -/
theorem inverse_prefix_floor {m : ℕ} {v : ℕ → ℤ} (hzero : v 0 = 0)
    (hstep : ∀ j < m, v j + 1 ≤ v (j + 1)) : ∀ j ≤ m, (j : ℤ) ≤ v j := by
  intro j
  induction j with
  | zero => exact fun _ => by rw [hzero, Nat.cast_zero]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hstep j (by omega)
    push_cast
    omega

/-- A terminal inverse row at its minimum fixes every earlier prefix at its minimum. -/
theorem inverse_row_eq_floor_of_terminal_eq {m : ℕ} {v : ℕ → ℤ}
    (hterminal : v 0 = m) (hstep : ∀ n < m, v (n + 1) + 1 ≤ v n)
    (hfloor : ∀ n ≤ m, (m : ℤ) - n ≤ v n) :
    ∀ n ≤ m, v n = (m : ℤ) - n := by
  have hupper : ∀ n ≤ m, v n + n ≤ (m : ℤ) := by
    intro n
    induction n with
    | zero => exact fun _ => by rw [hterminal, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep n (by omega)
      push_cast
      omega
  intro n hn
  have hlo := hfloor n hn
  have hhi := hupper n hn
  omega

/-- The last minimal inverse coordinate before a strict endpoint determines
an interval whose remaining coordinates all exceed the minimum by one. -/
theorem exists_last_inverse_boundary {m β : ℕ} (v : ℕ → ℤ)
    (hzero : v 0 = m) (hlower : ∀ h ≤ β, (m : ℤ) ≤ v h)
    (hβ : (m : ℤ) + 1 ≤ v β) :
    ∃ α < β, v α = m ∧ ∀ h, α < h → h ≤ β → (m : ℤ) + 1 ≤ v h := by
  have hβpos : 0 < β := by
    by_contra hn
    have he : β = 0 := by omega
    rw [he, hzero] at hβ
    omega
  let B := (range β).filter fun h => v h = m
  have hB : B.Nonempty := ⟨0, mem_filter.mpr ⟨mem_range.mpr hβpos, hzero⟩⟩
  obtain ⟨α, hα, hmax⟩ := B.exists_max_image id hB
  obtain ⟨hαβ, hαeq⟩ := mem_filter.mp hα
  refine ⟨α, mem_range.mp hαβ, hαeq, ?_⟩
  intro h hαh hhβ
  by_cases he : h = β
  · exact he.symm ▸ hβ
  · have hlow := hlower h hhβ
    have hne : v h ≠ m := by
      intro hvm
      have hm := hmax h (mem_filter.mpr ⟨mem_range.mpr (by omega), hvm⟩)
      change h ≤ α at hm
      omega
    omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_integral_inverse_prefixes
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.exists_last_inverse_boundary
