import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitExchanges

/-!
# Uniqueness of increasing digit allocations

In each residue class, the digits assigned to an initial segment of an
increasing composition lie below every remaining digit. Such a subset
minimizes its value among subsets of the same size.

Two increasing allocations with the same residue-content matrix therefore
have equal prefix values. Subtracting consecutive prefixes gives equality
of every numerical part. Equal digit occurrences may have different labels;
the numerical composition is unique.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Equal-sized finite collections can be compared when every value in the first is smaller. -/
theorem sum_le_of_equal_card_of_forall_le {α : Type*} (A B : Finset α) (f : α → ℤ)
    (hc : A.card = B.card) (hle : ∀ a ∈ A, ∀ b ∈ B, f a ≤ f b) :
    ∑ a ∈ A, f a ≤ ∑ b ∈ B, f b := by
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmin⟩ := B.exists_min_image f hB
    calc
      ∑ a ∈ A, f a ≤ ∑ _a ∈ A, f b := sum_le_sum fun a ha => hle a ha b hb
      _ = ∑ _b ∈ B, f b := by simp only [sum_const, hc]
      _ ≤ ∑ b ∈ B, f b := sum_le_sum fun a ha => hmin a ha
  · have hBe : B = ∅ := not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := card_eq_zero.mp (by simpa only [hBe, card_empty] using hc)
    simp only [hAe, hBe, sum_empty, le_refl]

/-- A subset lying below its complement minimizes every increasing additive weight at its size. -/
theorem smallest_subset_sum_le {α : Type*} [DecidableEq α] {A B S : Finset α}
    (f : α → ℤ) (hB : B ⊆ S) (hc : A.card = B.card)
    (hsmall : ∀ a ∈ A, ∀ b ∈ S \ A, f a ≤ f b) :
    ∑ a ∈ A, f a ≤ ∑ b ∈ B, f b := by
  have hdiff : (A \ B).card = (B \ A).card := by
    simp only [card_sdiff]
    rw [hc, inter_comm B A]
  have hle := sum_le_of_equal_card_of_forall_le (A \ B) (B \ A) f hdiff
    (fun a ha b hb => hsmall a (mem_sdiff.mp ha).1 b
      (mem_sdiff.mpr ⟨hB (mem_sdiff.mp hb).1, (mem_sdiff.mp hb).2⟩))
  have hAs : A \ (A ∩ B) = A \ B := by
    ext x
    simp only [mem_sdiff, mem_inter]
    tauto
  have hBs : B \ (A ∩ B) = B \ A := by
    ext x
    simp only [mem_sdiff, mem_inter]
    tauto
  have hA := sum_sdiff (f := f) (show A ∩ B ⊆ A from fun _ hx => (mem_inter.mp hx).1)
  have hB' := sum_sdiff (f := f) (show A ∩ B ⊆ B from fun _ hx => (mem_inter.mp hx).2)
  rw [hAs] at hA
  rw [hBs] at hB'
  linarith only [hle, hA, hB']

namespace DigitComposition
variable {p s m : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- The digits allocated to the first k parts. -/
def prefixDigits (C : DigitComposition p s m S) (k : ℕ) : Finset (Digit p) :=
  (univ.filter fun i : Fin m => i.val < k).biUnion C.parts

omit [NeZero s] in
theorem mem_prefix (C : DigitComposition p s m S) (k : ℕ) (x : Digit p) :
    x ∈ C.prefixDigits k ↔ ∃ i : Fin m, i.val < k ∧ x ∈ C.parts i := by
  simp only [prefixDigits, mem_biUnion, mem_filter, mem_univ, true_and]

omit [NeZero s] in
theorem prefix_subset (C : DigitComposition p s m S) (k : ℕ) : C.prefixDigits k ⊆ S := by
  intro x hx
  obtain ⟨i, _, hi⟩ := (C.mem_prefix k x).mp hx
  exact C.subset i hi

omit [NeZero s] in
/-- Prefix contents are sums of the contents of their constituent parts. -/
theorem content_prefix (C : DigitComposition p s m S) (k : ℕ) (h : ZMod s) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits k) h =
      ∑ i ∈ univ.filter (fun i : Fin m => i.val < k), C.content i h := by
  have hd : Set.PairwiseDisjoint
      (↑(univ.filter fun i : Fin m => i.val < k)) C.parts :=
    fun _ _ _ _ hij => C.disjoint hij
  simp only [content, tokenContent, card_filter, Nat.cast_sum, prefixDigits]
  rw [sum_biUnion hd]

omit [NeZero s] in
/-- The value of a prefix is the sum of its part values. -/
theorem value_prefix (C : DigitComposition p s m S) (k : ℕ) :
    digitValue p (C.prefixDigits k) =
      ∑ i ∈ univ.filter (fun i : Fin m => i.val < k), C.value i := by
  have hd : Set.PairwiseDisjoint
      (↑(univ.filter fun i : Fin m => i.val < k)) C.parts :=
    fun _ _ _ _ hij => C.disjoint hij
  dsimp only [digitValue, tokenValue, prefixDigits, value]
  rw [sum_biUnion hd]

omit [NeZero s] in
/-- Every residue-class prefix of an increasing allocation lies below its complement. -/
theorem TauMonotone.prefix_smallest {C : DigitComposition p s m S}
    (hC : C.TauMonotone) (k : ℕ) (h : ZMod s)
    {x y : Digit p} (hx : x ∈ (C.prefixDigits k).filter fun t => (t.1 : ZMod s) = h)
    (hy : y ∈ (S.filter fun t => (t.1 : ZMod s) = h) \
      ((C.prefixDigits k).filter fun t => (t.1 : ZMod s) = h)) : x.1 ≤ y.1 := by
  obtain ⟨hxP, hxcol⟩ := mem_filter.mp hx
  obtain ⟨i, hi, hxi⟩ := (C.mem_prefix k x).mp hxP
  obtain ⟨hyS, hycol⟩ := mem_filter.mp (mem_sdiff.mp hy).1
  obtain ⟨j, hyj⟩ := C.cover y hyS
  have hkj : k ≤ j.val := by
    by_contra hn
    exact (mem_sdiff.mp hy).2 (mem_filter.mpr
      ⟨(C.mem_prefix k y).mpr ⟨j, by omega, hyj⟩, hycol⟩)
  exact hC i j (by change i.val < j.val; omega) x hxi y hyj (hxcol.trans hycol.symm)

/-- Increasing allocations with the same content matrix give equal values to every prefix. -/
theorem TauMonotone.prefix_value_eq {C D : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hD : D.TauMonotone) (hc : C.content = D.content) (k : ℕ) :
    digitValue p (C.prefixDigits k) = digitValue p (D.prefixDigits k) := by
  have hcard (h : ZMod s) :
      ((C.prefixDigits k).filter fun t => (t.1 : ZMod s) = h).card =
        ((D.prefixDigits k).filter fun t => (t.1 : ZMod s) = h).card := by
    have he : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits k) h =
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (D.prefixDigits k) h := by
      rw [C.content_prefix, D.content_prefix, hc]
    dsimp only [tokenContent] at he
    exact_mod_cast he
  have hle {A B : DigitComposition p s m S} (hA : A.TauMonotone) (h : ZMod s)
      (hn : ((A.prefixDigits k).filter fun t => (t.1 : ZMod s) = h).card =
        ((B.prefixDigits k).filter fun t => (t.1 : ZMod s) = h).card) :
      (∑ x ∈ (A.prefixDigits k).filter (fun t => (t.1 : ZMod s) = h), (p : ℤ) ^ x.1) ≤
        ∑ x ∈ (B.prefixDigits k).filter (fun t => (t.1 : ZMod s) = h), (p : ℤ) ^ x.1 := by
    refine smallest_subset_sum_le (S := S.filter fun t => (t.1 : ZMod s) = h)
      (fun t : Digit p => (p : ℤ) ^ t.1) ?_ hn ?_
    · intro x hx
      exact mem_filter.mpr ⟨B.prefix_subset k (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
    · intro a ha b hb
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega))
        (hA.prefix_smallest k h ha hb)
  change (∑ x ∈ C.prefixDigits k, (p : ℤ) ^ x.1) = ∑ x ∈ D.prefixDigits k, (p : ℤ) ^ x.1
  rw [← sum_fiberwise (C.prefixDigits k) (fun t : Digit p => (t.1 : ZMod s)),
    ← sum_fiberwise (D.prefixDigits k) (fun t : Digit p => (t.1 : ZMod s))]
  apply sum_congr rfl
  intro h _
  exact le_antisymm (hle hC h (hcard h)) (hle hD h (hcard h).symm)

omit [NeZero s] in
/-- Consecutive prefix values differ by the intervening part. -/
theorem prefix_value_succ (C : DigitComposition p s m S) (i : Fin m) :
    digitValue p (C.prefixDigits (i.val + 1)) = digitValue p (C.prefixDigits i.val) + C.value i := by
  have hsets : univ.filter (fun j : Fin m => j.val < i.val + 1) =
      insert i (univ.filter fun j : Fin m => j.val < i.val) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hj
      by_cases he : j = i
      · exact Or.inl he
      · right
        have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
        omega
    · rintro (rfl | hj) <;> omega
  rw [C.value_prefix, C.value_prefix, hsets, sum_insert]
  · exact add_comm _ _
  · simp only [mem_filter, mem_univ, true_and, lt_self_iff_false, not_false_eq_true]

/-- The increasing allocation of a fixed content matrix has unique numerical part values. -/
theorem TauMonotone.values_eq {C D : DigitComposition p s m S} (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hD : D.TauMonotone) (hc : C.content = D.content) :
    C.value = D.value := by
  funext i
  have h0 := hC.prefix_value_eq hp hD hc i.val
  have h1 := hC.prefix_value_eq hp hD hc (i.val + 1)
  have hCstep := C.prefix_value_succ i
  have hDstep := D.prefix_value_succ i
  linarith only [h0, h1, hCstep, hDstep]

/-- Every realized content matrix determines one increasing numerical composition. -/
theorem exists_unique_tauMonotone_values (C : DigitComposition p s m S) (hp : 2 ≤ p) :
    ∃ D : DigitComposition p s m S, D.content = C.content ∧ D.TauMonotone ∧
      ∀ E : DigitComposition p s m S, E.content = C.content → E.TauMonotone → E.value = D.value := by
  obtain ⟨D, hDc, hD⟩ := C.exists_tauMonotone_same_content hp
  exact ⟨D, hDc, hD, fun E hEc hE => hE.values_eq hp hD (hEc.trans hDc.symm)⟩

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.TauMonotone.values_eq
#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_unique_tauMonotone_values
