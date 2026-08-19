import GaloisForLFunctions.HTGeometry.MilnorSumSplitting

/-!
# Milnor symbols are permutation invariant up to sign

Interchanging two adjacent entries of a Milnor symbol negates its class, so permuting the entries
changes the class only by a sign.

* `milnorClassDeg_perm` : **a permutation of the entries changes the class by an integer factor.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- **Permuting the entries of a symbol changes its class by a sign.** -/
theorem milnorClassDeg_perm :
    ∀ {l l' : List Kˣ}, l.Perm l' → ∀ (pre : List Kˣ) {n : ℕ}
      (h : (pre ++ l).length = n) (h' : (pre ++ l').length = n),
      ∃ ε : ℤ, milnorClassDeg K n ⟨pre ++ l, h⟩ = ε • milnorClassDeg K n ⟨pre ++ l', h'⟩ := by
  intro l l' hperm
  induction hperm with
  | nil =>
      intro pre n h h'
      exact ⟨1, by rw [one_zsmul]⟩
  | cons x hp ih =>
      intro pre n h h'
      have hcast1 : ∀ (t : List Kˣ) (ht : (pre ++ x :: t).length = n),
          milnorClassDeg K n ⟨pre ++ x :: t, ht⟩
            = milnorClassDeg K n ⟨(pre ++ [x]) ++ t, by simpa using ht⟩ := by
        intro t ht
        exact congrArg (milnorClassDeg K n) (Subtype.ext (by simp))
      rw [hcast1 _ h, hcast1 _ h']
      exact ih (pre ++ [x]) _ _
  | swap x y t =>
      intro pre n h h'
      have hn : (pre ++ t).length + 2 = n := by
        simp only [List.length_append, List.length_cons] at h ⊢
        omega
      refine ⟨-1, ?_⟩
      show twoSlot pre t hn y x = (-1 : ℤ) • twoSlot pre t hn x y
      rw [twoSlot_swap, neg_one_zsmul]
  | @trans a b c hp₁ hp₂ ih₁ ih₂ =>
      intro pre n h h'
      have hmid : (pre ++ b).length = n := by
        rw [← h]
        simp only [List.length_append]
        rw [hp₁.length_eq]
      obtain ⟨ε₁, hε₁⟩ := ih₁ pre h hmid
      obtain ⟨ε₂, hε₂⟩ := ih₂ pre hmid h'
      exact ⟨ε₁ * ε₂, by rw [hε₁, hε₂, mul_smul]⟩

end GaloisForLFunctions.HTGeometry
