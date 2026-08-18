import GaloisForLFunctions.HTGeometry.MilnorSumSplitting

/-!
# Moving an entry through a Milnor symbol

Adjacent entries of a Milnor symbol anticommute, so an entry can be moved past a block of `k`
entries at the cost of the sign `(−1)^k`.  This is what lets a degree argument assume that two
distinguished entries sit next to each other.

* `milnorClassDeg_move` : **moving an entry to the front of a block negates the class once per
  entry passed.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

theorem length_move (l₁ l₂ l₃ : List Kˣ) (a : Kˣ) {n : ℕ}
    (h : (l₁ ++ l₂ ++ a :: l₃).length = n) : (l₁ ++ a :: (l₂ ++ l₃)).length = n := by
  simp only [List.length_append, List.length_cons] at h ⊢
  omega

/-- **Moving an entry across a block.**  Passing `a` to the left across `l₂` multiplies the class by
`(−1)^{|l₂|}`. -/
theorem milnorClassDeg_move {n : ℕ} (l₂ : List Kˣ) :
    ∀ (l₁ l₃ : List Kˣ) (a : Kˣ) (h : (l₁ ++ l₂ ++ a :: l₃).length = n),
      milnorClassDeg K n ⟨l₁ ++ l₂ ++ a :: l₃, h⟩
        = ((-1 : ℤ) ^ l₂.length)
          • milnorClassDeg K n ⟨l₁ ++ a :: (l₂ ++ l₃), length_move l₁ l₂ l₃ a h⟩ := by
  induction l₂ with
  | nil =>
      intro l₁ l₃ a h
      simp only [List.length_nil, pow_zero, one_zsmul, List.nil_append, List.append_nil]
  | cons b t ih =>
      intro l₁ l₃ a h
      have hrw : l₁ ++ (b :: t) ++ a :: l₃ = (l₁ ++ [b]) ++ t ++ a :: l₃ := by simp
      have h' : ((l₁ ++ [b]) ++ t ++ a :: l₃).length = n := by rw [← hrw]; exact h
      have step1 : milnorClassDeg K n ⟨l₁ ++ (b :: t) ++ a :: l₃, h⟩
          = milnorClassDeg K n ⟨(l₁ ++ [b]) ++ t ++ a :: l₃, h'⟩ :=
        congrArg (milnorClassDeg K n) (Subtype.ext hrw)
      have step2 := ih (l₁ ++ [b]) l₃ a h'
      have hswap : ((l₁ ++ (t ++ l₃)).length + 2 = n) := by
        have := h
        simp only [List.length_append, List.length_cons] at this ⊢
        omega
      have step3 : milnorClassDeg K n
            ⟨(l₁ ++ [b]) ++ a :: (t ++ l₃), length_move (l₁ ++ [b]) t l₃ a h'⟩
          = twoSlot l₁ (t ++ l₃) hswap b a :=
        congrArg (milnorClassDeg K n) (Subtype.ext (by simp))
      have step4 : twoSlot l₁ (t ++ l₃) hswap b a = -twoSlot l₁ (t ++ l₃) hswap a b :=
        twoSlot_swap l₁ (t ++ l₃) hswap b a
      have step5 : twoSlot l₁ (t ++ l₃) hswap a b
          = milnorClassDeg K n ⟨l₁ ++ a :: (b :: t ++ l₃),
              length_move l₁ (b :: t) l₃ a h⟩ :=
        congrArg (milnorClassDeg K n) (Subtype.ext (by simp))
      rw [step1, step2, step3, step4, step5, List.length_cons, pow_succ]
      simp [smul_neg, mul_comm]

end GaloisForLFunctions.HTGeometry
