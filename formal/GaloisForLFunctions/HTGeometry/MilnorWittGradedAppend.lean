import GaloisForLFunctions.HTGeometry.MilnorWittGradedRing
import GaloisForLFunctions.HTGeometry.MilnorWittGradedCollapse

/-!
# Vanishing words stay vanishing inside longer words

The graded product is induced by concatenation of words, and it is additive in each variable, so a
word class that vanishes still vanishes after any prefix or suffix is concatenated onto it.  This
turns every identity proved for a word into an identity valid at an arbitrary interior slot, which
is the form the Milnor--Witt calculus needs.

* `mwClassDeg_mul_eq_zero_left`, `mwClassDeg_mul_eq_zero_right` : concatenation kills nothing.
* `mwClassDeg_eq_zero_of_prefix_eq_zero` : **a word with a vanishing prefix vanishes.**
* `mwSymbol_mul_neg_self_infix` : **`[a][-a] = 0` at an arbitrary interior slot.**
-/

namespace GaloisForLFunctions.HTGeometry

section Append

variable {F : Type*} [Field F]

/-- Concatenating a word on the right preserves vanishing. -/
theorem mwClassDeg_mul_eq_zero_left {m n : ℤ} (v : MWWordDeg F m) (w : MWWordDeg F n)
    (h : mwClassDeg F m v = 0) : mwClassDeg F (m + n) (mwWordMul v w) = 0 := by
  have h0 : mwMul m n (mwClassDeg F m v) (mwClassDeg F n w) = 0 := by
    rw [h, map_zero]
    rfl
  rwa [mwMul_class] at h0

/-- Concatenating a word on the left preserves vanishing. -/
theorem mwClassDeg_mul_eq_zero_right {m n : ℤ} (v : MWWordDeg F m) (w : MWWordDeg F n)
    (h : mwClassDeg F n w = 0) : mwClassDeg F (m + n) (mwWordMul v w) = 0 := by
  have h0 : mwMul m n (mwClassDeg F m v) (mwClassDeg F n w) = 0 := by
    rw [h, map_zero]
  rwa [mwMul_class] at h0

/-- **A word whose prefix already vanishes vanishes.**  The suffix is arbitrary, and so are the
`η`-exponents, provided they add up. -/
theorem mwClassDeg_eq_zero_of_prefix_eq_zero {m n d : ℤ} {k j kj : ℕ} {L R M : List Fˣ}
    (p : ((L.length : ℤ)) - k = m) (q : ((R.length : ℤ)) - j = n)
    (hk : kj = k + j) (hM : M = L ++ R) (hd : m + n = d)
    (pd : ((M.length : ℤ)) - kj = d)
    (h : mwClassDeg F m ⟨(k, L), p⟩ = 0) :
    mwClassDeg F d ⟨(kj, M), pd⟩ = 0 := by
  have h1 : mwClassDeg F (m + n) (mwWordMul (⟨(k, L), p⟩ : MWWordDeg F m)
      (⟨(j, R), q⟩ : MWWordDeg F n)) = 0 :=
    mwClassDeg_mul_eq_zero_left _ _ h
  have h2 := congrArg (mwDegCongr hd) h1
  rw [map_zero] at h2
  rw [mwDegCongr_class' hd _ (⟨(kj, M), pd⟩ : MWWordDeg F d)
    (by
      show ((k + j, L ++ R) : ℕ × List Fˣ) = (kj, M)
      rw [hk, hM])] at h2
  exact h2

/-- **`[a][-a] = 0` at an arbitrary interior slot.** -/
theorem mwSymbol_mul_neg_self_infix {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ) (a : Fˣ)
    (p : (((l₁ ++ a :: (-a) :: l₂).length : ℤ)) - k = n) :
    mwClassDeg F n ⟨(k, l₁ ++ a :: (-a) :: l₂), p⟩ = 0 := by
  have pL : ((((l₁ ++ [a, -a]).length : ℤ))) - k = ((l₁.length : ℤ)) + 2 - k := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    push_cast
    ring
  have pR : ((l₂.length : ℤ)) - (0 : ℕ) = ((l₂.length : ℤ)) := by
    push_cast
    ring
  refine mwClassDeg_eq_zero_of_prefix_eq_zero pL pR (Nat.add_zero k).symm
    (List.append_assoc l₁ [a, -a] l₂).symm ?_ p ?_
  · simp only [List.length_append, List.length_cons] at p
    push_cast at p ⊢
    omega
  · exact mwSymbol_mul_neg_self (F := F) k l₁ a pL

end Append

end GaloisForLFunctions.HTGeometry
