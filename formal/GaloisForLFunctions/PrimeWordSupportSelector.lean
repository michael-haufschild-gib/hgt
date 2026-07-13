import GaloisForLFunctions.KoszulCohomology

/-!
# Prime-word support selector

This file applies the finite marked-Koszul exponent to words in a prime alphabet.  The resulting
integer character is one exactly on words supported at one prime and zero on words supported at
two or more primes.  More importantly, mixed-prime words remain mixed after arbitrary words are
concatenated on either side.  Thus the scalar marked character annihilates the two-sided mixed-word
ideal.

This is a no-go theorem for a scalar connected-prime determinant, not an RH theorem.  Its positive
content is precise: any connected prime information must be retained in the marked complex,
cohomology, determinant line, or infinite completion defect *before* applying this scalar
character.
-/

namespace GaloisForLFunctions

section

variable {α : Type*} [DecidableEq α]

/-- The finite set of letters occurring in a word. -/
def primeWordSupport (w : List α) : Finset α :=
  w.toFinset

/-- The marked-Koszul character of the distinct-letter support of a word. -/
def primeWordSupportSelector (w : List α) : ℤ :=
  koszulSupportMarkedExponent (primeWordSupport w).card

/-- A word is mixed when at least two distinct letters occur in it. -/
def IsMixedPrimeWord (w : List α) : Prop :=
  2 ≤ (primeWordSupport w).card

/-- Concatenating on the left cannot remove letters from the support. -/
theorem primeWordSupport_subset_append_left (u w : List α) :
    primeWordSupport w ⊆ primeWordSupport (u ++ w) := by
  intro x hx
  simp only [primeWordSupport, List.mem_toFinset] at hx ⊢
  exact List.mem_append.mpr (Or.inr hx)

/-- Concatenating on the right cannot remove letters from the support. -/
theorem primeWordSupport_subset_append_right (w v : List α) :
    primeWordSupport w ⊆ primeWordSupport (w ++ v) := by
  intro x hx
  simp only [primeWordSupport, List.mem_toFinset] at hx ⊢
  exact List.mem_append.mpr (Or.inl hx)

/-- The mixed-word class is closed under left multiplication by words. -/
theorem IsMixedPrimeWord.append_left {w : List α} (h : IsMixedPrimeWord w) (u : List α) :
    IsMixedPrimeWord (u ++ w) := by
  exact h.trans (Finset.card_le_card (primeWordSupport_subset_append_left u w))

/-- The mixed-word class is closed under right multiplication by words. -/
theorem IsMixedPrimeWord.append_right {w : List α} (h : IsMixedPrimeWord w) (v : List α) :
    IsMixedPrimeWord (w ++ v) := by
  exact h.trans (Finset.card_le_card (primeWordSupport_subset_append_right w v))

/-- The mixed-word class is a two-sided word ideal. -/
theorem IsMixedPrimeWord.sandwich {w : List α} (h : IsMixedPrimeWord w) (u v : List α) :
    IsMixedPrimeWord (u ++ w ++ v) := by
  exact (h.append_left u).append_right v

/-- The word selector is the characteristic function of singleton support. -/
theorem primeWordSupportSelector_eq (w : List α) :
    primeWordSupportSelector w = if (primeWordSupport w).card = 1 then 1 else 0 := by
  exact koszulSupportMarkedExponent_eq _

/-- Every mixed-prime word is annihilated by the scalar support selector. -/
theorem primeWordSupportSelector_eq_zero_of_mixed (w : List α) (h : IsMixedPrimeWord w) :
    primeWordSupportSelector w = 0 := by
  exact koszulSupportMarkedExponent_eq_zero h

/-- The selector takes value one exactly when the word uses a single letter. -/
theorem primeWordSupportSelector_eq_one_iff (w : List α) :
    primeWordSupportSelector w = 1 ↔ ∃ p : α, primeWordSupport w = {p} := by
  constructor
  · intro hs
    rw [primeWordSupportSelector_eq] at hs
    by_cases hcard : (primeWordSupport w).card = 1
    · exact Finset.card_eq_one.mp hcard
    · simp [hcard] at hs
  · rintro ⟨p, hp⟩
    have hcard : (primeWordSupport w).card = 1 :=
      Finset.card_eq_one.mpr ⟨p, hp⟩
    rw [primeWordSupportSelector_eq, if_pos hcard]

/-- **Scalar two-sided-ideal no-go.**  Once a subword is mixed, arbitrary left and right context
cannot make its scalar marked-Koszul character nonzero. -/
theorem primeWordSupportSelector_sandwich_eq_zero {w : List α}
    (h : IsMixedPrimeWord w) (u v : List α) :
    primeWordSupportSelector (u ++ w ++ v) = 0 := by
  exact primeWordSupportSelector_eq_zero_of_mixed _ (h.sandwich u v)

end

end GaloisForLFunctions
