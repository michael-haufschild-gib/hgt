import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSum

/-!
# Support cardinality for additive reciprocity profiles

A nonzero finitely supported profile in an additive group whose coordinate sum vanishes cannot be
supported at one place. This product-formula lemma is independent of Brauer groups and applies to
logarithmic Kummer currents as well as invariant profiles.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- A nonzero finite-support zero-sum profile has support cardinality at least two. -/
theorem finsupp_two_le_support_card_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι] {G : Type v} [AddCommGroup G]
    (f : ι →₀ G) (hsum : f.sum (fun _ x => x) = 0) (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  by_contra hcardTwo
  have hcard : f.support.card ≤ 1 := by omega
  have hsupp : f.support.Nonempty := by
    by_contra hsupp
    apply hne
    apply Finsupp.ext
    intro i
    by_contra hi
    exact hsupp ⟨i, Finsupp.mem_support_iff.mpr hi⟩
  obtain ⟨i, hi⟩ := hsupp
  have hf_single : f = Finsupp.single i (f i) := by
    apply Finsupp.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hj : j ∉ f.support := by
        intro hj
        exact hij (Finset.card_le_one.mp hcard i hi j hj)
      have hfj : f j = 0 := by
        by_contra hfj
        exact hj (Finsupp.mem_support_iff.mpr hfj)
      rw [hfj]
      simp [hij]
  rw [hf_single] at hsum
  have hfi : f i = 0 := by simpa using hsum
  apply hne
  rw [hf_single, hfi]
  exact Finsupp.single_zero (M := G) i

/-- A nonzero finite-support zero-sum profile has two distinct nonzero coordinates. -/
theorem finsupp_exists_two_nonzero_places_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι] {G : Type v} [AddCommGroup G]
    (f : ι →₀ G) (hsum : f.sum (fun _ x => x) = 0) (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  have hcard := finsupp_two_le_support_card_of_sum_eq_zero f hsum hne
  have hone : 1 < f.support.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
  exact ⟨i, j, hij, Finsupp.mem_support_iff.mp hi, Finsupp.mem_support_iff.mp hj⟩

/-- Every specified nonzero coordinate of a zero-sum profile has a distinct nonzero partner. -/
theorem finsupp_exists_other_nonzero_place_of_sum_eq_zero
    {ι : Type u} [DecidableEq ι] {G : Type v} [AddCommGroup G]
    (f : ι →₀ G) (hsum : f.sum (fun _ x => x) = 0)
    {i : ι} (hi : f i ≠ 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  have hne : f ≠ 0 := by
    intro hf
    apply hi
    simpa using Finsupp.ext_iff.mp hf i
  have hcard := finsupp_two_le_support_card_of_sum_eq_zero f hsum hne
  by_contra hother
  push Not at hother
  have hsubset : f.support ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact Finsupp.mem_support_iff.mp hj (hother j hji)
  have hcardOne : f.support.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  omega

/-- Injectively measured zero-sum profiles also require support at two or more places. -/
theorem finsupp_two_le_support_card_of_injective_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    {A : Type v} [AddCommGroup A] {G : Type*} [AddCommGroup G]
    (inv : A →+ G) (hinv : Function.Injective inv)
    (f : ι →₀ A) (hsum : f.sum (fun _ x => inv x) = 0) (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  by_contra hcardTwo
  have hcard : f.support.card ≤ 1 := by omega
  have hsupp : f.support.Nonempty := by
    by_contra hsupp
    apply hne
    apply Finsupp.ext
    intro i
    by_contra hi
    exact hsupp ⟨i, Finsupp.mem_support_iff.mpr hi⟩
  obtain ⟨i, hi⟩ := hsupp
  have hf_single : f = Finsupp.single i (f i) := by
    apply Finsupp.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hj : j ∉ f.support := by
        intro hj
        exact hij (Finset.card_le_one.mp hcard i hi j hj)
      have hfj : f j = 0 := by
        by_contra hfj
        exact hj (Finsupp.mem_support_iff.mpr hfj)
      rw [hfj]
      simp [hij]
  rw [hf_single] at hsum
  have hmap : inv (f i) = 0 := by simpa using hsum
  have hfi : f i = 0 := by
    apply hinv
    simpa using hmap
  apply hne
  rw [hf_single, hfi]
  exact Finsupp.single_zero (M := A) i

/-- An injectively measured nonzero zero-sum profile has two distinct nonzero coordinates. -/
theorem finsupp_exists_two_nonzero_places_of_injective_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    {A : Type v} [AddCommGroup A] {G : Type*} [AddCommGroup G]
    (inv : A →+ G) (hinv : Function.Injective inv)
    (f : ι →₀ A) (hsum : f.sum (fun _ x => inv x) = 0) (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  have hcard := finsupp_two_le_support_card_of_injective_sum_eq_zero inv hinv f hsum hne
  have hone : 1 < f.support.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
  exact ⟨i, j, hij, Finsupp.mem_support_iff.mp hi, Finsupp.mem_support_iff.mp hj⟩

/-- Every specified nonzero coordinate has a distinct partner under an injective zero-sum
measurement. -/
theorem finsupp_exists_other_nonzero_place_of_injective_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    {A : Type v} [AddCommGroup A] {G : Type*} [AddCommGroup G]
    (inv : A →+ G) (hinv : Function.Injective inv)
    (f : ι →₀ A) (hsum : f.sum (fun _ x => inv x) = 0)
    {i : ι} (hi : f i ≠ 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  have hne : f ≠ 0 := by
    intro hf
    apply hi
    simpa using Finsupp.ext_iff.mp hf i
  have hcard := finsupp_two_le_support_card_of_injective_sum_eq_zero inv hinv f hsum hne
  by_contra hother
  push Not at hother
  have hsubset : f.support ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact Finsupp.mem_support_iff.mp hj (hother j hji)
  have hcardOne : f.support.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  omega

end GaloisForLFunctions.HTGeometry.ABHN
