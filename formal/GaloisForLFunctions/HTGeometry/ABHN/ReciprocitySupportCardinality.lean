import GaloisForLFunctions.HTGeometry.ABHN.ReciprocitySupportRigidity

/-!
# Cardinal rigidity of reciprocal support

When every local invariant is injective, a nonzero profile in the reciprocity kernel cannot be
supported at zero or one place. Thus every nontrivial reciprocal profile contains at least two
distinct nonzero local classes whose invariants participate in cancellation.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- A nonzero reciprocal profile with injective local invariants has support cardinality at least
two. -/
theorem heterogeneousRatModIntProfile_two_le_support_card_of_mem_kernel
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (hinv : ∀ i, Function.Injective (inv i))
    (f : Π₀ i, A i)
    (hf : f ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker)
    (hne : f ≠ 0) :
    2 ≤ f.support.card := by
  classical
  by_contra hcardTwo
  have hcard : f.support.card ≤ 1 := by omega
  have hsupp : f.support.Nonempty := by
    by_contra hsupp
    apply hne
    apply DFinsupp.ext
    intro i
    by_contra hi
    exact hsupp ⟨i, DFinsupp.mem_support_iff.mpr hi⟩
  obtain ⟨i, hi⟩ := hsupp
  have hf_single : f = DFinsupp.single i (f i) := by
    apply DFinsupp.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hj : j ∉ f.support := by
        intro hj
        exact hij (Finset.card_le_one.mp hcard i hi j hj)
      have hfj : f j = 0 := by
        by_contra hfj
        exact hj (DFinsupp.mem_support_iff.mpr hfj)
      rw [hfj]
      simp [DFinsupp.single_apply, hij]
  rw [hf_single] at hf
  have hfi : f i = 0 :=
    (heterogeneousRatModIntProfile_single_mem_kernel_iff_eq_zero
      A inv i (hinv i) (f i)).mp hf
  apply hne
  rw [hf_single, hfi]
  exact DFinsupp.single_zero i

/-- A nonzero reciprocal profile with injective local invariants has two distinct nonzero local
coordinates. -/
theorem heterogeneousRatModIntProfile_exists_two_nonzero_places_of_mem_kernel
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (hinv : ∀ i, Function.Injective (inv i))
    (f : Π₀ i, A i)
    (hf : f ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker)
    (hne : f ≠ 0) :
    ∃ i j, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  have hcard := heterogeneousRatModIntProfile_two_le_support_card_of_mem_kernel
    A inv hinv f hf hne
  have hone : 1 < f.support.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
  exact ⟨i, j, hij, DFinsupp.mem_support_iff.mp hi, DFinsupp.mem_support_iff.mp hj⟩

/-- Every specified nonzero coordinate of a reciprocal profile has a distinct nonzero partner. -/
theorem heterogeneousRatModIntProfile_exists_other_nonzero_place_of_mem_kernel
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (hinv : ∀ i, Function.Injective (inv i))
    (f : Π₀ i, A i)
    (hf : f ∈ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker)
    {i : ι} (hi : f i ≠ 0) :
    ∃ j, j ≠ i ∧ f j ≠ 0 := by
  have hne : f ≠ 0 := by
    intro hzero
    apply hi
    simpa using DFinsupp.ext_iff.mp hzero i
  have hcard := heterogeneousRatModIntProfile_two_le_support_card_of_mem_kernel
    A inv hinv f hf hne
  by_contra hother
  push Not at hother
  have hsubset : f.support ⊆ {i} := by
    intro j hj
    simp only [Finset.mem_singleton]
    by_contra hji
    exact DFinsupp.mem_support_iff.mp hj (hother j hji)
  have hcardOne : f.support.card ≤ 1 := by
    simpa using Finset.card_le_card hsubset
  omega

end


end GaloisForLFunctions.HTGeometry.ABHN
