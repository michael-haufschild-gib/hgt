import GaloisForLFunctions.HTGeometry.WeierstrassPaddedGenusProduct

/-!
# Padding a locally finite divisor into a sequence

A divisor presented as a family `p : ι → ℂ` over an arbitrary index type — locally finite (every
disc meets it in a finite set) and avoiding the origin — is automatically countable: the index type
is the countable union of the finite sets `{i | ‖p i‖ ≤ n}`.

Choosing an injection `g : ι → ℕ` and extending `p` by zero along it produces a sequence
`a : ℕ → ℂ` which is a `PaddedZeroSeq`, whose nonzero entries are exactly the values of `p`, and
whose fibre over every `w ≠ 0` has the same cardinality as the fibre of `p`.  This is the bridge
between the index-free description of a zero divisor and the ℕ-indexed Weierstrass product, and it
is what lets a *finite* zero set be handled by the same product as an infinite one.
-/

namespace GaloisForLFunctions

open Set

noncomputable section

/-- **A locally finite family in `ℂ` has a countable index type.** -/
theorem countable_of_locallyFiniteNorm {ι : Type*} {p : ι → ℂ}
    (hloc : ∀ r : ℝ, {i : ι | ‖p i‖ ≤ r}.Finite) : Countable ι := by
  have hcov : (Set.univ : Set ι) = ⋃ n : ℕ, {i : ι | ‖p i‖ ≤ (n : ℝ)} := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖p i‖
    exact ⟨n, hn⟩
  have huniv : (Set.univ : Set ι).Countable := by
    rw [hcov]
    exact Set.countable_iUnion fun n => (hloc (n : ℝ)).countable
  exact Set.countable_univ_iff.mp huniv

/-- **Padding a locally finite divisor into a sequence.**  Extending the family by zero along an
injection of its index type into `ℕ` gives a padded zero sequence with the same fibres away from
the origin. -/
theorem exists_paddedZeroSeq {ι : Type*} (p : ι → ℂ)
    (hloc : ∀ r : ℝ, {i : ι | ‖p i‖ ≤ r}.Finite) :
    ∃ a : ℕ → ℂ, PaddedZeroSeq a ∧ (∀ n, a n ≠ 0 → ∃ i, p i = a n) ∧
      ∀ w : ℂ, w ≠ 0 → {n : ℕ | a n = w}.ncard = {i : ι | p i = w}.ncard := by
  classical
  haveI : Countable ι := countable_of_locallyFiniteNorm hloc
  obtain ⟨g, hg⟩ : ∃ g : ι → ℕ, Function.Injective g := Countable.exists_injective_nat ι
  set a : ℕ → ℂ := Function.extend g p 0 with hadef
  have hval : ∀ i : ι, a (g i) = p i := fun i => hg.extend_apply p 0 i
  have hout : ∀ n : ℕ, (¬ ∃ i, g i = n) → a n = 0 := fun n hn => by
    rw [hadef, Function.extend_apply' p (0 : ℕ → ℂ) n hn]
    rfl
  have hsupp : ∀ n : ℕ, a n ≠ 0 → ∃ i, g i = n := by
    intro n hn
    by_contra hcon
    exact hn (hout n hcon)
  have hpre : ∀ n : ℕ, a n ≠ 0 → ∃ i, p i = a n := by
    intro n hn
    obtain ⟨i, rfl⟩ := hsupp n hn
    exact ⟨i, (hval i).symm⟩
  refine ⟨a, ?_, hpre, ?_⟩
  · intro r
    refine ((hloc r).image g).subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn
    obtain ⟨i, rfl⟩ := hsupp n hn.1
    refine ⟨i, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← hval i]
    exact hn.2
  · intro w hw
    have himg : {n : ℕ | a n = w} = g '' {i : ι | p i = w} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hn
        have hn0 : a n ≠ 0 := by rw [hn]; exact hw
        obtain ⟨i, rfl⟩ := hsupp n hn0
        exact ⟨i, by rw [← hval i]; exact hn, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rw [hval i]
        exact hi
    rw [himg, Set.ncard_image_of_injective _ hg]

end

end GaloisForLFunctions
