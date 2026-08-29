import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealPrime
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealTransport

/-!
# Finite generation of radical differential ideals descends along a differential surjection

An ideal containing the kernel of a surjection is recovered from its image, and radicality,
stability under the derivation and generation by a finite set all travel with it.  So a radical
differential ideal whose image is the radical differential ideal of a finite set is itself the
radical differential ideal of a finite set, once the kernel is known to lie in the radical
differential ideal of a finite subset.

* `isRadical_map_of_surjective`, `deriv_mem_map_of_surjective`;
* `isRadDiffFG_of_map`;
* `isRadDiffFG_comap_of_ringEquiv`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {A B : Type*} [CommRing A] [Differential A] [CommRing B] [Differential B]

omit [Differential A] [Differential B] in
/-- The image of a radical ideal containing the kernel is radical. -/
theorem isRadical_map_of_surjective (f : A →+* B) (hsurj : Function.Surjective f)
    {I : Ideal A} (hker : RingHom.ker f ≤ I) (hrad : I.IsRadical) :
    (Ideal.map f I).IsRadical := by
  have hcm : Ideal.comap f (Ideal.map f I) = I := by
    rw [Ideal.comap_map_of_surjective f hsurj I]
    exact sup_eq_left.mpr hker
  intro y hy
  obtain ⟨n, hn⟩ := hy
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← map_pow] at hn
  have hxI : x ∈ I := by
    refine hrad ⟨n, ?_⟩
    rw [← hcm]
    exact hn
  exact Ideal.mem_map_of_mem f hxI

/-- The image of a differential ideal under a differential surjection is differential. -/
theorem deriv_mem_map_of_surjective (f : A →+* B)
    (hf : ∀ x, f (Differential.deriv x) = Differential.deriv (f x))
    (hsurj : Function.Surjective f) {I : Ideal A}
    (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) :
    ∀ y ∈ Ideal.map f I, Differential.deriv y ∈ Ideal.map f I := by
  intro y hy
  obtain ⟨x, hxI, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hsurj).mp hy
  rw [← hf x]
  exact Ideal.mem_map_of_mem f (hδ x hxI)

/-- **Finite generation of a radical differential ideal descends along a differential
surjection.**  The finite set is the union of a finite set carrying the kernel with a set of lifts
of a finite set generating the image. -/
theorem isRadDiffFG_of_map (f : A →+* B)
    (hf : ∀ x, f (Differential.deriv x) = Differential.deriv (f x))
    (hsurj : Function.Surjective f) {I : Ideal A} (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) (hker : RingHom.ker f ≤ I)
    {T₀ : Finset A} (hT₀I : ↑T₀ ⊆ (I : Set A))
    (hT₀ker : RingHom.ker f ≤ radicalDifferentialIdeal (T₀ : Set A))
    (hmap : IsRadDiffFG (Ideal.map f I)) : IsRadDiffFG I := by
  classical
  obtain ⟨Tb, hTb⟩ := hmap
  have hlift : ∀ t ∈ Tb, ∃ a : A, a ∈ I ∧ f a = t := by
    intro t ht
    have htmem : t ∈ Ideal.map f I := by
      rw [hTb]
      exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
    exact (Ideal.mem_map_iff_of_surjective f hsurj).mp htmem
  choose! g hgI hgf using hlift
  set T : Finset A := T₀ ∪ Tb.image g with hT
  have hTI : ↑T ⊆ (I : Set A) := by
    intro y hy
    rcases Finset.mem_union.mp (by exact_mod_cast hy) with hy₀ | hyg
    · exact hT₀I (by exact_mod_cast hy₀)
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hyg
      exact hgI t ht
  set J : Ideal A := radicalDifferentialIdeal (T : Set A) with hJ
  have hJI : J ≤ I :=
    radicalDifferentialIdeal_le hTI hrad hδ
  have hkerJ : RingHom.ker f ≤ J := by
    refine le_trans hT₀ker (radicalDifferentialIdeal_le ?_
      (isRadical_radicalDifferentialIdeal _) (deriv_mem_radicalDifferentialIdeal _))
    intro y hy
    exact subset_radicalDifferentialIdeal _
      (by exact_mod_cast Finset.mem_union_left (Tb.image g) (by exact_mod_cast hy))
  have hmapJ : Ideal.map f I ≤ Ideal.map f J := by
    rw [hTb]
    refine radicalDifferentialIdeal_le ?_
      (isRadical_map_of_surjective f hsurj hkerJ (isRadical_radicalDifferentialIdeal _))
      (deriv_mem_map_of_surjective f hf hsurj (deriv_mem_radicalDifferentialIdeal _))
    intro t ht
    have htT : t ∈ Tb := by exact_mod_cast ht
    rw [← hgf t htT]
    refine Ideal.mem_map_of_mem f (subset_radicalDifferentialIdeal _ ?_)
    exact_mod_cast Finset.mem_union_right T₀ (Finset.mem_image_of_mem g htT)
  refine ⟨T, le_antisymm ?_ hJI⟩
  have hcmI : Ideal.comap f (Ideal.map f I) = I := by
    rw [Ideal.comap_map_of_surjective f hsurj I]
    exact sup_eq_left.mpr hker
  have hcmJ : Ideal.comap f (Ideal.map f J) = J := by
    rw [Ideal.comap_map_of_surjective f hsurj J]
    exact sup_eq_left.mpr hkerJ
  intro x hx
  have hxc : x ∈ Ideal.comap f (Ideal.map f J) := hmapJ (by rw [← hcmI] at hx; exact hx)
  rwa [hcmJ] at hxc

/-- **Finite generation of a radical differential ideal travels along a differential ring
isomorphism.** -/
theorem isRadDiffFG_comap_of_ringEquiv (e : A ≃+* B)
    (he : ∀ x, e (Differential.deriv x) = Differential.deriv (e x))
    {J : Ideal B} (hrad : J.IsRadical) (hδ : ∀ y ∈ J, Differential.deriv y ∈ J)
    (hJ : IsRadDiffFG J) : IsRadDiffFG (Ideal.comap (e : A →+* B) J) := by
  classical
  have hsurj : Function.Surjective (e : A →+* B) := e.surjective
  have hker : RingHom.ker (e : A →+* B) = ⊥ := by
    ext x
    simp
  have hradc : (Ideal.comap (e : A →+* B) J).IsRadical := by
    intro x hxn
    obtain ⟨n, hn⟩ := hxn
    have : (e x) ^ n ∈ J := by rw [← map_pow]; exact hn
    exact hrad ⟨n, this⟩
  have hδc : ∀ x ∈ Ideal.comap (e : A →+* B) J, Differential.deriv x ∈
      Ideal.comap (e : A →+* B) J := by
    intro x hx
    show e (Differential.deriv x) ∈ J
    rw [he x]
    exact hδ _ hx
  refine isRadDiffFG_of_map (e : A →+* B) he hsurj hradc hδc (by rw [hker]; exact bot_le)
    (T₀ := ∅) (by simp) (by rw [hker]; exact bot_le) ?_
  rw [Ideal.map_comap_of_surjective (e : A →+* B) hsurj J]
  exact hJ

end

end GaloisForLFunctions.HTGeometry
