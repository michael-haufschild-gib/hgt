import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A regular local ring is a domain

```text
exists_finset_span_insert_of_ne_zero    a nonzero vector extends to a basis, as a finite set
exists_span_insert_of_notMem_sq         ** an element outside `𝔪²` is part of a minimal generating
                                           set of `𝔪` **
spanFinrank_map_maximalIdeal_succ_le    ** so the quotient by it needs one generator fewer **
```

The first is linear algebra in the cotangent space `𝔪/𝔪²`, transported to `𝔪` by Nakayama in the
form `CotangentSpace.span_image_eq_top_iff`.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Submodule IsLocalRing

universe u
variable {R : Type u} [CommRing R]

/-- A nonzero vector of a finite-dimensional space belongs to a spanning set of its dimension. -/
theorem exists_finset_span_insert_of_ne_zero {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {v : V} (hv : v ≠ 0) :
    ∃ b : Finset V, v ∈ b ∧ b.card = finrank k V ∧ Submodule.span k (b : Set V) = ⊤ := by
  classical
  have hli : LinearIndepOn k (id : V → V) ({v} : Set V) := by
    rw [linearIndepOn_singleton_iff]
    simpa using hv
  obtain ⟨B, -, hvB, hspan, hBli⟩ := exists_linearIndepOn_id_extension hli (Set.subset_univ _)
  have hsp : Submodule.span k B = ⊤ := by
    rw [eq_top_iff]
    intro y _hy
    exact hspan (Set.mem_univ y)
  have hfin : B.Finite := hBli.linearIndependent.setFinite
  haveI : Fintype B := hfin.fintype
  let bas : Basis B k V := Basis.mk hBli.linearIndependent (by
    simpa [Set.range_id'] using hsp.ge)
  refine ⟨hfin.toFinset, hfin.mem_toFinset.mpr (hvB rfl), ?_, ?_⟩
  · rw [finrank_eq_card_basis bas]
    simp
  · rw [Set.Finite.coe_toFinset]
    exact hsp

variable [IsLocalRing R] [IsNoetherianRing R]

/-- **An element outside `𝔪²` is part of a minimal generating set of `𝔪`.** -/
theorem exists_span_insert_of_notMem_sq {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ (maximalIdeal R) ^ 2) :
    ∃ s : Finset R, s.card + 1 ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span (insert x (s : Set R)) = maximalIdeal R := by
  classical
  set V := CotangentSpace R
  set v : V := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hv
  have hvne : v ≠ 0 := by
    rw [hv, Ne, Ideal.toCotangent_eq_zero]
    exact hx2
  obtain ⟨b, hvb, hcard, hspan⟩ := exists_finset_span_insert_of_ne_zero (k := ResidueField R) hvne
  -- lift the other basis vectors to `𝔪`
  have hsurj := (maximalIdeal R).toCotangent_surjective
  choose lift hlift using hsurj
  set s : Finset R := (b.erase v).image (fun w => ((lift w : ↥(maximalIdeal R)) : R)) with hs
  have himg : (maximalIdeal R).toCotangent ''
      (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
        ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) = (b : Set V) := by
    rw [Set.image_insert_eq, Set.image_image]
    have : (fun w => (maximalIdeal R).toCotangent (lift w)) = id := by
      funext w
      exact hlift w
    rw [this, Set.image_id, ← hv]
    ext w
    constructor
    · rintro (rfl | hw)
      · exact hvb
      · exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hw))
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl hwv
      · exact Or.inr (by simp [Finset.mem_erase, hwv, Finset.mem_coe.mp hw])
  have htop : Submodule.span R
      (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
        ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, himg, hspan]
  refine ⟨s, ?_, ?_⟩
  · have h1 : s.card ≤ (b.erase v).card := Finset.card_image_le
    have h2 : (b.erase v).card = b.card - 1 := Finset.card_erase_of_mem hvb
    have h3 : 1 ≤ b.card := Finset.card_pos.mpr ⟨v, hvb⟩
    have h4 : b.card = (maximalIdeal R).spanFinrank := by
      rw [hcard, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    omega
  · have hcoe : (insert x (s : Set R))
        = Subtype.val '' (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
          ((fun w => lift w) '' ((b.erase v : Finset V) : Set V))) := by
      rw [Set.image_insert_eq, Set.image_image, hs, Finset.coe_image]
    have hmap : Submodule.map (Submodule.subtype (maximalIdeal R))
        (Submodule.span R (insert (⟨x, hx⟩ : ↥(maximalIdeal R))
          ((fun w => lift w) '' ((b.erase v : Finset V) : Set V)))) = maximalIdeal R := by
      rw [htop, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span] at hmap
    rw [hcoe]
    exact hmap

end GaloisForLFunctions.HTGeometry
