import GaloisForLFunctions.HTGeometry.ApartmentChains

/-!
# The interval below a coordinate subset is the apartment of that subset

Inside the apartment of a frame, the elements strictly below a coordinate subset `S` are the proper
nonzero subsets of `S`, which is the apartment of the frame `S` itself.  The identification is by
restriction and image along the inclusion of `S`.

This is what the Mayer--Vietoris descent needs to recognise the link of a coatom of an apartment as
an apartment again, one vector smaller.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial Opposite

universe u

variable {ι : Type u}

/-- **The interval below a coordinate subset is the apartment of that subset.** -/
def properBelowSetOrderIso (S : Set ι) :
    {U : properPart (Set ι) // (U : Set ι) < S} ≃o properPart (Set ↥S) where
  toFun U :=
    ⟨Subtype.val ⁻¹' ((U : properPart (Set ι)) : Set ι), by
      obtain ⟨x, hx⟩ : ((U : properPart (Set ι)) : Set ι).Nonempty :=
        Set.nonempty_iff_ne_empty.2 (ne_of_gt (U : properPart (Set ι)).2.1)
      exact Set.empty_ssubset.2 ⟨⟨x, le_of_lt U.2 hx⟩, hx⟩, by
      obtain ⟨y, hyS, hyU⟩ : ∃ y, y ∈ S ∧ y ∉ ((U : properPart (Set ι)) : Set ι) := by
        by_contra hcon
        push Not at hcon
        exact absurd (Set.Subset.antisymm (le_of_lt U.2) fun z hz => hcon z hz) (ne_of_lt U.2)
      exact Set.ssubset_univ_iff.2 fun hcon => hyU (by
        have : (⟨y, hyS⟩ : ↥S) ∈ Subtype.val ⁻¹' ((U : properPart (Set ι)) : Set ι) := by
          rw [hcon]
          trivial
        exact this)⟩
  invFun T :=
    ⟨⟨Subtype.val '' ((T : properPart (Set ↥S)) : Set ↥S), by
        obtain ⟨y, hy⟩ : ((T : properPart (Set ↥S)) : Set ↥S).Nonempty :=
          Set.nonempty_iff_ne_empty.2 (ne_of_gt (T : properPart (Set ↥S)).2.1)
        exact Set.empty_ssubset.2 ⟨(y : ι), ⟨y, hy, rfl⟩⟩, by
        obtain ⟨z, hz⟩ : ∃ z : ↥S, z ∉ ((T : properPart (Set ↥S)) : Set ↥S) := by
          by_contra hcon
          push Not at hcon
          exact absurd (Set.eq_univ_of_forall hcon) (ne_of_lt (T : properPart (Set ↥S)).2.2)
        refine Set.ssubset_univ_iff.2 fun hcon => hz ?_
        have hmem : (z : ι) ∈ Subtype.val '' ((T : properPart (Set ↥S)) : Set ↥S) := by
          rw [hcon]
          trivial
        obtain ⟨w, hw, hwz⟩ := hmem
        rwa [Subtype.val_injective hwz] at hw⟩,
      by
        obtain ⟨z, hz⟩ : ∃ z : ↥S, z ∉ ((T : properPart (Set ↥S)) : Set ↥S) := by
          by_contra hcon
          push Not at hcon
          exact absurd (Set.eq_univ_of_forall hcon) (ne_of_lt (T : properPart (Set ↥S)).2.2)
        refine lt_of_le_of_ne (fun x hx => ?_) fun hcon => hz ?_
        · obtain ⟨w, -, rfl⟩ := hx
          exact w.2
        · have hcon' : Subtype.val '' ((T : properPart (Set ↥S)) : Set ↥S) = S := hcon
          have hmem : (z : ι) ∈ Subtype.val '' ((T : properPart (Set ↥S)) : Set ↥S) := by
            rw [hcon']
            exact z.2
          obtain ⟨w, hw, hwz⟩ := hmem
          rwa [Subtype.val_injective hwz] at hw⟩
  left_inv U := by
    refine Subtype.ext (Subtype.ext ?_)
    exact Set.image_preimage_eq_of_subset (by
      rw [Subtype.range_coe]
      exact le_of_lt U.2)
  right_inv T := by
    refine Subtype.ext ?_
    exact Set.preimage_image_eq _ Subtype.val_injective
  map_rel_iff' {U U'} := by
    constructor
    · intro h x hx
      have hxS : x ∈ S := le_of_lt U.2 hx
      exact h (show (⟨x, hxS⟩ : ↥S) ∈ Subtype.val ⁻¹' _ from hx)
    · intro h y hy
      exact h hy

/-! ## Orderings that end with a given vector -/

section Restrict

variable {n : ℕ} {a : ι}

theorem ne_of_castSucc {e : Fin (n + 3) ≃ ι} (he : e (Fin.last (n + 2)) = a) (j : Fin (n + 2)) :
    e j.castSucc ∈ (Set.univ \ {a} : Set ι) := by
  refine ⟨Set.mem_univ _, fun hcon => ?_⟩
  have : j.castSucc = Fin.last (n + 2) := e.injective (by
    rw [he]
    exact Set.mem_singleton_iff.1 hcon)
  exact absurd (congrArg Fin.val this) (by
    simp only [Fin.val_castSucc, Fin.val_last]
    have := j.isLt
    omega)

theorem symm_lt_of_mem {e : Fin (n + 3) ≃ ι} (he : e (Fin.last (n + 2)) = a)
    (x : ↥(Set.univ \ {a} : Set ι)) : ((e.symm (x : ι)) : ℕ) < n + 2 := by
  have hne : e.symm (x : ι) ≠ Fin.last (n + 2) := by
    intro hcon
    refine x.2.2 (Set.mem_singleton_iff.2 ?_)
    have hx : (x : ι) = e (Fin.last (n + 2)) := by
      conv_lhs => rw [← Equiv.apply_symm_apply e (x : ι)]
      rw [hcon]
    rw [hx, he]
  have hlt := (e.symm (x : ι)).isLt
  have hval : ((e.symm (x : ι)) : ℕ) ≠ n + 2 := fun hcon => hne (Fin.ext (by simpa using hcon))
  omega

/-- **An ordering that ends with a given vector restricts to an ordering of the rest.** -/
def restrictOrdering {e : Fin (n + 3) ≃ ι} (he : e (Fin.last (n + 2)) = a) :
    Fin (n + 2) ≃ ↥(Set.univ \ {a} : Set ι) where
  toFun j := ⟨e j.castSucc, ne_of_castSucc he j⟩
  invFun x := ⟨((e.symm (x : ι)) : ℕ), symm_lt_of_mem he x⟩
  left_inv j := by
    refine Fin.ext ?_
    simp only [Equiv.symm_apply_apply, Fin.val_castSucc]
  right_inv x := by
    refine Subtype.ext ?_
    have hval : (⟨((e.symm (x : ι)) : ℕ), symm_lt_of_mem he x⟩ : Fin (n + 2)).castSucc
        = e.symm (x : ι) := by
      refine Fin.ext ?_
      simp
    show e (⟨((e.symm (x : ι)) : ℕ), symm_lt_of_mem he x⟩ : Fin (n + 2)).castSucc = (x : ι)
    rw [hval, Equiv.apply_symm_apply]

/-- **The initial segments of the restricted ordering are those of the original one.** -/
theorem image_initialSegSet_restrictOrdering {e : Fin (n + 3) ≃ ι}
    (he : e (Fin.last (n + 2)) = a) (i : Fin (n + 2)) :
    Subtype.val '' (initialSegSet (restrictOrdering he) i) = initialSegSet e i.castSucc := by
  ext x
  simp only [initialSegSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j.castSucc, by simpa using hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k : Fin (n + 2), k.castSucc = j := by
      refine ⟨⟨(j : ℕ), ?_⟩, Fin.ext (by simp)⟩
      have := Fin.le_def.1 hj
      simp only [Fin.val_castSucc] at this
      have := i.isLt
      omega
    exact ⟨⟨e k.castSucc, ne_of_castSucc he k⟩, ⟨k, by simpa using hj, rfl⟩, rfl⟩

/-- **The chambers of the link are the top faces of the chambers of the star.**  Transported into the
apartment, the chain of the restricted ordering is the chain of the original one with its top vertex
removed. -/
theorem coe_properBelowSetOrderIso_symm_chainOfOrdering {e : Fin (n + 3) ≃ ι}
    (he : e (Fin.last (n + 2)) = a) (i : Fin (n + 1)) :
    ((((properBelowSetOrderIso (Set.univ \ {a})).symm
        (chainOfOrdering (restrictOrdering he) i)) :
      {U : properPart (Set ι) // (U : Set ι) < Set.univ \ {a}}) : properPart (Set ι))
      = chainOfOrdering e i.castSucc := by
  refine Subtype.ext ?_
  exact image_initialSegSet_restrictOrdering he i.castSucc

end Restrict

end GaloisForLFunctions.HTGeometry
