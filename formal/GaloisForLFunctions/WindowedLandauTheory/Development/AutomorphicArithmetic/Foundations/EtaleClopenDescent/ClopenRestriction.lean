import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! Finite morphisms restrict to clopen subschemes over an open target. -/

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Cb

/-- A clopen subscheme of the inverse image of an open remains finite over that open. -/
theorem finite_resLE_of_clopen {X Y : Scheme} (f : X ⟶ Y) [IsFinite f]
    (U : Y.Opens) (V : X.Opens) (hV : IsClosed (V : Set X)) (h : V ≤ f ⁻¹ᵁ U) :
    IsFinite (f.resLE U V h) := by
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion V.ι (by simpa using hV)
  haveI : IsClosedImmersion (X.homOfLE h ≫ (f ⁻¹ᵁ U).ι) := by
    rw [Scheme.homOfLE_ι]
    infer_instance
  haveI : IsClosedImmersion (X.homOfLE h) :=
    IsClosedImmersion.of_comp _ ((f ⁻¹ᵁ U).ι)
  show IsFinite (X.homOfLE h ≫ f ∣_ U)
  infer_instance

/-- A map from a one-point scheme factors through a unique member of a disjoint open cover. -/
theorem existsUnique_lift_one_point {X Y : Scheme} [Subsingleton X] {J : Type*}
    (f : X ⟶ Y) (x₀ : X) (U : J → Y.Opens)
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcover : iSup U = ⊤) :
    ∃! j, ∃! g : X ⟶ (U j).toScheme, g ≫ (U j).ι = f := by
  have hm : f x₀ ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  have hr : Set.range f ⊆ Set.range (U j).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x₀, Scheme.Opens.range_ι]
    exact hj
  refine ⟨j, ⟨IsOpenImmersion.lift (U j).ι f hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩, ?_⟩
  · intro g hg
    exact (cancel_mono (U j).ι).mp (hg.trans (IsOpenImmersion.lift_fac _ _ _).symm)
  · rintro l ⟨g, hg, -⟩
    by_contra hlj
    have hl : f x₀ ∈ U l := by
      rw [← hg, Scheme.Hom.comp_apply]
      exact (g x₀).2
    have hc : f x₀ ∈ U l ⊓ U j := ⟨hl, hj⟩
    rw [hdis l j hlj] at hc
    exact hc

end UpperTheory.Cb
