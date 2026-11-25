import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Free
import Mathlib.Tactic.Algebraize
import Mathlib.Topology.JacobsonSpace

/-! Generic freeness gives a nonempty open of flatness for a dominant finite morphism.
On a Jacobson scheme, flatness can also be checked at closed points. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory.FiniteEndFlat

private theorem flat_iff_comp_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  letI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C

private theorem flat_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y) trivial
  rw [flat_iff_comp_germ hU hy, TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _

private theorem flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y)
    {x y : X} (h : x ⤳ y) (hf : (f.stalkMap y).hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := f y) trivial
  have he : f x ⤳ f y := h.map f.continuous
  rw [flat_iff_comp_germ hU (he.mem_open U.2 hy),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hy he, Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x y h, ← flat_iff_comp_germ hU hy]
  exact hf.comp (flat_stalkSpecializes h)

/-- Flatness at every closed point suffices on a Jacobson source. -/
theorem flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)

private theorem exists_flat_away {A B : Type} [CommRing A] [CommRing B] [IsDomain A]
    [IsNoetherianRing A] (φ : A →+* B) (hφ : φ.Finite) :
    ∃ r : A, r ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra B C] [IsLocalization.Away (φ r) C],
      ((algebraMap B C).comp φ).Flat := by
  algebraize [φ]
  letI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) B) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun C _ _ _ => ?_⟩
  letI : Algebra A C := ((algebraMap B C).comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers r)) C := by
    rw [Algebra.algebraMapSubmonoid_powers]
    assumption
  haveI : Module.Flat A (LocalizedModule (Submonoid.powers r) B) :=
    Module.Flat.trans A (Localization (Submonoid.powers r)) _
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers r) (IsScalarTower.toAlgHom A B C).toLinearMap).symm

/-- A finite morphism that carries the generic point to the generic point is flat on
a nonempty open of its source. -/
theorem exists_open_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f (genericPoint X) = genericPoint Y) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, (f.stalkMap x).hom.Flat := by
  obtain ⟨U, hU, hξ, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := genericPoint Y) trivial
  haveI : Nonempty U := ⟨⟨_, hξ⟩⟩
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨r, hr, H⟩ := exists_flat_away (f.app U).hom (f.finite_app U hU)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  refine ⟨X.basicOpen (f.app U r), ⟨genericPoint X, ?_⟩, fun x hx => ?_⟩
  · rw [← Scheme.preimage_basicOpen, SetLike.mem_coe, Scheme.Hom.mem_preimage, hf]
    refine ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen r).2).mpr ?_
    rw [Set.univ_inter]
    exact (Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)
  · haveI := hV.isLocalization_basicOpen (f.app U r)
    have h := H Γ(X, X.basicOpen (f.app U r))
    have hxU : x ∈ f ⁻¹ᵁ U := X.basicOpen_le _ hx
    have hg : (X.presheaf.germ _ x hx).hom.Flat := by
      rw [← Category.comp_id (X.presheaf.germ _ x hx), ← flat_iff_comp_germ (hV.basicOpen _)]
      exact RingHom.Flat.id _
    rw [flat_iff_comp_germ hU (x := f x) hxU, f.germ_stalkMap U x hxU,
      ← X.presheaf.germ_res (homOfLE (X.basicOpen_le (f.app U r))) x hx]
    exact h.comp hg

end GlobalTheory.FiniteEndFlat
