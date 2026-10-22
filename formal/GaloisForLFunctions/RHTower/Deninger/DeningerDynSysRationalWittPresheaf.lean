/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §2:
Proposition 2.1(a) (`t22n`) and Definitions 2.2, 2.3 (`t23n`).

The rational Witt vectors form a functor `W_rat : CommRingCat ⥤ CommRingCat`, so composing with
the structure sheaf of a ringed space gives the presheaf `U ↦ W_rat (𝒪_X (U))` of Definition 2.2.
This file proves that presheaf is **separated**: a rational Witt vector is determined by the
coefficients of its underlying power series, those coefficients are natural in the coefficient
ring, and the structure sheaf is separated coefficientwise.  Separatedness is proved both in the
concrete open-cover form and in the site-theoretic form, and the latter yields the second half of
Proposition 2.1(a): the unit of the sheafification is injective on sections, i.e.

  `W_rat (𝒪_X (U)) ⊆ W_rat (𝒪_X) (U)`.

Definition 2.3, the rational Witt space `W_rat (X) = (X_top, W_rat (𝒪_X))`, is then a sheafed
space over `CommRingCat`.

The functoriality laws `W_rat (id) = id` and `W_rat (g ∘ f) = W_rat (g) ∘ W_rat (f)` are proved
here as well; they follow from the corresponding laws for the big Witt ring together with the
injectivity and naturality of the canonical embedding `W_rat (A) ↪ W (A)`.
-/
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Geometry.RingedSpace.SheafedSpace
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFunctoriality

namespace RHTower

open CategoryTheory TopologicalSpace Opposite

universe u

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The power series underlying a rational Witt vector. -/
noncomputable def deningerRationalWittSeries (w : DeningerCanonicalRationalWittRing A) :
    PowerSeries A :=
  deningerBigWittSeries (Additive.toMul (deningerCanonicalRationalWittEmbedding w).additiveVal)

theorem deningerBigWittSeries_injective :
    Function.Injective (deningerBigWittSeries (A := A)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem deningerRationalWittSeries_injective :
    Function.Injective (deningerRationalWittSeries (A := A)) := by
  intro x y h
  apply deningerCanonicalRationalWittEmbedding_injective
  apply DeningerBigWittRing.ext
  apply Additive.toMul.injective
  exact deningerBigWittSeries_injective h

theorem deningerRationalWittSeries_map (f : A →+* B) (w : DeningerCanonicalRationalWittRing A) :
    deningerRationalWittSeries (deningerCanonicalRationalWittMap f w)
      = PowerSeries.map f (deningerRationalWittSeries w) := by
  show deningerBigWittSeries
      (Additive.toMul (deningerCanonicalRationalWittEmbedding
        (deningerCanonicalRationalWittMapFun f w)).additiveVal) = _
  rw [deningerCanonicalRationalWittEmbedding_mapFun, deningerBigWittRingMap_additiveVal]
  simp [deningerRationalWittSeries]

/-- **The rational Witt functor** `A ↦ W_rat (A)` on commutative rings. -/
noncomputable def deningerRationalWittFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (DeningerCanonicalRationalWittRing A)
  map f := CommRingCat.ofHom (deningerCanonicalRationalWittMap f.hom)
  map_id A := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show deningerCanonicalRationalWittMap (CommRingCat.Hom.hom (𝟙 A)) w = w
    rw [CommRingCat.hom_id]
    exact deningerCanonicalRationalWittMap_id w
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show deningerCanonicalRationalWittMap (CommRingCat.Hom.hom (f ≫ g)) w
        = deningerCanonicalRationalWittMap (CommRingCat.Hom.hom g)
          (deningerCanonicalRationalWittMap (CommRingCat.Hom.hom f) w)
    rw [CommRingCat.hom_comp]
    exact deningerCanonicalRationalWittMap_comp _ _ w

/-- **Deninger, Definition 2.2, structure presheaf.**  The presheaf `U ↦ W_rat (𝒪 (U))`. -/
noncomputable def deningerRationalWittPresheaf {X : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} X) : TopCat.Presheaf CommRingCat.{u} X :=
  F ⋙ deningerRationalWittFunctor

/-- **Deninger, Proposition 2.1(a).**  For any sheaf of commutative rings the presheaf of rational
Witt vectors is separated: two rational Witt vectors over `𝒪(V)` agreeing on an open cover of `V`
are equal. -/
theorem deningerRationalWittPresheaf_separated {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s t : DeningerCanonicalRationalWittRing (F.1.obj (op V)))
    (h : ∀ i, deningerCanonicalRationalWittMap (F.1.map (iUV i).op).hom s
            = deningerCanonicalRationalWittMap (F.1.map (iUV i).op).hom t) :
    s = t := by
  apply deningerRationalWittSeries_injective
  apply PowerSeries.ext
  intro n
  refine TopCat.Sheaf.eq_of_locally_eq' F U V iUV hcover _ _ ?_
  intro i
  have hi := congrArg deningerRationalWittSeries (h i)
  rw [deningerRationalWittSeries_map, deningerRationalWittSeries_map] at hi
  have hcoeff := congrArg (PowerSeries.coeff n) hi
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at hcoeff
  exact hcoeff

/-- **Deninger, Proposition 2.1(a)**, in presheaf form: the rational Witt presheaf of a sheaf of
commutative rings is separated. -/
theorem deningerRationalWittPresheaf_isSeparated {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (V : Opens X) (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U)
    (s t : (deningerRationalWittPresheaf F.1).obj (op V))
    (h : ∀ i, ((deningerRationalWittPresheaf F.1).map (iUV i).op).hom s
            = ((deningerRationalWittPresheaf F.1).map (iUV i).op).hom t) :
    s = t :=
  deningerRationalWittPresheaf_separated F U V iUV hcover s t h

/-- **Deninger, Proposition 2.1(a)**, in the site-theoretic form used for sheafification. -/
theorem deningerRationalWittPresheaf_isSeparated_site {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) :
    Presheaf.IsSeparated (Opens.grothendieckTopology X) (deningerRationalWittPresheaf F.1) := by
  intro V S hS x y h
  refine deningerRationalWittPresheaf_separated F
    (ι := Σ V' : Opens X, {f : V' ⟶ V // S.arrows f}) (fun i => i.1) V (fun i => i.2.1) ?_ x y ?_
  · intro z hz
    obtain ⟨V', f, hf, hzV⟩ := (Opens.mem_grothendieckTopology _).1 hS z hz
    exact Opens.mem_iSup.2 ⟨⟨V', f, hf⟩, hzV⟩
  · intro i
    exact h i.1 i.2.1 i.2.2

/-- The separatedness of the rational Witt presheaf, in the form required by
`Presheaf.isLocallyInjective_iff_injective_of_separated`. -/
theorem deningerRationalWittPresheaf_isSeparated_forget {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) :
    Presieve.IsSeparated (Opens.grothendieckTopology X)
      (deningerRationalWittPresheaf F.1 ⋙ forget CommRingCat.{u}) := by
  intro V S hS fam t₁ t₂ h₁ h₂
  refine deningerRationalWittPresheaf_isSeparated_site F V S hS t₁ t₂ ?_
  intro W f hf
  exact (h₁ f hf).trans (h₂ f hf).symm

/-- **Deninger, Proposition 2.1(a), second half.**  Because the rational Witt presheaf is
separated, its sections inject into the sections of its sheafification:
`W_rat (𝒪_X (U)) ⊆ W_rat (𝒪_X) (U)`. -/
theorem deningerRationalWittPresheaf_toSheafify_injective {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) (V : (Opens X)ᵒᵖ) :
    Function.Injective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (deningerRationalWittPresheaf F.1)).app V) :=
  (Presheaf.isLocallyInjective_iff_injective_of_separated _ _
    (deningerRationalWittPresheaf_isSeparated_forget F)).1 inferInstance V

/-! ### The rational Witt space -/

/-- **Deninger, §2.**  The sheaf `W_rat (𝒪_X)`: the sheafification of the separated presheaf
`U ↦ W_rat (𝒪_X (U))`. -/
noncomputable def deningerRationalWittSheaf {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) : TopCat.Sheaf CommRingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    (deningerRationalWittPresheaf F.1)

/-- **Deninger, Definition 2.3 (`t23n`).**  The rational Witt space of a ringed space: the same
underlying topological space, equipped with the structure sheaf `W_rat (𝒪_X)`. -/
noncomputable def deningerRationalWittSpace {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) : AlgebraicGeometry.SheafedSpace CommRingCat.{u} where
  carrier := X
  presheaf := (deningerRationalWittSheaf F).1
  IsSheaf := (deningerRationalWittSheaf F).2

@[simp] theorem deningerRationalWittSpace_carrier {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) :
    (deningerRationalWittSpace F).carrier = X := rfl

@[simp] theorem deningerRationalWittSpace_presheaf {X : TopCat.{u}}
    (F : TopCat.Sheaf CommRingCat.{u} X) :
    (deningerRationalWittSpace F).presheaf = (deningerRationalWittSheaf F).1 := rfl

end RHTower
