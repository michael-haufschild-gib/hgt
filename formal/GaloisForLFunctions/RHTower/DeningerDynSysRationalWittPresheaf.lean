/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §2, Proposition 2.1(a).

The rational Witt vectors form a functor `W_rat : CommRingCat ⥤ CommRingCat`, so composing with
the structure sheaf of a scheme gives the presheaf `U ↦ W_rat (𝒪_X (U))` of Definition 2.2.  This
file proves that presheaf is **separated** for the structure sheaf of any ringed space: a rational
Witt vector is determined by the coefficients of its underlying power series, those coefficients
are natural in the coefficient ring, and the structure sheaf is separated coefficientwise.

The functoriality laws `W_rat (id) = id` and `W_rat (g ∘ f) = W_rat (g) ∘ W_rat (f)` are proved
here as well; they follow from the corresponding laws for the big Witt ring together with the
injectivity and naturality of the canonical embedding `W_rat (A) ↪ W (A)`.
-/
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import GaloisForLFunctions.RHTower.DeningerRationalWittCanonicalMultiplication

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

/-! ### Functoriality -/

@[simp] theorem deningerCanonicalRationalWittMap_id (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittMap (RingHom.id A) w = w := by
  apply deningerCanonicalRationalWittEmbedding_injective
  show deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun (RingHom.id A) w) = _
  rw [deningerCanonicalRationalWittEmbedding_mapFun, deningerBigWittRingMap_id]

@[simp] theorem deningerCanonicalRationalWittMap_comp {D : Type*} [CommRing D]
    (g : B →+* D) (f : A →+* B) (w : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittMap (g.comp f) w
      = deningerCanonicalRationalWittMap g (deningerCanonicalRationalWittMap f w) := by
  apply deningerCanonicalRationalWittEmbedding_injective
  show deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun (g.comp f) w) = _
  rw [deningerCanonicalRationalWittEmbedding_mapFun, deningerBigWittRingMap_comp]
  show _ = deningerCanonicalRationalWittEmbedding
      (deningerCanonicalRationalWittMapFun g (deningerCanonicalRationalWittMapFun f w))
  rw [deningerCanonicalRationalWittEmbedding_mapFun,
    deningerCanonicalRationalWittEmbedding_mapFun]

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

end RHTower
