/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §2.

The sentence "the presheaf `U ↦ W_rat (𝒪_X (U))` is a sub-presheaf of the sheaf `W (𝒪_X)`, hence
it is separated" is made literal here: the big Witt vectors form a functor
`W : CommRingCat ⥤ CommRingCat`, the presheaf `U ↦ W (𝒪_X (U))` attached to a **sheaf** of
commutative rings is again a **sheaf** — a big Witt vector is a power series with constant term
`1`, so gluing is gluing of each coefficient and the constant term glues to `1` by separatedness —
and the canonical embedding `W_rat (A) ↪ W (A)` is a natural transformation whose components are
injective.

This is the sheaf `W (𝒪_X)` in which Deninger's Proposition 2.1(c) describes the sections of
`W_rat (𝒪_X)`.
-/
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import GaloisForLFunctions.RHTower.DeningerDynSysRationalWittPresheaf

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

universe u

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The power series underlying a big Witt vector. -/
def deningerDynSysBigWittSeries (w : DeningerBigWittRing A) : PowerSeries A :=
  deningerBigWittSeries (Additive.toMul w.additiveVal)

theorem deningerDynSysBigWittSeries_injective :
    Function.Injective (deningerDynSysBigWittSeries (A := A)) := by
  intro x y h
  apply DeningerBigWittRing.ext
  apply Additive.toMul.injective
  exact deningerBigWittSeries_injective h

@[simp] theorem deningerDynSysBigWittSeries_constantCoeff (w : DeningerBigWittRing A) :
    PowerSeries.constantCoeff (deningerDynSysBigWittSeries w) = 1 :=
  deningerBigWittSeries_constantCoeff _

/-- A power series with constant term `1` as a big Witt vector. -/
noncomputable def deningerDynSysBigWittOfSeries (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) : DeningerBigWittRing A :=
  ⟨Additive.ofMul (deningerBigWittOfSeries f hf)⟩

@[simp] theorem deningerDynSysBigWittSeries_ofSeries (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) :
    deningerDynSysBigWittSeries (deningerDynSysBigWittOfSeries f hf) = f := rfl

theorem deningerDynSysBigWittSeries_map (f : A →+* B) (w : DeningerBigWittRing A) :
    deningerDynSysBigWittSeries (deningerBigWittRingMap f w)
      = PowerSeries.map f (deningerDynSysBigWittSeries w) := by
  show deningerBigWittSeries (Additive.toMul
      (deningerBigWittRingMap f w).additiveVal) = _
  rw [deningerBigWittRingMap_additiveVal]
  simp [deningerDynSysBigWittSeries]

/-- **The big Witt functor** `A ↦ W (A)` on commutative rings. -/
noncomputable def deningerBigWittFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj A := CommRingCat.of (DeningerBigWittRing A)
  map f := CommRingCat.ofHom (deningerBigWittRingMap f.hom)
  map_id A := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show deningerBigWittRingMap (CommRingCat.Hom.hom (𝟙 A)) w = w
    rw [CommRingCat.hom_id]
    exact deningerBigWittRingMap_id w
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show deningerBigWittRingMap (CommRingCat.Hom.hom (f ≫ g)) w
        = deningerBigWittRingMap (CommRingCat.Hom.hom g)
          (deningerBigWittRingMap (CommRingCat.Hom.hom f) w)
    rw [CommRingCat.hom_comp]
    exact deningerBigWittRingMap_comp _ _ w

/-- The big Witt presheaf `U ↦ W (𝒪 (U))`. -/
noncomputable def deningerBigWittPresheaf {X : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} X) : TopCat.Presheaf CommRingCat.{u} X :=
  F ⋙ deningerBigWittFunctor

theorem deningerBigWittPresheaf_map_series {X : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} X)
    {V W : Opens X} (h : V ⟶ W) (w : DeningerBigWittRing (F.obj (op W))) :
    deningerDynSysBigWittSeries ((deningerBigWittPresheaf F).map h.op w)
      = PowerSeries.map (F.map h.op).hom (deningerDynSysBigWittSeries w) :=
  deningerDynSysBigWittSeries_map _ _

/-- **The big Witt presheaf of a sheaf of commutative rings is a sheaf.**  A big Witt vector is a
power series with constant term `1`, so gluing is gluing of each coefficient. -/
theorem deningerBigWittPresheaf_isSheaf {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X) :
    (deningerBigWittPresheaf F.1).IsSheaf := by
  rw [isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  have hFsheaf := (isSheaf_iff_isSheafUniqueGluing (F := F.1)).1 F.2
  have hcoeffcompat : ∀ n : ℕ, IsCompatible F.1 U
      (fun i => PowerSeries.coeff n (deningerDynSysBigWittSeries (sf i))) := by
    intro n i j
    have h1 := congrArg (fun w => PowerSeries.coeff n (deningerDynSysBigWittSeries w)) (hcompat i j)
    simpa [deningerBigWittPresheaf_map_series, PowerSeries.coeff_map] using h1
  choose a ha hauniq using fun n => hFsheaf U _ (hcoeffcompat n)
  have ha0 : a 0 = 1 := by
    refine (hauniq 0 1 ?_).symm
    intro i
    have hone : PowerSeries.coeff 0 (deningerDynSysBigWittSeries (sf i)) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, deningerDynSysBigWittSeries_constantCoeff]
    show (F.1.map _).hom 1 = _
    rw [map_one]
    exact hone.symm
  have hconst : PowerSeries.constantCoeff (PowerSeries.mk a) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk, ha0]
  refine ⟨deningerDynSysBigWittOfSeries (PowerSeries.mk a) hconst, ?_, ?_⟩
  · intro i
    apply deningerDynSysBigWittSeries_injective
    rw [deningerBigWittPresheaf_map_series, deningerDynSysBigWittSeries_ofSeries]
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact ha n i
  · intro y hy
    apply deningerDynSysBigWittSeries_injective
    apply PowerSeries.ext
    intro n
    rw [deningerDynSysBigWittSeries_ofSeries, PowerSeries.coeff_mk]
    refine hauniq n _ ?_
    intro i
    have h1 := congrArg (fun w => PowerSeries.coeff n (deningerDynSysBigWittSeries w)) (hy i)
    simpa [deningerBigWittPresheaf_map_series, PowerSeries.coeff_map] using h1

/-- The big Witt sheaf `W (𝒪_X)`. -/
noncomputable def deningerBigWittSheaf {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X) :
    TopCat.Sheaf CommRingCat.{u} X :=
  ⟨deningerBigWittPresheaf F.1, deningerBigWittPresheaf_isSheaf F⟩

/-! ### `W_rat` as a subpresheaf of the big Witt sheaf -/

/-- The canonical embedding `W_rat (A) ↪ W (A)` as a natural transformation of functors. -/
noncomputable def deningerRationalWittToBigWitt :
    deningerRationalWittFunctor.{u} ⟶ deningerBigWittFunctor.{u} where
  app A := CommRingCat.ofHom (deningerCanonicalRationalWittEmbedding (A := A))
  naturality A B f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    show deningerCanonicalRationalWittEmbedding
        (deningerCanonicalRationalWittMapFun (CommRingCat.Hom.hom f) w)
      = deningerBigWittRingMap (CommRingCat.Hom.hom f)
        (deningerCanonicalRationalWittEmbedding w)
    exact deningerCanonicalRationalWittEmbedding_mapFun _ _

/-- **Deninger, §2.**  The rational Witt presheaf is a subpresheaf of the big Witt sheaf. -/
noncomputable def deningerRationalWittToBigWittPresheaf {X : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} X) :
    deningerRationalWittPresheaf F ⟶ deningerBigWittPresheaf F :=
  CategoryTheory.Functor.whiskerLeft F deningerRationalWittToBigWitt

theorem deningerRationalWittToBigWittPresheaf_injective {X : TopCat.{u}}
    (F : TopCat.Presheaf CommRingCat.{u} X) (V : (Opens X)ᵒᵖ) :
    Function.Injective ((deningerRationalWittToBigWittPresheaf F).app V) :=
  fun _ _ h => deningerCanonicalRationalWittEmbedding_injective h

end RHTower
