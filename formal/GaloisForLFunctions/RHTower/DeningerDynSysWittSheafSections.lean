import Mathlib.CategoryTheory.Sites.LocallySurjective
import GaloisForLFunctions.RHTower.DeningerDynSysWittLocalSections

/-!
# The sections of the sheaf `W_rat (𝒪_X)`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.1.

The sheaf `W_rat (𝒪_X)` is the sheafification of the separated presheaf `U ↦ W_rat (𝒪_X (U))`.
That presheaf is a subpresheaf of the sheaf `W (𝒪_X)`, so the universal property of sheafification
produces a comparison morphism `W_rat (𝒪_X) ⟶ W (𝒪_X)`.  This module proves that the comparison
is injective on sections and that its image over an open `U` is exactly the subring of *locally
rational* big Witt vectors, giving a ring isomorphism

`W_rat (𝒪_X) (U) ≅ {w ∈ W (𝒪_X (U)) | w is locally rational}`.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

universe u

variable {X : TopCat.{u}}

/-- The unit `W_rat (𝒪_X (·)) ⟶ W_rat (𝒪_X)` of the sheafification. -/
noncomputable abbrev deningerRationalWittUnit (F : TopCat.Sheaf CommRingCat.{u} X) :
    deningerRationalWittPresheaf F.1 ⟶ (deningerRationalWittSheaf F).1 :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (deningerRationalWittPresheaf F.1)

/-- The comparison morphism `W_rat (𝒪_X) ⟶ W (𝒪_X)`, obtained from the subpresheaf inclusion by
the universal property of sheafification. -/
noncomputable def deningerRationalWittSheafToBigWitt (F : TopCat.Sheaf CommRingCat.{u} X) :
    (deningerRationalWittSheaf F).1 ⟶ deningerBigWittPresheaf F.1 :=
  CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (deningerRationalWittToBigWittPresheaf F.1) (deningerBigWittPresheaf_isSheaf F)

theorem deningerRationalWittUnit_res (F : TopCat.Sheaf CommRingCat.{u} X) {U V : Opens X}
    (h : V ≤ U) (a : DeningerCanonicalRationalWittRing (F.1.obj (op U))) :
    (deningerRationalWittSheaf F).1.map (homOfLE h).op ((deningerRationalWittUnit F).app (op U) a)
      = (deningerRationalWittUnit F).app (op V)
        (deningerCanonicalRationalWittMap (F.1.map (homOfLE h).op).hom a) := by
  have hn := ConcreteCategory.congr_hom
    ((deningerRationalWittUnit F).naturality (homOfLE h).op) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  exact hn.symm

theorem deningerRationalWittSheafToBigWitt_res (F : TopCat.Sheaf CommRingCat.{u} X)
    {U V : Opens X} (h : V ≤ U) (s : (deningerRationalWittSheaf F).1.obj (op U)) :
    (deningerRationalWittSheafToBigWitt F).app (op V)
        ((deningerRationalWittSheaf F).1.map (homOfLE h).op s)
      = deningerBigWittRingMap (F.1.map (homOfLE h).op).hom
        ((deningerRationalWittSheafToBigWitt F).app (op U) s) := by
  have hn := ConcreteCategory.congr_hom
    ((deningerRationalWittSheafToBigWitt F).naturality (homOfLE h).op) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  exact hn

theorem deningerRationalWittSheafToBigWitt_unit (F : TopCat.Sheaf CommRingCat.{u} X)
    (U : (Opens X)ᵒᵖ) (a : DeningerCanonicalRationalWittRing (F.1.obj U)) :
    (deningerRationalWittSheafToBigWitt F).app U ((deningerRationalWittUnit F).app U a)
      = deningerCanonicalRationalWittEmbedding a := by
  have h := CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (deningerRationalWittToBigWittPresheaf F.1) (deningerBigWittPresheaf_isSheaf F)
  have h3 := ConcreteCategory.congr_hom (CategoryTheory.NatTrans.congr_app h U) a
  rw [CategoryTheory.NatTrans.comp_app, ConcreteCategory.comp_apply] at h3
  exact h3

/-- Every section of `W_rat (𝒪_X)` is, near each point, the image of a rational Witt vector. -/
theorem deningerRationalWittSheaf_exists_local (F : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} (s : (deningerRationalWittSheaf F).1.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ V : Opens X, ∃ h : V ≤ U, x ∈ V ∧
      ∃ a : DeningerCanonicalRationalWittRing (F.1.obj (op V)),
        (deningerRationalWittUnit F).app (op V) a
          = (deningerRationalWittSheaf F).1.map (homOfLE h).op s := by
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (deningerRationalWittUnit F) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (deningerRationalWittPresheaf F.1)))
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (deningerRationalWittUnit F) (U := op U) s
  obtain ⟨V, f, ⟨a, ha⟩, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hmem x hx
  refine ⟨V, f.le, hxV, a, ?_⟩
  rw [ha]
  congr 2

/-- The comparison morphism sends a section of `W_rat (𝒪_X)` to a locally rational big Witt
vector. -/
theorem deningerRationalWittSheafToBigWitt_locallyRational
    (F : TopCat.Sheaf CommRingCat.{u} X) {U : Opens X}
    (s : (deningerRationalWittSheaf F).1.obj (op U)) :
    DeningerWittLocallyRational F.1 U ((deningerRationalWittSheafToBigWitt F).app (op U) s) := by
  intro x hx
  obtain ⟨V, h, hxV, a, ha⟩ := deningerRationalWittSheaf_exists_local F s hx
  refine ⟨V, h, hxV, a, ?_⟩
  rw [← deningerRationalWittSheafToBigWitt_res, ← ha,
    deningerRationalWittSheafToBigWitt_unit]

/-- The comparison morphism is injective on sections: the sections of `W_rat (𝒪_X)` form a subring
of `W (𝒪_X (U))`. -/
theorem deningerRationalWittSheafToBigWitt_injective (F : TopCat.Sheaf CommRingCat.{u} X)
    (U : Opens X) :
    Function.Injective ((deningerRationalWittSheafToBigWitt F).app (op U)) := by
  intro s t hst
  have hs : ∀ x : {x : X // x ∈ U}, ∃ V : Opens X, ∃ h : V ≤ U, (x : X) ∈ V ∧
      ∃ a : DeningerCanonicalRationalWittRing (F.1.obj (op V)),
        (deningerRationalWittUnit F).app (op V) a
          = (deningerRationalWittSheaf F).1.map (homOfLE h).op s :=
    fun x => deningerRationalWittSheaf_exists_local F s x.2
  have ht : ∀ x : {x : X // x ∈ U}, ∃ V : Opens X, ∃ h : V ≤ U, (x : X) ∈ V ∧
      ∃ a : DeningerCanonicalRationalWittRing (F.1.obj (op V)),
        (deningerRationalWittUnit F).app (op V) a
          = (deningerRationalWittSheaf F).1.map (homOfLE h).op t :=
    fun x => deningerRationalWittSheaf_exists_local F t x.2
  choose V hV hxV a ha using hs
  choose W hW hxW b hb using ht
  refine TopCat.Sheaf.eq_of_locally_eq' (deningerRationalWittSheaf F)
    (fun x => V x ⊓ W x) U (fun x => homOfLE (le_trans inf_le_left (hV x))) ?_ s t ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, ⟨hxV ⟨x, hx⟩, hxW ⟨x, hx⟩⟩⟩
  · intro x
    have hsx : (deningerRationalWittSheaf F).1.map
        (homOfLE (le_trans inf_le_left (hV x))).op s
        = (deningerRationalWittUnit F).app (op (V x ⊓ W x))
          (deningerCanonicalRationalWittMap
            (F.1.map (homOfLE (inf_le_left : V x ⊓ W x ≤ V x)).op).hom (a x)) := by
      rw [← deningerRationalWittUnit_res, ha x, ← ConcreteCategory.comp_apply,
        ← (deningerRationalWittSheaf F).1.map_comp]
      congr 2
    have htx : (deningerRationalWittSheaf F).1.map
        (homOfLE (le_trans inf_le_left (hV x))).op t
        = (deningerRationalWittUnit F).app (op (V x ⊓ W x))
          (deningerCanonicalRationalWittMap
            (F.1.map (homOfLE (inf_le_right : V x ⊓ W x ≤ W x)).op).hom (b x)) := by
      rw [← deningerRationalWittUnit_res, hb x, ← ConcreteCategory.comp_apply,
        ← (deningerRationalWittSheaf F).1.map_comp]
      congr 2
    rw [hsx, htx]
    congr 1
    apply deningerCanonicalRationalWittEmbedding_injective
    rw [deningerCanonicalRationalWittEmbedding_map,
      deningerCanonicalRationalWittEmbedding_map]
    have hA : deningerCanonicalRationalWittEmbedding (a x)
        = deningerBigWittRingMap (F.1.map (homOfLE (hV x)).op).hom
          ((deningerRationalWittSheafToBigWitt F).app (op U) s) := by
      rw [← deningerRationalWittSheafToBigWitt_unit, ha x,
        deningerRationalWittSheafToBigWitt_res]
    have hB : deningerCanonicalRationalWittEmbedding (b x)
        = deningerBigWittRingMap (F.1.map (homOfLE (hW x)).op).hom
          ((deningerRationalWittSheafToBigWitt F).app (op U) t) := by
      rw [← deningerRationalWittSheafToBigWitt_unit, hb x,
        deningerRationalWittSheafToBigWitt_res]
    rw [hA, hB, hst, deningerBigWittRing_res_trans, deningerBigWittRing_res_trans]

/-- Every locally rational big Witt vector is a section of `W_rat (𝒪_X)`. -/
theorem deningerRationalWittSheafToBigWitt_surjective (F : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} {w : DeningerBigWittRing (F.1.obj (op U))}
    (hw : DeningerWittLocallyRational F.1 U w) :
    ∃ s : (deningerRationalWittSheaf F).1.obj (op U),
      (deningerRationalWittSheafToBigWitt F).app (op U) s = w := by
  have hw' : ∀ x : {x : X // x ∈ U}, ∃ V : Opens X, ∃ h : V ≤ U, (x : X) ∈ V ∧
      ∃ v : DeningerCanonicalRationalWittRing (F.1.obj (op V)),
        deningerCanonicalRationalWittEmbedding v
          = deningerBigWittRingMap (F.1.map (homOfLE h).op).hom w :=
    fun x => hw x.1 x.2
  choose V hV hxV v hv using hw'
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible (deningerRationalWittSheaf F).1 V
      (fun x => (deningerRationalWittUnit F).app (op (V x)) (v x)) := by
    intro x y
    have hx : (deningerRationalWittSheaf F).1.map (Opens.infLELeft (V x) (V y)).op
        ((deningerRationalWittUnit F).app (op (V x)) (v x))
        = (deningerRationalWittUnit F).app (op (V x ⊓ V y))
          (deningerCanonicalRationalWittMap
            (F.1.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op).hom (v x)) :=
      deningerRationalWittUnit_res F _ _
    have hy : (deningerRationalWittSheaf F).1.map (Opens.infLERight (V x) (V y)).op
        ((deningerRationalWittUnit F).app (op (V y)) (v y))
        = (deningerRationalWittUnit F).app (op (V x ⊓ V y))
          (deningerCanonicalRationalWittMap
            (F.1.map (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op).hom (v y)) :=
      deningerRationalWittUnit_res F _ _
    rw [hx, hy]
    congr 1
    apply deningerCanonicalRationalWittEmbedding_injective
    rw [deningerCanonicalRationalWittEmbedding_map,
      deningerCanonicalRationalWittEmbedding_map, hv x, hv y,
      deningerBigWittRing_res_trans, deningerBigWittRing_res_trans]
  obtain ⟨s, hs, -⟩ := (deningerRationalWittSheaf F).existsUnique_gluing' V U
    (fun x => homOfLE (hV x)) hcover _ hcompat
  refine ⟨s, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (deningerBigWittSheaf F) V U
    (fun x => homOfLE (hV x)) hcover _ _ ?_
  intro x
  show deningerBigWittRingMap (F.1.map (homOfLE (hV x)).op).hom _
    = deningerBigWittRingMap (F.1.map (homOfLE (hV x)).op).hom _
  rw [← deningerRationalWittSheafToBigWitt_res, hs x,
    deningerRationalWittSheafToBigWitt_unit, hv x]

/-- **Deninger, Proposition 2.1.**  The sections of `W_rat (𝒪_X)` over an open `U` are exactly the
locally rational big Witt vectors over `𝒪_X (U)`. -/
noncomputable def deningerRationalWittSheafSectionsEquiv (F : TopCat.Sheaf CommRingCat.{u} X)
    (U : Opens X) :
    (deningerRationalWittSheaf F).1.obj (op U) ≃+* deningerWittLocallyRationalSubring F.1 U :=
  RingEquiv.ofBijective
    (((deningerRationalWittSheafToBigWitt F).app (op U)).hom.codRestrict
      (deningerWittLocallyRationalSubring F.1 U)
      (fun s => deningerRationalWittSheafToBigWitt_locallyRational F s))
    ⟨fun s t hst => deningerRationalWittSheafToBigWitt_injective F U
        (congrArg Subtype.val hst),
     fun w => by
      obtain ⟨s, hs⟩ := deningerRationalWittSheafToBigWitt_surjective F w.2
      exact ⟨s, Subtype.ext hs⟩⟩

@[simp] theorem deningerRationalWittSheafSectionsEquiv_apply (F : TopCat.Sheaf CommRingCat.{u} X)
    (U : Opens X) (s : (deningerRationalWittSheaf F).1.obj (op U)) :
    (deningerRationalWittSheafSectionsEquiv F U s : DeningerBigWittRing (F.1.obj (op U)))
      = (deningerRationalWittSheafToBigWitt F).app (op U) s := rfl

end RHTower
