import GaloisForLFunctions.HTGeometry.StokesCellularGermCompatibility

/-!
# Object descent for cellular Stokes germs

A family of local wall germs comes from a global cyclic boundary representation exactly when its
two copies of each arc stalk are isomorphic. Chosen arc-gluing isomorphisms construct a global
quiver representation, and explicit cospan isomorphisms recover the original local family.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

open CellularMicrolocal

/-- Object-level descent condition: the two local copies of every arc stalk are isomorphic. -/
def HasCompatibleArcGluing {k : ℕ} (hk : 0 < k) (K : GermFamily k) : Prop :=
  ∀ v : StokesWall k, Nonempty
    (((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
      ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))

private def initialIncidenceAt {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))
    (v w : StokesWall k) (h : nextWall hk v = w) :
    (K.obj (Discrete.mk w)).obj WalkingCospan.right ⟶
      (K.obj (Discrete.mk v)).obj WalkingCospan.one := by
  subst w
  exact (e v).inv ≫ (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inl

private def initialIncidence {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))
    (w : StokesWall k) :
    (K.obj (Discrete.mk w)).obj WalkingCospan.right ⟶
      (K.obj (Discrete.mk (prevWall hk w))).obj WalkingCospan.one :=
  initialIncidenceAt hk K e (prevWall hk w) w (nextWall_prevWall hk w)

private def terminalIncidenceAt {k : ℕ} (_hk : 0 < k) (K : GermFamily k)
    (v w : StokesWall k) (h : v = w) :
    (K.obj (Discrete.mk w)).obj WalkingCospan.right ⟶
      (K.obj (Discrete.mk v)).obj WalkingCospan.one := by
  subst v
  exact (K.obj (Discrete.mk w)).map WalkingCospan.Hom.inr

private def terminalIncidence {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (w : StokesWall k) :
    (K.obj (Discrete.mk w)).obj WalkingCospan.right ⟶
      (K.obj (Discrete.mk (prevWall hk (nextWall hk w)))).obj WalkingCospan.one :=
  terminalIncidenceAt hk K (prevWall hk (nextWall hk w)) w
    (prevWall_nextWall hk w)

/-- Quiver representation glued from local germs and chosen duplicated-arc identifications. -/
def gluedBoundaryPrefunctor {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right)) :
    BoundaryQuiver k hk ⥤q ModuleCat ℚ where
  obj
    | .arc w => (K.obj (Discrete.mk w)).obj WalkingCospan.right
    | .wall w => (K.obj (Discrete.mk (prevWall hk w))).obj WalkingCospan.one
  map := by
    intro X Y f
    change BoundaryArrow k hk X Y at f
    cases f with
    | initial w => exact initialIncidence hk K e w
    | terminal w => exact terminalIncidence hk K w

/-- Global cyclic boundary object glued from local germs and chosen arc identifications. -/
def gluedBoundaryObject {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right)) :
    BoundaryCategory k hk :=
  CategoryTheory.Paths.lift (gluedBoundaryPrefunctor hk K e)

private def centerReindexIso {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (v : StokesWall k) :
    (K.obj (Discrete.mk (prevWall hk (nextWall hk v)))).obj WalkingCospan.one ≅
      (K.obj (Discrete.mk v)).obj WalkingCospan.one :=
  eqToIso (congrArg
    (fun w => (K.obj (Discrete.mk w)).obj WalkingCospan.one)
    (prevWall_nextWall hk v))

private theorem initialIncidenceAt_reindex {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))
    (u v : StokesWall k) (p : u = v) (q : nextWall hk u = nextWall hk v) :
    initialIncidenceAt hk K e u (nextWall hk v) q ≫
        eqToHom (congrArg
          (fun w => (K.obj (Discrete.mk w)).obj WalkingCospan.one) p) =
      (e v).inv ≫ (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inl := by
  subst u
  rfl

private theorem terminalIncidenceAt_reindex {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (u v : StokesWall k) (p : u = v) :
    terminalIncidenceAt hk K u v p ≫
        eqToHom (congrArg
          (fun w => (K.obj (Discrete.mk w)).obj WalkingCospan.one) p) =
      (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inr := by
  subst u
  rfl

private theorem initialIncidence_next {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))
    (v : StokesWall k) :
    initialIncidence hk K e (nextWall hk v) ≫ (centerReindexIso hk K v).hom =
      (e v).inv ≫ (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inl := by
  exact initialIncidenceAt_reindex hk K e
    (prevWall hk (nextWall hk v)) v (prevWall_nextWall hk v)
    (nextWall_prevWall hk (nextWall hk v))

private theorem terminalIncidence_center {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (v : StokesWall k) :
    terminalIncidence hk K v ≫ (centerReindexIso hk K v).hom =
      (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inr := by
  exact terminalIncidenceAt_reindex hk K
    (prevWall hk (nextWall hk v)) v (prevWall_nextWall hk v)

/-- Each local restriction of a glued boundary object recovers its input germ. -/
noncomputable def gluedBoundaryLocalIso {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right))
    (v : StokesWall k) :
    ((allLocalGermRestrictions k hk).obj (gluedBoundaryObject hk K e)).obj
        (Discrete.mk v) ≅ K.obj (Discrete.mk v) := by
  refine cospanIsoMk (centerReindexIso hk K v) (e v).symm (Iso.refl _) ?_ ?_
  · change initialIncidence hk K e (nextWall hk v) ≫
        (centerReindexIso hk K v).hom =
      (e v).inv ≫ (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inl
    exact initialIncidence_next hk K e v
  · change terminalIncidence hk K v ≫ (centerReindexIso hk K v).hom =
      (K.obj (Discrete.mk v)).map WalkingCospan.Hom.inr
    exact terminalIncidence_center hk K v

/-- Simultaneous local restriction of a glued boundary object recovers its input family. -/
noncomputable def gluedBoundaryFamilyIso {k : ℕ} (hk : 0 < k) (K : GermFamily k)
    (e : ∀ v : StokesWall k,
      ((K.obj (Discrete.mk v)).obj WalkingCospan.left) ≅
        ((K.obj (Discrete.mk (nextWall hk v))).obj WalkingCospan.right)) :
    (allLocalGermRestrictions k hk).obj (gluedBoundaryObject hk K e) ≅ K :=
  Discrete.natIso fun v => gluedBoundaryLocalIso hk K e v.as

/-- Local restrictions of every global boundary object have compatible duplicated arc stalks. -/
theorem allLocalGermRestrictions_hasCompatibleArcGluing {k : ℕ} (hk : 0 < k)
    (F : BoundaryCategory k hk) :
    HasCompatibleArcGluing hk ((allLocalGermRestrictions k hk).obj F) := by
  intro v
  exact ⟨Iso.refl _⟩

/-- Compatible arc gluing is invariant under isomorphism of local-germ families. -/
theorem HasCompatibleArcGluing.of_iso {k : ℕ} (hk : 0 < k)
    {K L : GermFamily k} (e : K ≅ L) (hK : HasCompatibleArcGluing hk K) :
    HasCompatibleArcGluing hk L := by
  intro v
  exact ⟨((e.app (Discrete.mk v)).app WalkingCospan.left).symm ≪≫
    Classical.choice (hK v) ≪≫
    (e.app (Discrete.mk (nextWall hk v))).app WalkingCospan.right⟩

/-- Exact object-level essential-image characterization for simultaneous local restriction. -/
theorem mem_allLocalGermRestrictions_essImage_iff {k : ℕ} (hk : 0 < k)
    (K : GermFamily k) :
    (allLocalGermRestrictions k hk).essImage K ↔ HasCompatibleArcGluing hk K := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact HasCompatibleArcGluing.of_iso hk e
      (allLocalGermRestrictions_hasCompatibleArcGluing hk F)
  · intro hK
    let e := fun v : StokesWall k => Classical.choice (hK v)
    exact ⟨gluedBoundaryObject hk K e, ⟨gluedBoundaryFamilyIso hk K e⟩⟩

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
