import GaloisForLFunctions.HTGeometry.StokesCellularGermDescent
import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Compatibility of local Stokes-germ morphisms

Every arc occurs twice in the simultaneous local-germ family: as the left object of one germ and
the right object of its successor. Global boundary morphisms necessarily agree on these two
copies. This is the exact necessary compatibility law for morphism-level descent.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

open CellularMicrolocal

/-- Local germ morphisms are compatible when their two components on every duplicated arc
agree. -/
def IsCompatibleLocalMorphism {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G) : Prop :=
  ∀ v : StokesWall k,
    (η.app (Discrete.mk v)).app WalkingCospan.left =
      (η.app (Discrete.mk (nextWall hk v))).app WalkingCospan.right

/-- Restriction of every global boundary morphism is compatible on duplicated arcs. -/
theorem allLocalGermRestrictions_map_compatible {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk} (α : F ⟶ G) :
    IsCompatibleLocalMorphism hk ((allLocalGermRestrictions k hk).map α) := by
  intro v
  rfl

private def localWallComponent {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (v w : StokesWall k) (h : nextWall hk v = w) :
    F.obj (.wall w) ⟶ G.obj (.wall w) := by
  subst w
  exact (η.app (Discrete.mk v)).app WalkingCospan.one

private theorem localWallComponent_initial {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (hη : IsCompatibleLocalMorphism hk η)
    (v w : StokesWall k) (h : nextWall hk v = w) :
    F.map (initialBoundaryPath hk w) ≫ localWallComponent hk η v w h =
      (η.app (Discrete.mk w)).app WalkingCospan.right ≫
        G.map (initialBoundaryPath hk w) := by
  subst w
  rw [← hη v]
  exact (η.app (Discrete.mk v)).naturality WalkingCospan.Hom.inl

private theorem localWallComponent_terminal {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (v : StokesWall k) :
    F.map (terminalBoundaryPath hk v) ≫
        localWallComponent hk η v (nextWall hk v) rfl =
      (η.app (Discrete.mk v)).app WalkingCospan.right ≫
        G.map (terminalBoundaryPath hk v) := by
  exact (η.app (Discrete.mk v)).naturality WalkingCospan.Hom.inr

private def predecessorWallComponent {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (w : StokesWall k) : F.obj (.wall w) ⟶ G.obj (.wall w) :=
  localWallComponent hk η (prevWall hk w) w (nextWall_prevWall hk w)

private theorem predecessorWallComponent_next {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (v : StokesWall k) :
    predecessorWallComponent hk η (nextWall hk v) =
      localWallComponent hk η v (nextWall hk v) rfl := by
  simp only [predecessorWallComponent, prevWall_nextWall]

/-- A compatible family of local germ morphisms glues to a global boundary morphism. -/
def compatibleLocalMorphismLift {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (hη : IsCompatibleLocalMorphism hk η) : F ⟶ G :=
  CategoryTheory.Paths.liftNatTrans
    (fun cell => match cell with
      | .arc v => (η.app (Discrete.mk v)).app WalkingCospan.right
      | .wall w => predecessorWallComponent hk η w)
    (fun {X Y} f => by
      change BoundaryArrow k hk X Y at f
      cases f with
      | initial w =>
          exact localWallComponent_initial hk η hη
            (prevWall hk w) w (nextWall_prevWall hk w)
      | terminal w =>
          change F.map (terminalBoundaryPath hk w) ≫
              predecessorWallComponent hk η (nextWall hk w) =
            (η.app (Discrete.mk w)).app WalkingCospan.right ≫
              G.map (terminalBoundaryPath hk w)
          rw [predecessorWallComponent_next]
          exact localWallComponent_terminal hk η w)

/-- Restricting a glued compatible morphism recovers the original local family. -/
theorem allLocalGermRestrictions_map_compatibleLocalMorphismLift {k : ℕ}
    (hk : 0 < k) {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G)
    (hη : IsCompatibleLocalMorphism hk η) :
    (allLocalGermRestrictions k hk).map (compatibleLocalMorphismLift hk η hη) = η := by
  apply NatTrans.ext
  funext v
  apply NatTrans.ext
  funext X
  rcases v with ⟨v⟩
  cases X with
  | none =>
      change predecessorWallComponent hk η (nextWall hk v) =
        (η.app (Discrete.mk v)).app WalkingCospan.one
      rw [predecessorWallComponent_next]
      rfl
  | some b =>
      cases b with
      | left =>
          change (η.app (Discrete.mk (nextWall hk v))).app WalkingCospan.right =
            (η.app (Discrete.mk v)).app WalkingCospan.left
          exact (hη v).symm
      | right =>
          rfl

/-- Compatibility is exactly existence and uniqueness of a global boundary-morphism lift. -/
theorem compatible_iff_existsUnique_lift {k : ℕ} (hk : 0 < k)
    {F G : BoundaryCategory k hk}
    (η : (allLocalGermRestrictions k hk).obj F ⟶
      (allLocalGermRestrictions k hk).obj G) :
    IsCompatibleLocalMorphism hk η ↔
      ∃! α : F ⟶ G, (allLocalGermRestrictions k hk).map α = η := by
  constructor
  · intro hη
    refine ⟨compatibleLocalMorphismLift hk η hη,
      allLocalGermRestrictions_map_compatibleLocalMorphismLift hk η hη, ?_⟩
    intro α hα
    apply (allLocalGermRestrictions k hk).map_injective
    rw [hα, allLocalGermRestrictions_map_compatibleLocalMorphismLift]
  · rintro ⟨α, hα, _⟩
    rw [← hα]
    exact allLocalGermRestrictions_map_compatible hk α

/-- Global boundary morphisms are exactly compatible families of local germ morphisms. -/
def globalHomEquivCompatibleLocalHom {k : ℕ} (hk : 0 < k)
    (F G : BoundaryCategory k hk) :
    (F ⟶ G) ≃
      {η : (allLocalGermRestrictions k hk).obj F ⟶
        (allLocalGermRestrictions k hk).obj G // IsCompatibleLocalMorphism hk η} where
  toFun α := ⟨(allLocalGermRestrictions k hk).map α,
    allLocalGermRestrictions_map_compatible hk α⟩
  invFun η := compatibleLocalMorphismLift hk η.1 η.2
  left_inv α := by
    apply (allLocalGermRestrictions k hk).map_injective
    rw [allLocalGermRestrictions_map_compatibleLocalMorphismLift]
  right_inv η := by
    apply Subtype.ext
    exact allLocalGermRestrictions_map_compatibleLocalMorphismLift hk η.1 η.2

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
