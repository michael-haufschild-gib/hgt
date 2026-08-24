import GaloisForLFunctions.HTGeometry.StokesCellularBoundaryRestriction

/-!
# Global cellular Stokes data detected by all local germs

Restrict a cyclic boundary representation to the cospan at every wall. The resulting functor to
the category of local-germ families preserves finite limits and colimits, is additive, faithful,
and reflects isomorphisms. Thus all local germs jointly detect global morphisms and equivalences;
the remaining descent issue is compatibility/fullness of arbitrary local families.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

open CellularMicrolocal

/-- Families of local cellular Stokes germs indexed by predecessor arcs. -/
abbrev GermFamily (k : ℕ) := Discrete (StokesWall k) ⥤ GermCategory

/-- Restriction of a global cyclic boundary representation to all its local wall germs. -/
def allLocalGermRestrictions (k : ℕ) (hk : 0 < k) :
    BoundaryCategory k hk ⥤ GermFamily k where
  obj F := Discrete.functor fun v => (localGermRestrictionFromPredecessor hk v).obj F
  map α := Discrete.natTrans fun v =>
    (localGermRestrictionFromPredecessor hk v.as).map α
  map_id _ := by
    ext v X
    rfl
  map_comp _ _ := by
    ext v X
    rfl

/-- Simultaneous local-germ restriction preserves finite limits. -/
noncomputable instance allLocalGermRestrictions_preservesFiniteLimits
    (k : ℕ) (hk : 0 < k) : PreservesFiniteLimits (allLocalGermRestrictions k hk) := by
  apply preservesFiniteLimits_of_evaluation
  intro v
  change PreservesFiniteLimits (localGermRestrictionFromPredecessor hk v.as)
  dsimp [localGermRestrictionFromPredecessor]
  infer_instance

/-- Simultaneous local-germ restriction preserves finite colimits. -/
noncomputable instance allLocalGermRestrictions_preservesFiniteColimits
    (k : ℕ) (hk : 0 < k) : PreservesFiniteColimits (allLocalGermRestrictions k hk) := by
  apply preservesFiniteColimits_of_evaluation
  intro v
  change PreservesFiniteColimits (localGermRestrictionFromPredecessor hk v.as)
  dsimp [localGermRestrictionFromPredecessor]
  infer_instance

/-- Simultaneous local-germ restriction is additive. -/
noncomputable instance allLocalGermRestrictions_additive
    (k : ℕ) (hk : 0 < k) : (allLocalGermRestrictions k hk).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts (allLocalGermRestrictions k hk)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- All local wall germs jointly detect every morphism of global boundary representations. -/
instance allLocalGermRestrictions_faithful (k : ℕ) (hk : 0 < k) :
    (allLocalGermRestrictions k hk).Faithful where
  map_injective := by
    intro F G α β h
    apply NatTrans.ext
    funext cell
    cases cell with
    | arc w =>
        have hw := NatTrans.congr_app h (Discrete.mk w)
        exact NatTrans.congr_app hw WalkingCospan.right
    | wall w =>
        have hw := NatTrans.congr_app h (Discrete.mk (prevWall hk w))
        have hcomp := NatTrans.congr_app hw WalkingCospan.one
        change α.app (.wall (nextWall hk (prevWall hk w))) =
          β.app (.wall (nextWall hk (prevWall hk w))) at hcomp
        rw [nextWall_prevWall hk w] at hcomp
        exact hcomp

/-- A global boundary morphism is an isomorphism whenever all its local germ restrictions are
isomorphisms. -/
instance allLocalGermRestrictions_reflectsIsomorphisms (k : ℕ) (hk : 0 < k) :
    (allLocalGermRestrictions k hk).ReflectsIsomorphisms where
  reflects := by
    intro F G α hα
    letI : ∀ cell, IsIso (α.app cell) := fun cell => by
      cases cell with
      | arc w =>
          letI : IsIso (((allLocalGermRestrictions k hk).map α).app (Discrete.mk w)) :=
            NatIso.isIso_app_of_isIso ((allLocalGermRestrictions k hk).map α) (Discrete.mk w)
          letI : IsIso
              ((((allLocalGermRestrictions k hk).map α).app (Discrete.mk w)).app
                WalkingCospan.right) :=
            NatIso.isIso_app_of_isIso
              (((allLocalGermRestrictions k hk).map α).app (Discrete.mk w))
              WalkingCospan.right
          change IsIso
            ((((allLocalGermRestrictions k hk).map α).app (Discrete.mk w)).app
              WalkingCospan.right)
          infer_instance
      | wall w =>
          let v := prevWall hk w
          letI : IsIso (((allLocalGermRestrictions k hk).map α).app (Discrete.mk v)) :=
            NatIso.isIso_app_of_isIso ((allLocalGermRestrictions k hk).map α) (Discrete.mk v)
          letI : IsIso
              ((((allLocalGermRestrictions k hk).map α).app (Discrete.mk v)).app
                WalkingCospan.one) :=
            NatIso.isIso_app_of_isIso
              (((allLocalGermRestrictions k hk).map α).app (Discrete.mk v))
              WalkingCospan.one
          rw [← nextWall_prevWall hk w]
          change IsIso
            ((((allLocalGermRestrictions k hk).map α).app (Discrete.mk v)).app
              WalkingCospan.one)
          infer_instance
    exact NatIso.isIso_of_isIso_app α

/-- Every component of the all-germs restriction of the exponential boundary is its corresponding
local exponential germ. -/
noncomputable def allLocalGermRestrictionsExponentialIso (k d : ℕ) (hk : 0 < k)
    (v : StokesWall k) :
    ((allLocalGermRestrictions k hk).obj (exponentialBoundary k d hk)).obj
        (Discrete.mk v) ≅
      exponentialGerm d (nextWall hk v).2 :=
  localGermRestrictionFromPredecessorExponentialIso k d hk v

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
