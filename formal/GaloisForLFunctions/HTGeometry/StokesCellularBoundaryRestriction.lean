import GaloisForLFunctions.HTGeometry.StokesCellularCategory

/-!
# Restriction from cyclic Stokes boundaries to local germs

Every wall in the cyclic cellular boundary has an outgoing arc and a predecessor arc. Restricting
an entrance-path representation to this cospan gives its local Stokes germ. The global alternating
exponential boundary restricts to the previously constructed local exponential germ.
-/

open CategoryTheory CategoryTheory.Limits

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

open CellularMicrolocal

/-- Cyclic predecessor on the `Fin k` factor. -/
def predFin {k : ℕ} (hk : 0 < k) (a : Fin k) : Fin k :=
  haveI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  a - 1

/-- The project convention for cyclic successor is addition by one in `Fin k`. -/
theorem succFin_eq_add_one {k : ℕ} (hk : 0 < k) (a : Fin k) :
    succFin hk a =
      haveI : NeZero k := ⟨Nat.ne_of_gt hk⟩
      a + 1 := by
  apply Fin.ext
  simp [succFin, Fin.add_def]

/-- Cyclic predecessor is a right inverse to cyclic successor. -/
theorem succFin_predFin {k : ℕ} (hk : 0 < k) (a : Fin k) :
    succFin hk (predFin hk a) = a := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [succFin_eq_add_one]
  change (a - 1) + 1 = a
  exact sub_add_cancel a 1

/-- Cyclic predecessor is a left inverse to cyclic successor. -/
theorem predFin_succFin {k : ℕ} (hk : 0 < k) (a : Fin k) :
    predFin hk (succFin hk a) = a := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [succFin_eq_add_one]
  change (a + 1) - 1 = a
  exact add_sub_cancel_right a 1

/-- Cyclic predecessor on Stokes walls. -/
def prevWall {k : ℕ} (hk : 0 < k) : StokesWall k → StokesWall k
  | (a, false) => (predFin hk a, true)
  | (a, true) => (a, false)

/-- Wall predecessor is a right inverse to wall successor. -/
@[simp]
theorem nextWall_prevWall {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    nextWall hk (prevWall hk w) = w := by
  rcases w with ⟨a, b⟩
  cases b <;> simp [prevWall, nextWall, succFin_predFin]

/-- Wall predecessor is a left inverse to wall successor. -/
@[simp]
theorem prevWall_nextWall {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    prevWall hk (nextWall hk w) = w := by
  rcases w with ⟨a, b⟩
  cases b <;> simp [prevWall, nextWall, predFin_succFin]

/-- Consecutive walls have complementary Boolean orientation labels. -/
@[simp]
theorem prevWall_snd {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    (prevWall hk w).2 = !w.2 := by
  rcases w with ⟨a, b⟩
  cases b <;> rfl

/-- Entrance-path arrow from a chosen outgoing arc into its initial wall. -/
def initialBoundaryPath {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    @Quiver.Path (BoundaryQuiver k hk)
      (inferInstance : Quiver (BoundaryQuiver k hk)) (.arc w) (.wall w) :=
  Quiver.Hom.toPath (BoundaryArrow.initial w)

/-- Entrance-path arrow from an arc into its terminal wall. -/
def terminalBoundaryPath {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    @Quiver.Path (BoundaryQuiver k hk)
      (inferInstance : Quiver (BoundaryQuiver k hk))
      (.arc w) (.wall (nextWall hk w)) :=
  Quiver.Hom.toPath (BoundaryArrow.terminal w)

/-- Local cospan around the terminal wall of a chosen predecessor arc. -/
def localBoundaryInclusionFromPredecessor {k : ℕ} (hk : 0 < k)
    (v : StokesWall k) :
    WalkingCospan ⥤ BoundaryPath k hk :=
  cospan (initialBoundaryPath hk (nextWall hk v)) (terminalBoundaryPath hk v)

/-- Restriction to the germ around the terminal wall of a chosen predecessor arc. -/
def localGermRestrictionFromPredecessor {k : ℕ} (hk : 0 < k)
    (v : StokesWall k) : BoundaryCategory k hk ⥤ GermCategory :=
  (Functor.whiskeringLeft WalkingCospan (BoundaryPath k hk) (ModuleCat ℚ)).obj
    (localBoundaryInclusionFromPredecessor hk v)

/-- Restriction of global cyclic boundary data to the cellular germ at one wall. -/
def localGermRestriction {k : ℕ} (hk : 0 < k) (w : StokesWall k) :
    BoundaryCategory k hk ⥤ GermCategory :=
  localGermRestrictionFromPredecessor hk (prevWall hk w)

/-- Local germ restriction preserves finite limits. -/
noncomputable instance localGermRestriction_preservesFiniteLimits {k : ℕ}
    (hk : 0 < k) (w : StokesWall k) :
    PreservesFiniteLimits (localGermRestriction hk w) := by
  dsimp [localGermRestriction, localGermRestrictionFromPredecessor]
  infer_instance

/-- Local germ restriction preserves finite colimits. -/
noncomputable instance localGermRestriction_preservesFiniteColimits {k : ℕ}
    (hk : 0 < k) (w : StokesWall k) :
    PreservesFiniteColimits (localGermRestriction hk w) := by
  dsimp [localGermRestriction, localGermRestrictionFromPredecessor]
  infer_instance

/-- Local germ restriction is additive. -/
noncomputable instance localGermRestriction_additive {k : ℕ}
    (hk : 0 < k) (w : StokesWall k) : (localGermRestriction hk w).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts (localGermRestriction hk w)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction indexed by a predecessor arc recovers the local germ at its terminal wall. -/
noncomputable def localGermRestrictionFromPredecessorExponentialIso
    (k d : ℕ) (hk : 0 < k) (v : StokesWall k) :
    (localGermRestrictionFromPredecessor hk v).obj (exponentialBoundary k d hk) ≅
      exponentialGerm d (nextWall hk v).2 := by
  rcases v with ⟨a, b⟩
  cases b
  · refine cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · change (exponentialBoundary k d hk).map
        (initialBoundaryPath hk (a, true)) = ModuleCat.ofHom (restriction d true)
      exact exponentialBoundary_map_initial k d hk (a, true)
    · change (exponentialBoundary k d hk).map
        (terminalBoundaryPath hk (a, false)) = ModuleCat.ofHom (restriction d false)
      exact exponentialBoundary_map_terminal k d hk (a, false)
  · refine cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · change (exponentialBoundary k d hk).map
        (initialBoundaryPath hk (succFin hk a, false)) =
          ModuleCat.ofHom (restriction d false)
      exact exponentialBoundary_map_initial k d hk (succFin hk a, false)
    · change (exponentialBoundary k d hk).map
        (terminalBoundaryPath hk (a, true)) = ModuleCat.ofHom (restriction d true)
      exact exponentialBoundary_map_terminal k d hk (a, true)

/-- Restricting the global alternating exponential boundary to a wall recovers its local
exponential germ. -/
noncomputable def localGermRestrictionExponentialIso (k d : ℕ) (hk : 0 < k)
    (w : StokesWall k) :
    (localGermRestriction hk w).obj (exponentialBoundary k d hk) ≅
      exponentialGerm d w.2 := by
  simpa only [localGermRestriction, nextWall_prevWall] using
    localGermRestrictionFromPredecessorExponentialIso k d hk (prevWall hk w)

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
