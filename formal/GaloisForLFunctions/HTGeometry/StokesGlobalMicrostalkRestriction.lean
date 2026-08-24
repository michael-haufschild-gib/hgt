import GaloisForLFunctions.HTGeometry.StokesCellularBoundaryRestriction
import GaloisForLFunctions.HTGeometry.StokesIrregularRealizationTransport

/-!
# Wallwise microstalks of global cellular Stokes boundaries

Composing exact local-germ restriction with cellular microlocalization produces a wallwise
microstalk functor on the global cyclic boundary category. For the alternating exponential
boundary, its two directed ranks recover the local complementary rank law at every wall.
-/

open CategoryTheory

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

open CellularMicrolocal

/-- Wallwise microlocalization of a global cyclic Stokes boundary representation. -/
noncomputable def wallMicrostalkFunctor {k : ℕ} (hk : 0 < k)
    (w : StokesWall k) (s : ConormalSide) :
    BoundaryCategory k hk ⥤ ModuleCat ℚ :=
  localGermRestriction hk w ⋙ microstalkFunctor s

/-- Every global boundary object has the local arc-to-nearby-to-vanishing exact sequence at each
wall and conormal side. -/
theorem wallRestriction_exact {k : ℕ} (hk : 0 < k) (w : StokesWall k)
    (F : BoundaryCategory k hk) (s : ConormalSide) :
    Function.Exact (sideMap ((localGermRestriction hk w).obj F) s).hom
        (nearbyToVanishing ((localGermRestriction hk w).obj F) s) ∧
      Function.Surjective
        (nearbyToVanishing ((localGermRestriction hk w).obj F) s) :=
  realizationTransport_exact (localGermRestriction hk w) F s

/-- Wallwise microstalk of the global exponential boundary agrees with that of the local
exponential germ. -/
noncomputable def wallMicrostalkExponentialIso (k d : ℕ) (hk : 0 < k)
    (w : StokesWall k) (s : ConormalSide) :
    (wallMicrostalkFunctor hk w s).obj (exponentialBoundary k d hk) ≅
      (microstalkFunctor s).obj (exponentialGerm d w.2) :=
  (microstalkFunctor s).mapIso (localGermRestrictionExponentialIso k d hk w)

/-- Left wallwise microstalk rank of the global exponential boundary. -/
theorem exponentialBoundary_wallMicrostalk_left_finrank
    (k d : ℕ) (hk : 0 < k) (w : StokesWall k) :
    Module.finrank ℚ
        ((wallMicrostalkFunctor hk w .left).obj (exponentialBoundary k d hk)) =
      if w.2 then 0 else d := by
  calc
    Module.finrank ℚ
        ((wallMicrostalkFunctor hk w .left).obj (exponentialBoundary k d hk)) =
        Module.finrank ℚ ((microstalkFunctor .left).obj (exponentialGerm d w.2)) :=
      (moduleLinearEquivOfIso
        (wallMicrostalkExponentialIso k d hk w .left)).finrank_eq
    _ = if w.2 then 0 else d := exponentialGerm_left_finrank d w.2

/-- Right wallwise microstalk rank of the global exponential boundary. -/
theorem exponentialBoundary_wallMicrostalk_right_finrank
    (k d : ℕ) (hk : 0 < k) (w : StokesWall k) :
    Module.finrank ℚ
        ((wallMicrostalkFunctor hk w .right).obj (exponentialBoundary k d hk)) =
      if w.2 then d else 0 := by
  calc
    Module.finrank ℚ
        ((wallMicrostalkFunctor hk w .right).obj (exponentialBoundary k d hk)) =
        Module.finrank ℚ ((microstalkFunctor .right).obj (exponentialGerm d w.2)) :=
      (moduleLinearEquivOfIso
        (wallMicrostalkExponentialIso k d hk w .right)).finrank_eq
    _ = if w.2 then d else 0 := exponentialGerm_right_finrank d w.2

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
