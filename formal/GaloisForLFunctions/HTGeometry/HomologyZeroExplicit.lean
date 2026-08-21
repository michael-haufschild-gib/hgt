import GaloisForLFunctions.HTGeometry.ZerothHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The zeroth homology, explicitly

In degree zero the differential out of the complex vanishes, so the homology is the cokernel of the
first boundary map: the `0`-chains modulo the boundaries.  On a path-connected space the boundaries
are the chains of total coefficient zero, so the augmentation identifies the zeroth homology with
the coefficient ring.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

theorem sc'_zero_g_eq_zero (K : ChainComplex (ModuleCat.{v} R) ℕ) :
    (K.sc' 1 0 ((ComplexShape.down ℕ).next 0)).g = 0 := by
  refine K.shape 0 _ ?_
  intro h
  exact absurd h (by simp [ComplexShape.down_Rel])

/-- In degree zero the homology is the chains modulo the boundaries. -/
noncomputable def homologyZeroIso (K : ChainComplex (ModuleCat.{v} R) ℕ) :
    K.homology 0 ≅ ModuleCat.of R ((K.X 0) ⧸ LinearMap.range (K.d 1 0).hom) := by
  refine ShortComplex.homologyMapIso
    (K.isoSc' 1 0 ((ComplexShape.down ℕ).next 0) (ComplexShape.prev_eq' _ rfl) rfl) ≪≫ ?_
  refine (K.sc' 1 0 ((ComplexShape.down ℕ).next 0)).moduleCatHomologyIso ≪≫ ?_
  refine LinearEquiv.toModuleIso ?_
  refine Submodule.Quotient.equiv _ _
    ((LinearEquiv.ofEq _ _ (by rw [sc'_zero_g_eq_zero]; exact LinearMap.ker_zero)).trans
      Submodule.topEquiv) ?_
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := hz
    exact ⟨x, rfl⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩

theorem singAug_surjective [Nonempty X] : Function.Surjective (singAug R (X := X)) := by
  intro r
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact ⟨Finsupp.single (constSimplex x 0) r, singAug_single R _ r⟩

/-- **The zeroth homology of a path-connected space is the coefficient ring.** -/
noncomputable def homologyZeroIsoRing (X : Type v) [TopologicalSpace X] [PathConnectedSpace X] :
    (singChainComplex R X).homology 0 ≅ ModuleCat.of R (ULift.{v} R) := by
  refine homologyZeroIso R (singChainComplex R X) ≪≫ LinearEquiv.toModuleIso ?_
  refine ((Submodule.quotEquivOfEq _ _ (range_singBd_zero_eq_ker_singAug R)).trans
    (LinearMap.quotKerEquivOfSurjective (singAug R (X := X)) (singAug_surjective R))).trans
    (ULift.moduleEquiv).symm

end GaloisForLFunctions.HTGeometry
