import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Stabilization
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.StabilizationEmbedding
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateDerivation
import GaloisForLFunctions.HTGeometry.PaperComplexDerivationSlice

/-!
A concrete terminating clock from the proven stable-coordinate construction
in OpenAI/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
All clock and splitting statements concern the explicit polynomial `StableCoordinate.f`.
The final obstruction records why this clock cannot fix the original coefficient algebra.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StableCoordinate MvPolynomial

/-- The explicit presentation change sending the stabilized polynomial to a coordinate. -/
def paperStabilizedCoordinateEquiv : R 5 ≃ₐ[ℂ] R 5 :=
  Presentation.stabilizedPresentation.symm.trans Stabilization.stablePresentationEquiv

private theorem presentation_change_image {K A B C : Type*} [CommSemiring K]
    [Semiring A] [Semiring B] [Semiring C] [Algebra K A] [Algebra K B] [Algebra K C]
    (u : A ≃ₐ[K] B) (v : A ≃ₐ[K] C) (a : A) (b : B) (c : C)
    (hu : u a = b) (hv : v a = c) : u.symm.trans v b = c := by
  change v (u.symm b) = c
  rw [← hu, AlgEquiv.symm_apply_apply, hv]

@[simp] theorem paperStabilizedCoordinateEquiv_f :
    paperStabilizedCoordinateEquiv (stabilize f) = X 0 :=
  presentation_change_image Presentation.stabilizedPresentation
    Stabilization.stablePresentationEquiv (Presentation.mk 1 (Presentation.p 1))
    (stabilize f) (X 0) Presentation.stabilizedPresentation_p
    Stabilization.stablePresentationEquiv_p

@[simp] theorem paperStabilizedCoordinateEquiv_symm_X_zero :
    paperStabilizedCoordinateEquiv.symm (X 0) = stabilize f := by
  apply paperStabilizedCoordinateEquiv.injective
  simp

/-- Differentiate in the coordinate furnished by the stable-coordinate proof. -/
def paperStabilizedClock : Derivation ℂ (R 5) (R 5) :=
  CoordinateDerivation.coordinatePartial paperStabilizedCoordinateEquiv.symm 0

theorem paperStabilizedClock_slice : paperStabilizedClock (stabilize f) = 1 := by
  rw [← paperStabilizedCoordinateEquiv_symm_X_zero]
  exact CoordinateDerivation.coordinatePartial_self paperStabilizedCoordinateEquiv.symm 0

theorem paperStabilizedClock_ne_zero : paperStabilizedClock ≠ 0 := by
  intro h
  have hs := paperStabilizedClock_slice
  rw [h] at hs
  exact zero_ne_one hs

/-- Four complementary coordinates are constants of the new clock. -/
theorem paperStabilizedClock_complementary_constant (i : Fin 4) :
    paperStabilizedClock (paperStabilizedCoordinateEquiv.symm (X i.succ)) = 0 :=
  CoordinateDerivation.coordinatePartial_other paperStabilizedCoordinateEquiv.symm
    (i := (0 : Fin 5)) (j := i.succ) (by simp)

theorem paperStabilizedClock_iterate (n : ℕ) (p : R 5) :
    (paperStabilizedClock^[n]) p = paperStabilizedCoordinateEquiv.symm
      ((pderiv (0 : Fin 5))^[n] (paperStabilizedCoordinateEquiv p)) :=
  CoordinateDerivation.transport_iterate paperStabilizedCoordinateEquiv.symm (pderiv 0) n p

/-- A symbolic degree bound for termination; no coefficient calculation is required. -/
theorem paperStabilizedClock_degree_bound (p : R 5) :
    (paperStabilizedClock^[degreeOf 0 (paperStabilizedCoordinateEquiv p) + 1]) p = 0 := by
  rw [paperStabilizedClock_iterate]
  have hz : ((pderiv (0 : Fin 5))^[degreeOf 0 (paperStabilizedCoordinateEquiv p) + 1])
      (paperStabilizedCoordinateEquiv p) = 0 := by
    ext m
    exact CoordinateDerivation.coeff_iterate_pderiv_eq_zero 0
      (paperStabilizedCoordinateEquiv p) _ m (by omega)
  rw [hz, map_zero]

theorem paperStabilizedClock_locallyNilpotent (p : R 5) :
    ∃ n : ℕ, (paperStabilizedClock^[n]) p = 0 :=
  ⟨degreeOf 0 (paperStabilizedCoordinateEquiv p) + 1, paperStabilizedClock_degree_bound p⟩

/-- The stabilized ring splits over the actual complex constants of this clock. -/
def paperStabilizedClockSplitting :
    Polynomial (complexDerivationKernel paperStabilizedClock) ≃ₐ[ℂ] R 5 :=
  complexSliceAlgEquiv paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent

@[simp] theorem paperStabilizedClockSplitting_X :
    paperStabilizedClockSplitting Polynomial.X = stabilize f :=
  complexSliceAlgEquiv_X paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent

theorem paperStabilizedClock_unique_polynomial (p : R 5) :
    ∃! q : Polynomial (complexDerivationKernel paperStabilizedClock),
      Polynomial.aeval (stabilize f) q = p :=
  complexSlice_unique_polynomial paperStabilizedClock paperStabilizedClock_slice
    paperStabilizedClock_locallyNilpotent p

/-- The same clock in the literal polynomial extension of the four-variable ring. -/
def paperPolynomialExtensionClock : Derivation ℂ (Polynomial (R 4)) (Polynomial (R 4)) :=
  CoordinateDerivation.transport stabilizationEquiv paperStabilizedClock

theorem paperPolynomialExtensionClock_slice :
    paperPolynomialExtensionClock (Polynomial.C f) = 1 := by
  rw [← stabilizationEquiv_stabilize]
  change CoordinateDerivation.transport stabilizationEquiv paperStabilizedClock
    (stabilizationEquiv (stabilize f)) = 1
  rw [CoordinateDerivation.transport_apply_image, paperStabilizedClock_slice, map_one]

theorem paperPolynomialExtensionClock_locallyNilpotent (p : Polynomial (R 4)) :
    ∃ n : ℕ, (paperPolynomialExtensionClock^[n]) p = 0 :=
  CoordinateDerivation.transport_locallyNilpotent stabilizationEquiv paperStabilizedClock
    paperStabilizedClock_locallyNilpotent p

/-- This clock necessarily moves original coefficients, even after adding a variable. -/
theorem paperPolynomialExtensionClock_not_coefficient_linear :
    ¬ ∃ E : Derivation (R 4) (Polynomial (R 4)) (Polynomial (R 4)),
      (E : Polynomial (R 4) → Polynomial (R 4)) = paperPolynomialExtensionClock := by
  rintro ⟨E, hE⟩
  have hz := E.map_algebraMap f
  change E (Polynomial.C f) = 0 at hz
  have h := congrFun hE (Polynomial.C f)
  rw [hz, paperPolynomialExtensionClock_slice] at h
  exact zero_ne_one h

end
end GaloisForLFunctions.HTGeometry
