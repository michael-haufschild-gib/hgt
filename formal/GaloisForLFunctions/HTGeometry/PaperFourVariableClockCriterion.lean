import GaloisForLFunctions.HTGeometry.PaperComplexSliceFibers
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ZeroFiberExact
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateDerivation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Algebra.Rat

/-!
The proven affine-three-space zero fibre turns a terminating clock for the exact
four-variable polynomial into an ambient coordinate. The converse transports
a coordinate derivative. `PaperFourVariableClockObstruction` applies this bridge
to the proved non-coordinate theorem, ruling out terminating transverse clocks.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StableCoordinate

private theorem slice_coordinate_image {K : Type*} [CommRing K] [Algebra ℂ K]
    (e : Polynomial K ≃ₐ[ℂ] R 4) (k : K ≃ₐ[ℂ] R 3) (s : R 4)
    (hx : e Polynomial.X = s) :
    (e.symm.trans ((Polynomial.mapAlgEquiv k).trans (MvPolynomial.finSuccEquiv ℂ 3).symm)) s =
      MvPolynomial.X 0 := by
  change (MvPolynomial.finSuccEquiv ℂ 3).symm ((Polynomial.mapAlgEquiv k) (e.symm s)) = _
  apply (MvPolynomial.finSuccEquiv ℂ 3).injective
  rw [AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_zero]
  rw [← hx, AlgEquiv.symm_apply_apply]
  simp only [Polynomial.coe_mapAlgEquiv, Polynomial.map_X]

/-- For the exact polynomial, a terminating complex clock exists exactly when it is a coordinate. -/
theorem paperFourVariableClock_iff_coordinate :
    (∃ D : Derivation ℂ (R 4) (R 4), D f = 1 ∧
      ∀ p : R 4, ∃ n : ℕ, (D^[n]) p = 0) ↔ IsCoordinate (by omega) f := by
  constructor
  · rintro ⟨D, hs, hnil⟩
    let e := complexSliceAlgEquiv D hs hnil
    let k : complexDerivationKernel D ≃ₐ[ℂ] R 3 :=
      (complexSliceFiberEquiv D hs hnil 0).symm.trans zeroFiberEquiv
    refine ⟨e.symm.trans ((Polynomial.mapAlgEquiv k).trans
      (MvPolynomial.finSuccEquiv ℂ 3).symm), ?_⟩
    exact slice_coordinate_image e k f (complexSliceAlgEquiv_X D hs hnil)
  · rintro ⟨φ, hφ⟩
    refine ⟨CoordinateDerivation.coordinatePartial φ.symm (0 : Fin 4), ?_,
      CoordinateDerivation.coordinatePartial_locallyNilpotent φ.symm 0⟩
    have hf : φ.symm (MvPolynomial.X 0) = f := by
      apply φ.injective
      rw [AlgEquiv.apply_symm_apply, hφ]
      rfl
    rw [← hf]
    exact CoordinateDerivation.coordinatePartial_self φ.symm 0

end
end GaloisForLFunctions.HTGeometry
