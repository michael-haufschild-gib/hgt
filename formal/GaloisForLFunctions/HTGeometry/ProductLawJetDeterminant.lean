import GaloisForLFunctions.HTGeometry.ProductLawPolynomialBridge
import GaloisForLFunctions.HTGeometry.JetJacobianWithCoordinate

/-!
# Transporting the determinant back to the polynomial model

The coordinate derivations of the polynomial ring map onto those of the rational model, so the
polynomial jet Jacobian maps onto the rational one — transposed, since one indexes rows by jets and
the other by derivations.  A determinant computed in the fraction field therefore certifies the
polynomial one, and with it the algebraic independence the analytic transfer needs.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The coordinate derivations commute with the inclusion. -/
theorem algebraMap_pderiv (k : ℕ) (P : MvPolynomial ℕ ℂ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField ((MvPolynomial.pderiv k) P)
      = fpderiv k (algebraMap (MvPolynomial ℕ ℂ) CascadeField P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [show (MvPolynomial.C c : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl,
        (MvPolynomial.pderiv k).map_algebraMap, map_zero,
        ← IsScalarTower.algebraMap_apply ℂ (MvPolynomial ℕ ℂ) CascadeField,
        (fpderiv k).map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
      have hpoly : (MvPolynomial.pderiv k) (p * MvPolynomial.X j)
          = p * (MvPolynomial.pderiv k) (MvPolynomial.X j)
            + MvPolynomial.X j * (MvPolynomial.pderiv k) p := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hfield : fpderiv k
          (algebraMap (MvPolynomial ℕ ℂ) CascadeField p * fx j)
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField p * fpderiv k (fx j)
            + fx j * fpderiv k (algebraMap (MvPolynomial ℕ ℂ) CascadeField p) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hpoly, map_add, map_mul, map_mul, hp, map_mul,
        show algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.X j) = fx j from rfl,
        hfield]
      by_cases hkj : j = k
      · subst hkj
        rw [MvPolynomial.pderiv_X_self, fpderiv_fx_self, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne hkj, fpderiv_fx_of_ne hkj, map_zero]

/-- The model jets map onto the rational jets. -/
theorem algebraMap_modelJet (N i : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (modelJet (polyProdDerivation Q v) N i)
      = ((prodDerivation Q v : CascadeField → CascadeField)^[i]) (fx N) := by
  rw [modelJet, algebraMap_iterate_polyProdDerivation]
  rfl

/-- **A nonvanishing rational jet determinant certifies the polynomial one.** -/
theorem jetDet_ne_zero_of_field {N m : ℕ}
    (hfield : (Matrix.of fun i j : Fin (m + 1) =>
        fpderiv ((j : ℕ) + 1)
          (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx N))).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (modelJet (polyProdDerivation Q v) N (j : ℕ))).det ≠ 0 := by
  intro hzero
  refine hfield ?_
  have hmap : (Matrix.of fun i j : Fin (m + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx N)))
      = ((algebraMap (MvPolynomial ℕ ℂ) CascadeField).mapMatrix
          (Matrix.of fun i j : Fin (m + 1) =>
            (MvPolynomial.pderiv ((i : ℕ) + 1))
              (modelJet (polyProdDerivation Q v) N (j : ℕ)))).transpose := by
    funext i j
    rw [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.of_apply, algebraMap_pderiv, algebraMap_modelJet]
  rw [hmap, Matrix.det_transpose, ← RingHom.map_det, hzero, map_zero]

end GaloisForLFunctions.HTGeometry
