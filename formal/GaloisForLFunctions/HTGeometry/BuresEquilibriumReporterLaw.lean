import GaloisForLFunctions.HTGeometry.FiniteBuresReporterVariationalLaw

/-!
# Bures equilibrium reporter law

The positive-definite geometric-mean reporter is not only variationally
optimal: it transports source covariance exactly to target covariance.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Equilibrium reporter laws -/

/-- The geometric-mean reporter transports the positive source exactly to the
positive target. -/
theorem finiteBuresOptimalReporter_transport
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    finiteBuresOptimalReporter C M * C * finiteBuresOptimalReporter C M = M := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt C
  let W : Matrix (Fin n) (Fin n) ℂ := CFC.conjSqrt C M
  let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt W
  have hC0 : 0 ≤ C := Matrix.nonneg_iff_posSemidef.mpr hC.posSemidef
  have hP2 : P * P = C := by
    simpa [P, pow_two] using CFC.sq_sqrt C hC0
  have hPunit : IsUnit P := (CFC.isUnit_sqrt_iff C hC0).2 hC.isUnit
  have hPdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hPunit
  have hWpos : W.PosDef := by
    rw [← Matrix.isStrictlyPositive_iff_posDef]
    exact (CFC.isStrictlyPositive_conjSqrt_iff C M
      hC.isStrictlyPositive).2 hM.isStrictlyPositive
  have hW0 : 0 ≤ W := Matrix.nonneg_iff_posSemidef.mpr hWpos.posSemidef
  have hS2 : S * S = W := by
    simpa [S, pow_two] using CFC.sq_sqrt W hW0
  have hW : P * M * P = W := by
    simp [P, W, CFC.conjSqrt_apply]
  have hsqrtInv : CFC.sqrt C⁻¹ = P⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, CFC.sqrt_ringInverse,
      ← Matrix.nonsing_inv_eq_ringInverse]
  change (CFC.sqrt C⁻¹ * S * CFC.sqrt C⁻¹) * C *
      (CFC.sqrt C⁻¹ * S * CFC.sqrt C⁻¹) = M
  rw [hsqrtInv, ← hP2]
  calc
    (P⁻¹ * S * P⁻¹) * (P * P) * (P⁻¹ * S * P⁻¹) =
        P⁻¹ * S * (P⁻¹ * P) * (P * P⁻¹) * S * P⁻¹ := by
      noncomm_ring
    _ = P⁻¹ * S * S * P⁻¹ := by
      rw [Matrix.nonsing_inv_mul P hPdet, Matrix.mul_nonsing_inv P hPdet]
      simp
    _ = P⁻¹ * W * P⁻¹ := by rw [← hS2]; noncomm_ring
    _ = P⁻¹ * (P * M * P) * P⁻¹ := by rw [hW]
    _ = M := by
      rw [show P⁻¹ * (P * M * P) * P⁻¹ =
        (P⁻¹ * P) * M * (P * P⁻¹) by noncomm_ring,
        Matrix.nonsing_inv_mul P hPdet, Matrix.mul_nonsing_inv P hPdet]
      simp

end

end GaloisForLFunctions.HTGeometry
