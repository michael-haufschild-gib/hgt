import GaloisForLFunctions.HTGeometry.FiniteBuresReporterVariationalLaw
import GaloisForLFunctions.HTGeometry.FiniteBuresTargetMinimaxCore

/-!
# Bures equilibrium reporter law

The positive-definite geometric-mean reporter is not only variationally
optimal: it transports source covariance exactly to target covariance.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

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

/-- **Positive-design complementary slackness `(EQ3)`.**  If a probability
mixture attains the largest target leverage, every endpoint carrying positive
design weight attains that same largest leverage.  No extremality or
uniqueness of the design representation is required. -/
theorem finiteBuresEquilibrium_positiveWeight_eq_maxLeverage
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (p : C → ℝ) (hp : p ∈ stdSimplex ℝ C)
    (target : C → Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ)
    (hle : ∀ c, finiteBuresTargetLeverage A (target c) ≤ B)
    (hattain : finiteBuresTargetPairing
        (finiteBuresTargetMixture p target) A = B) :
    ∀ c, 0 < p c → finiteBuresTargetLeverage A (target c) = B := by
  classical
  intro c hc
  have havg : (∑ j, p j * finiteBuresTargetLeverage A (target j)) = B := by
    rw [← finiteBuresTargetMixture_pairing_eq_average]
    exact hattain
  apply le_antisymm (hle c)
  by_contra hnot
  have hlt : finiteBuresTargetLeverage A (target c) < B :=
    lt_of_not_ge hnot
  have hnonneg : ∀ j ∈ (Finset.univ : Finset C),
      0 ≤ p j * (B - finiteBuresTargetLeverage A (target j)) := by
    intro j _
    exact mul_nonneg (hp.1 j) (sub_nonneg.mpr (hle j))
  have hpos : 0 < ∑ j, p j *
      (B - finiteBuresTargetLeverage A (target j)) := by
    apply Finset.sum_pos' hnonneg
    exact ⟨c, Finset.mem_univ c, mul_pos hc (sub_pos.mpr hlt)⟩
  have hsum : ∑ j, p j = 1 := hp.2
  have hzero : ∑ j, p j *
      (B - finiteBuresTargetLeverage A (target j)) = 0 := by
    calc
      (∑ j, p j * (B - finiteBuresTargetLeverage A (target j))) =
          B * (∑ j, p j) -
            ∑ j, p j * finiteBuresTargetLeverage A (target j) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = 0 := by rw [hsum, havg]; ring
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

end

end GaloisForLFunctions.HTGeometry
