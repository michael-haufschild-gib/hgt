import GaloisForLFunctions.HTGeometry.CriticalGeometricSheetFibre
import GaloisForLFunctions.HTGeometry.CriticalSchurPrimeDivisor
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic

/-!
# The actual critical Jacobian and the Schur prime divisor

This module identifies the Jacobian determinant of the actual reciprocal polynomial in the
critical source field with the rectangular-Schur equation in source coordinates, up to the
explicit invertible power of the source scale.  In particular, the abstract Schur divisor built
in `CriticalSchurPrimeDivisor` is exactly the actual critical ramification divisor.
-/

open Polynomial Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000

/-- Nonzero constant coefficient of the actual raw source polynomial. -/
noncomputable def criticalSourceScale
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceField K m n :=
  criticalSourceRaw K m n ⟨0, by omega⟩

theorem criticalSourceScale_ne_zero
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSourceScale K hm hn ≠ 0 := by
  intro hzero
  exact ((algebraicIndependent_criticalSourceRaw K m n).transcendental
    ⟨0, by omega⟩) (hzero ▸ isAlgebraic_zero)

/-- Unit-normalized actual raw polynomial through the critical horizon. -/
noncomputable def criticalSourceNormalizedRawPolynomial
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSourceField K m n)[X] :=
  finiteUnitPolynomial (criticalSourceNormalizedPositive K hm hn)

/-- Canonical truncated reciprocal of the unit-normalized actual raw polynomial. -/
noncomputable def criticalSourceNormalizedReciprocalPolynomial
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSourceField K m n)[X] :=
  finiteUnitPolynomial
    (finiteReciprocalPositive (criticalSourceNormalizedPositive K hm hn))

/-- Through the critical horizon, unit normalization is multiplication by the inverse source
scale. -/
theorem criticalSourceNormalizedRawPolynomial_coeff
    (K : Type*) [Field K] {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hk : k < m + n) :
    (criticalSourceNormalizedRawPolynomial K hm hn).coeff k =
      (criticalSourceScale K hm hn)⁻¹ *
        (criticalSourceRawPolynomial K m n).coeff k := by
  rcases k with _ | k
  · rw [criticalSourceNormalizedRawPolynomial, finiteUnitPolynomial_coeff_zero,
      criticalSourceRawPolynomial_coeff K m n 0 (by omega)]
    exact (inv_mul_cancel₀ (criticalSourceScale_ne_zero K hm hn)).symm
  · have hk' : k < m + n - 1 := by omega
    let i : Fin (m + n - 1) := ⟨k, hk'⟩
    rw [criticalSourceNormalizedRawPolynomial,
      show k + 1 = (i : ℕ) + 1 by rfl,
      finiteUnitPolynomial_coeff_succ]
    rw [criticalSourceRawPolynomial_coeff K m n (k + 1) (by omega)]
    simp only [criticalSourceNormalizedPositive, normalizedPositiveFiniteJet,
      normalizedFiniteJet, div_eq_inv_mul,
      criticalSourceScale, criticalSourceRawReindexed]
    congr 2

/-- The normalized polynomial agrees modulo the critical horizon with the raw polynomial divided
by its source scale. -/
theorem X_pow_dvd_criticalSourceNormalizedRaw_sub_scale
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      criticalSourceNormalizedRawPolynomial K hm hn -
        C (criticalSourceScale K hm hn)⁻¹ * criticalSourceRawPolynomial K m n := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    criticalSourceNormalizedRawPolynomial_coeff K hm hn hk]
  exact sub_self _

/-- The scale-adjusted actual reciprocal polynomial is an inverse of the unit-normalized raw
polynomial modulo the full critical horizon. -/
theorem X_pow_dvd_normalizedRaw_mul_scaleReciprocal_sub_one
    (K : Type*) [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      criticalSourceNormalizedRawPolynomial K hm hn *
        (C (criticalSourceScale K hm hn) *
          criticalSourceReciprocalPolynomial K m n) - 1 := by
  let s := criticalSourceScale K hm hn
  let U := criticalSourceNormalizedRawPolynomial K hm hn
  let R := criticalSourceRawPolynomial K m n
  let Y := criticalSourceReciprocalPolynomial K m n
  have hs : s ≠ 0 := criticalSourceScale_ne_zero K hm hn
  have hraw : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣ R * Y - 1 :=
    X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n
  have hbase : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      (C s⁻¹ * R) * (C s * Y) - 1 := by
    rw [show (C s⁻¹ * R) * (C s * Y) =
        (C s⁻¹ * C s) * (R * Y) by ring,
      ← Polynomial.C_mul, inv_mul_cancel₀ hs]
    simpa using hraw
  have hdiff : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      U - C s⁻¹ * R :=
    X_pow_dvd_criticalSourceNormalizedRaw_sub_scale K hm hn
  rw [show U * (C s * Y) - 1 =
      ((C s⁻¹ * R) * (C s * Y) - 1) + (U - C s⁻¹ * R) * (C s * Y) by ring]
  exact dvd_add hbase (dvd_mul_of_dvd_left hdiff _)

/-- The canonical truncated reciprocal is an inverse of the actual normalized raw polynomial. -/
theorem X_pow_dvd_normalizedRaw_mul_normalizedReciprocal_sub_one
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣
      criticalSourceNormalizedRawPolynomial K hm hn *
        criticalSourceNormalizedReciprocalPolynomial K hm hn - 1 := by
  let u := criticalSourceNormalizedPositive K hm hn
  let U := finiteUnitPolynomial u
  let Y := truncatedReciprocalKernel ((m + n - 1) + 1) U
  let V := finiteUnitPolynomial (finiteReciprocalPositive u)
  have hUY : (X : (criticalSourceField K m n)[X]) ^ ((m + n - 1) + 1) ∣
      U * Y - 1 :=
    truncatedReciprocalKernel_isInverseMod ((m + n - 1) + 1) U
      (finiteUnitPolynomial_coeff_zero u)
  have hUV : (X : (criticalSourceField K m n)[X]) ^ ((m + n - 1) + 1) ∣
      U * V - 1 :=
    X_pow_dvd_mul_sub_of_coeff_eq ((m + n - 1) + 1) U V Y hUY
      (finiteUnitPolynomial_reciprocal_coeff u)
  have hL : m + n - 1 + 1 = m + n := by omega
  rw [hL] at hUV
  simpa [criticalSourceNormalizedRawPolynomial,
    criticalSourceNormalizedReciprocalPolynomial, u, U, V] using hUV

/-- The canonical normalized reciprocal agrees through the critical horizon with the actual
reciprocal multiplied by the source scale. -/
theorem criticalSourceNormalizedReciprocalPolynomial_coeff
    (K : Type*) [Field K] [CharZero K]
    {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : k < m + n) :
    (criticalSourceNormalizedReciprocalPolynomial K hm hn).coeff k =
      criticalSourceScale K hm hn *
        (criticalSourceReciprocalPolynomial K m n).coeff k := by
  let U := criticalSourceNormalizedRawPolynomial K hm hn
  let V := criticalSourceNormalizedReciprocalPolynomial K hm hn
  let Y := C (criticalSourceScale K hm hn) *
    criticalSourceReciprocalPolynomial K m n
  have hU0 : U.coeff 0 = 1 := finiteUnitPolynomial_coeff_zero _
  have hUV : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣ U * V - 1 :=
    X_pow_dvd_normalizedRaw_mul_normalizedReciprocal_sub_one K hm hn
  have hUY : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣ U * Y - 1 :=
    X_pow_dvd_normalizedRaw_mul_scaleReciprocal_sub_one K hm hn
  have hcoeff : V.coeff k = Y.coeff k :=
    inverse_mod_coeff_unique (m + n) U V Y hU0 hUV hUY hk
  simpa [V, Y, Polynomial.coeff_C_mul] using hcoeff

/-- Squaring preserves the scale relation through the critical horizon. -/
theorem criticalSourceNormalizedReciprocalPolynomial_sq_coeff
    (K : Type*) [Field K] [CharZero K]
    {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : k < m + n) :
    ((criticalSourceNormalizedReciprocalPolynomial K hm hn) ^ 2).coeff k =
      (criticalSourceScale K hm hn) ^ 2 *
        ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff k := by
  simp only [pow_two, Polynomial.coeff_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij_sum : ij.1 + ij.2 = k :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [criticalSourceNormalizedReciprocalPolynomial_coeff K hm hn
      (k := ij.1) (by omega),
    criticalSourceNormalizedReciprocalPolynomial_coeff K hm hn
      (k := ij.2) (by omega)]
  ring

/-- The normalized reciprocal-square coordinate series is the square of the normalized reciprocal
polynomial through the entire critical horizon. -/
theorem unitConstantSeries_criticalSourceReciprocalSquarePositive
    (K : Type*) [Field K] [CharZero K]
    {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : k < m + n) :
    unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn) k =
      ((criticalSourceNormalizedReciprocalPolynomial K hm hn) ^ 2).coeff k := by
  rcases k with _ | k
  · simp [criticalSourceNormalizedReciprocalPolynomial, pow_two]
  · have hk' : k < m + n - 1 := by omega
    rw [unitConstantSeries_succ _ hk']
    rfl

/-- Actual reciprocal-square coefficients differ from normalized Schur coordinates by exactly the
square of the source scale. -/
theorem unitConstantSeries_criticalSourceReciprocalSquarePositive_eq_scale
    (K : Type*) [Field K] [CharZero K]
    {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : k < m + n) :
    unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn) k =
      (criticalSourceScale K hm hn) ^ 2 *
        ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff k := by
  rw [unitConstantSeries_criticalSourceReciprocalSquarePositive K hm hn hk,
    criticalSourceNormalizedReciprocalPolynomial_sq_coeff K hm hn hk]

/-- The normalized Schur matrix is the source-scale square times the actual reciprocal Toeplitz
matrix. -/
theorem rectangularSchurToeplitz_normalized_eq_scale_smul_actual
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    rectangularSchurToeplitz
        (unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn)) n m =
      (criticalSourceScale K hm hn) ^ 2 •
        rectangularSchurToeplitz
          (fun k => ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff k) n m := by
  apply Matrix.ext
  intro r i
  rw [Matrix.smul_apply]
  simp only [rectangularSchurToeplitz]
  by_cases hi : (i : ℕ) ≤ n + (r : ℕ)
  · rw [if_pos hi, if_pos hi, smul_eq_mul,
      unitConstantSeries_criticalSourceReciprocalSquarePositive_eq_scale K hm hn]
    omega
  · simp [hi]

/-- Conversely, the actual reciprocal Toeplitz matrix is the normalized Schur matrix multiplied
by the inverse scale square. -/
theorem rectangularSchurToeplitz_actual_eq_invScale_smul_normalized
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    rectangularSchurToeplitz
        (fun k => ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff k) n m =
      ((criticalSourceScale K hm hn) ^ 2)⁻¹ •
        rectangularSchurToeplitz
          (unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn)) n m := by
  rw [rectangularSchurToeplitz_normalized_eq_scale_smul_actual K hm hn,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (criticalSourceScale_ne_zero K hm hn)),
    one_smul]

/-- **Actual Jacobian/Schur-divisor identity.**  The determinant of the concrete critical
reciprocal Jacobian is the evaluated irreducible Schur equation times an explicit unit. -/
theorem criticalSourceReciprocalJacobian_det_eq_schurRamification
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalReciprocalJacobian
        (criticalSourceReciprocalPolynomial K m n) n m).det =
      (-1 : criticalSourceField K m n) ^ m *
        (((criticalSourceScale K hm hn) ^ 2)⁻¹) ^ m *
          MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn)
            (criticalSourceSchurRamificationPolynomial K m n) := by
  rw [criticalReciprocalJacobian_det_eq_rectangularSchur,
    show (fun k =>
      (criticalSourceReciprocalPolynomial K m n *
        criticalSourceReciprocalPolynomial K m n).coeff k) =
      (fun k => ((criticalSourceReciprocalPolynomial K m n) ^ 2).coeff k) by
        simp [pow_two],
    rectangularSchurToeplitz_actual_eq_invScale_smul_normalized K hm hn,
    Matrix.det_smul, aeval_criticalSourceSchurRamificationPolynomial K hm hn]
  simp only [Fintype.card_fin]
  ring

end

end GaloisForLFunctions.HTGeometry
