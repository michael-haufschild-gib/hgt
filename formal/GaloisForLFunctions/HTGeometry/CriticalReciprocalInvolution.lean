import GaloisForLFunctions.HTGeometry.CriticalRawCoordinateValuation

/-!
# Reciprocal inversion recovers the actual raw source coordinates

The actual raw and reciprocal truncations are inverse modulo the full critical horizon.  Reversing
the convolution recurrence therefore expresses every raw coefficient by the same universal cleared
reciprocal numerator, now evaluated in the reciprocal coordinate system.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial Polynomial

set_option maxHeartbeats 1000000

/-- The actual raw coefficients satisfy the inverse recurrence with raw and reciprocal roles
reversed. -/
theorem criticalSourceRaw_succ
    (K : Type*) [Field K] {m n k : ℕ} (hk : k + 1 < m + n) :
    criticalSourceRaw K m n ⟨k + 1, hk⟩ =
      -criticalSourceRaw K m n ⟨0, by omega⟩ *
        ∑ i : Fin (k + 1),
          criticalSourceRecip K m n ⟨(i : ℕ) + 1, by omega⟩ *
            criticalSourceRaw K m n ⟨k - (i : ℕ), by omega⟩ := by
  let R := criticalSourceRawPolynomial K m n
  let Q := criticalSourceReciprocalPolynomial K m n
  have hQR : (X : (criticalSourceField K m n)[X]) ^ (m + n) ∣ Q * R - 1 := by
    simpa [R, Q, mul_comm] using
      (X_pow_dvd_criticalSourceRaw_mul_reciprocal_sub_one K m n)
  have hQR' : (X : (criticalSourceField K m n)[X]) ^ (m + n - 1 + 1) ∣
      Q * R - 1 := by
    simpa only [show m + n - 1 + 1 = m + n by omega] using hQR
  have hzero := coeff_zero_mul_of_dvd (L := m + n - 1) hQR'
  have hrec := coeff_zero_mul_coeff_of_dvd (L := m + n - 1) hQR'
    (k := k + 1) (by omega) (by omega)
  have hQ0 : Q.coeff 0 = criticalSourceRecip K m n ⟨0, by omega⟩ :=
    criticalSourceReciprocalPolynomial_coeff K m n 0 (by omega)
  have hR0 : R.coeff 0 = criticalSourceRaw K m n ⟨0, by omega⟩ :=
    criticalSourceRawPolynomial_coeff K m n 0 (by omega)
  rw [hQ0, hR0] at hzero
  have hzero' : criticalSourceRaw K m n ⟨0, by omega⟩ *
      criticalSourceRecip K m n ⟨0, by omega⟩ = 1 := by
    simpa only [mul_comm] using hzero
  have hrec' : criticalSourceRecip K m n ⟨0, by omega⟩ *
      criticalSourceRaw K m n ⟨k + 1, hk⟩ =
        -∑ i : Fin (k + 1),
          criticalSourceRecip K m n ⟨(i : ℕ) + 1, by omega⟩ *
            criticalSourceRaw K m n ⟨k - (i : ℕ), by omega⟩ := by
    rw [hQ0, criticalSourceRawPolynomial_coeff K m n (k + 1) hk] at hrec
    dsimp [Q, R] at hrec
    rw [← Fin.sum_univ_eq_sum_range] at hrec
    calc
      _ = -∑ i : Fin (k + 1),
          (criticalSourceReciprocalPolynomial K m n).coeff ((i : ℕ) + 1) *
            (criticalSourceRawPolynomial K m n).coeff
              (k + 1 - ((i : ℕ) + 1)) := hrec
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [criticalSourceReciprocalPolynomial_coeff K m n ((i : ℕ) + 1) (by omega),
          criticalSourceRawPolynomial_coeff K m n (k + 1 - ((i : ℕ) + 1)) (by omega)]
        congr 2
        apply Fin.ext
        dsimp only [Fin.val_mk]
        have hi : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
        omega
  calc
    criticalSourceRaw K m n ⟨k + 1, hk⟩ =
        (criticalSourceRaw K m n ⟨0, by omega⟩ *
          criticalSourceRecip K m n ⟨0, by omega⟩) *
            criticalSourceRaw K m n ⟨k + 1, hk⟩ := by rw [hzero', one_mul]
    _ = criticalSourceRaw K m n ⟨0, by omega⟩ *
        (criticalSourceRecip K m n ⟨0, by omega⟩ *
          criticalSourceRaw K m n ⟨k + 1, hk⟩) := by ring
    _ = criticalSourceRaw K m n ⟨0, by omega⟩ *
        (-∑ i : Fin (k + 1),
          criticalSourceRecip K m n ⟨(i : ℕ) + 1, by omega⟩ *
            criticalSourceRaw K m n ⟨k - (i : ℕ), by omega⟩) := by rw [hrec']
    _ = -criticalSourceRaw K m n ⟨0, by omega⟩ *
        ∑ i : Fin (k + 1),
          criticalSourceRecip K m n ⟨(i : ℕ) + 1, by omega⟩ *
            criticalSourceRaw K m n ⟨k - (i : ℕ), by omega⟩ := by ring

/-- Evaluating a present reciprocal-coordinate variable returns that actual reciprocal source
coordinate. -/
@[simp] theorem aeval_criticalSourceRecipReindexed_finiteRawX
    (K : Type*) [Field K] [CharZero K]
    {m n j : ℕ} (hm : 0 < m) (hn : 0 < n) (hj : j < m + n - 1 + 1) :
    MvPolynomial.aeval (criticalSourceRecipReindexed K hm hn)
        (finiteRawX K (m + n - 1 + 1) j) =
      criticalSourceRecipReindexed K hm hn ⟨j, hj⟩ := by
  rw [finiteRawX, dif_pos hj, MvPolynomial.aeval_X]

/-- Applying reciprocal inversion twice recovers every actual raw coordinate.  Equivalently, each
raw coefficient is the universal cleared reciprocal numerator evaluated in the actual reciprocal
coordinate system. -/
theorem criticalSourceRaw_eq_reciprocalNumerator_div
    (K : Type*) [Field K] [CharZero K]
    {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) (hk : k < m + n) :
    criticalSourceRaw K m n ⟨k, hk⟩ =
      MvPolynomial.aeval (criticalSourceRecipReindexed K hm hn)
          (criticalReciprocalNumerator K (m + n - 1 + 1) k) /
        (criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩) ^ (k + 1) := by
  have hq0 : criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ≠ 0 :=
    criticalSourceRecipReindexed_zero_ne K hm hn
  have hrawZero : criticalSourceRaw K m n ⟨0, by omega⟩ =
      (criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩)⁻¹ := by
    have hbase := criticalSourceRecip_zero_eq_inv K (m := m) (n := n) (by omega)
    have hreindexed : criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ =
        (criticalSourceRaw K m n ⟨0, by omega⟩)⁻¹ := by
      unfold criticalSourceRecipReindexed
      convert hbase using 1 <;> apply congrArg <;> apply Fin.ext <;> rfl
    rw [hreindexed, inv_inv]
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · rw [criticalReciprocalNumerator, map_one, pow_one, one_div]
        exact hrawZero
      · have hk' : k + 1 < m + n := by omega
        rw [criticalSourceRaw_succ K hk', hrawZero,
          criticalReciprocalNumerator, map_neg, map_sum]
        simp only [map_mul, map_pow]
        rw [show k + 1 + 1 = k + 2 by omega]
        rw [eq_div_iff (pow_ne_zero (k + 2) hq0)]
        rw [Finset.mul_sum]
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hki : k - (i : ℕ) < m + n := by omega
        have hrec := ih (k - (i : ℕ)) (by omega) hki
        rw [hrec hq0 hrawZero,
          aeval_criticalSourceRecipReindexed_finiteRawX K hm hn
            (by omega : (i : ℕ) + 1 < m + n - 1 + 1),
          aeval_criticalSourceRecipReindexed_finiteRawX K hm hn
            (by omega : 0 < m + n - 1 + 1)]
        have hrecipSucc :
            criticalSourceRecipReindexed K hm hn ⟨(i : ℕ) + 1, by omega⟩ =
              criticalSourceRecip K m n ⟨(i : ℕ) + 1, by omega⟩ := by
          unfold criticalSourceRecipReindexed
          congr 1
        rw [hrecipSucc]
        field_simp
        have hi_le : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
        have hpow : criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ *
              criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^
                (k - (i : ℕ) + 1) *
              criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^ (i : ℕ) =
            criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^ (k + 2) := by
          calc
            _ = criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^ 1 *
                  criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^
                    (k - (i : ℕ) + 1) *
                  criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^ (i : ℕ) := by
                    rw [pow_one]
            _ = criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^
                  (1 + (k - (i : ℕ) + 1)) *
                    criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^ (i : ℕ) := by
                      rw [← pow_add]
            _ = criticalSourceRecipReindexed K hm hn ⟨0, by omega⟩ ^
                  (1 + (k - (i : ℕ) + 1) + (i : ℕ)) := by rw [← pow_add]
            _ = _ := by congr 1; omega
        rw [← hpow]
        ring

end

end GaloisForLFunctions.HTGeometry
