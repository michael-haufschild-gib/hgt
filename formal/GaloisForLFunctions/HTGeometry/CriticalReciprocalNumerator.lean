import GaloisForLFunctions.HTGeometry.CriticalReciprocalSourceCoordinates
import GaloisForLFunctions.HTGeometry.CoordinateDivisorOrder

/-!
# Cleared numerators of truncated reciprocal coefficients

For raw variables `x₀,…`, the coefficient `y_k` of the reciprocal series has denominator
`x₀^(k+1)`.  This file constructs its exact numerator recursively.  A specialization with only
`x₀=x₁=1` nonzero proves that numerator never vanishes identically on any coordinate divisor
`x_m=0` with `m ≥ 2`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1000000

/-- Coordinate `j` when it is present in a finite raw-coordinate ring, and zero otherwise. -/
def finiteRawX (K : Type*) [Field K] (L j : ℕ) : MvPolynomial (Fin L) K :=
  if h : j < L then X ⟨j, h⟩ else 0

/-- Numerator of the `k`-th ordinary reciprocal coefficient after clearing `x₀^(k+1)`. -/
def criticalReciprocalNumerator (K : Type*) [Field K] (L : ℕ) :
    ℕ → MvPolynomial (Fin L) K
  | 0 => 1
  | k + 1 =>
      -∑ i : Fin (k + 1),
        finiteRawX K L ((i : ℕ) + 1) *
          criticalReciprocalNumerator K L (k - (i : ℕ)) *
            finiteRawX K L 0 ^ (i : ℕ)
termination_by k => k
decreasing_by omega

/-- Test point with `x₀=x₁=1` and every higher coordinate zero. -/
def criticalReciprocalTestPoint (K : Type*) [Field K] {L : ℕ} (i : Fin L) : K :=
  if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then 1 else 0

@[simp] theorem aeval_finiteRawX_zero
    (K : Type*) [Field K] {L : ℕ} (hL : 0 < L) :
    MvPolynomial.aeval (criticalReciprocalTestPoint K)
      (finiteRawX K L 0) = 1 := by
  rw [finiteRawX, dif_pos hL, MvPolynomial.aeval_X]
  simp [criticalReciprocalTestPoint]

@[simp] theorem aeval_finiteRawX_succ
    (K : Type*) [Field K] {L i : ℕ} (hi : i + 1 < L) :
    MvPolynomial.aeval (criticalReciprocalTestPoint K)
      (finiteRawX K L (i + 1)) = if i = 0 then 1 else 0 := by
  rw [finiteRawX, dif_pos hi, MvPolynomial.aeval_X]
  by_cases h : i = 0
  · subst i
    simp [criticalReciprocalTestPoint]
  · have hi1 : i + 1 ≠ 1 := by omega
    simp [criticalReciprocalTestPoint, h, hi1]

/-- At the test point, the cleared reciprocal numerator is exactly `(-1)^k`. -/
theorem aeval_criticalReciprocalNumerator_testPoint
    (K : Type*) [Field K] {L k : ℕ} (hk : k < L) :
    MvPolynomial.aeval (criticalReciprocalTestPoint K)
      (criticalReciprocalNumerator K L k) = (-1 : K) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simp [criticalReciprocalNumerator]
      · rw [criticalReciprocalNumerator, map_neg, map_sum]
        simp only [map_mul, map_pow]
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (k + 1))]
        · rw [aeval_finiteRawX_succ K (by omega), if_pos rfl,
            Nat.sub_zero, ih k (by omega) (by omega),
            aeval_finiteRawX_zero K (by omega), pow_zero, mul_one, one_mul]
          rw [pow_succ]
          ring
        · intro i _ hi0
          have hi0' : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
          rw [aeval_finiteRawX_succ K (by omega), if_neg hi0', zero_mul, zero_mul]
        · intro hnot
          exact (hnot (Finset.mem_univ (⟨0, by omega⟩ : Fin (k + 1)))).elim

/-- For `m ≥ 2`, the reciprocal numerator does not vanish identically on `x_m=0`. -/
theorem criticalReciprocalNumerator_not_mem_coordDivisor
    (K : Type*) [Field K] {L k m : ℕ} (hk : k < L) (hm : 2 ≤ m) (hmL : m < L) :
    criticalReciprocalNumerator K L k ∉
      (coordDivisor (k := K) (⟨m, hmL⟩ : Fin L)).1 := by
  intro hmem
  rw [coordDivisor_val, Ideal.mem_span_singleton] at hmem
  have hdvd := map_dvd
    (MvPolynomial.aeval (criticalReciprocalTestPoint K)) hmem
  rw [aeval_criticalReciprocalNumerator_testPoint K hk,
    MvPolynomial.aeval_X] at hdvd
  have hcoord : criticalReciprocalTestPoint K (⟨m, hmL⟩ : Fin L) = 0 := by
    simp [criticalReciprocalTestPoint]
    omega
  rw [hcoord] at hdvd
  exact (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)) (zero_dvd_iff.mp hdvd)

/-- The constant actual reciprocal coordinate is the inverse raw constant coordinate. -/
theorem criticalSourceRecip_zero_eq_inv
    (K : Type*) [Field K] {m n : ℕ} (hL : 0 < m + n) :
    criticalSourceRecip K m n ⟨0, hL⟩ =
      (criticalSourceRaw K m n ⟨0, hL⟩)⁻¹ := by
  have hmul := congrArg (genericJetFieldMap K (m + n))
    (genericRaw_zero_mul_inv K (m + n))
  rw [map_mul, map_one] at hmul
  apply Subtype.ext
  apply eq_inv_of_mul_eq_one_right
  simpa [criticalSourceRecip, criticalSourceRaw, criticalAmbientRaw,
    criticalAmbientRecip, genericRecip] using hmul

/-- Actual reciprocal coordinates obey the ordinary truncated inverse recurrence internally in
the source field. -/
theorem criticalSourceRecip_succ
    (K : Type*) [Field K] {m n k : ℕ} (hk : k + 1 < m + n) :
    criticalSourceRecip K m n ⟨k + 1, hk⟩ =
      -criticalSourceRecip K m n ⟨0, by omega⟩ *
        ∑ i : Fin (k + 1),
          criticalSourceRaw K m n ⟨(i : ℕ) + 1, by omega⟩ *
            criticalSourceRecip K m n ⟨k - (i : ℕ), by omega⟩ := by
  apply (criticalSourceField K m n).val.injective
  simp only [map_neg, map_mul, map_sum]
  change genericJetFieldMap K (m + n) (genericRecip K (m + n) (k + 1)) =
    -genericJetFieldMap K (m + n) (genericRecip K (m + n) 0) *
      ∑ i : Fin (k + 1),
        genericJetFieldMap K (m + n) (genericRaw K (m + n) ((i : ℕ) + 1)) *
          genericJetFieldMap K (m + n) (genericRecip K (m + n) (k - (i : ℕ)))
  conv_lhs => rw [genericRecip]
  rw [map_mul, map_neg, map_sum]
  simp only [map_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [genericRecip]

/-- Evaluating a present finite raw variable at the actual raw source coordinates returns that
coordinate. -/
@[simp] theorem aeval_criticalSourceRaw_finiteRawX
    (K : Type*) [Field K] {m n j : ℕ} (hj : j < m + n) :
    MvPolynomial.aeval (criticalSourceRaw K m n)
        (finiteRawX K (m + n) j) =
      criticalSourceRaw K m n ⟨j, hj⟩ := by
  rw [finiteRawX, dif_pos hj, MvPolynomial.aeval_X]

/-- Actual reciprocal coefficients equal the cleared numerator divided by the expected power of
the actual raw constant coordinate. -/
theorem criticalSourceRecip_eq_numerator_div
    (K : Type*) [Field K] {m n k : ℕ} (hk : k < m + n) :
    criticalSourceRecip K m n ⟨k, hk⟩ =
      MvPolynomial.aeval (criticalSourceRaw K m n)
          (criticalReciprocalNumerator K (m + n) k) /
        (criticalSourceRaw K m n ⟨0, by omega⟩) ^ (k + 1) := by
  have hs : criticalSourceRaw K m n ⟨0, by omega⟩ ≠ 0 := by
    intro hzero
    exact ((algebraicIndependent_criticalSourceRaw K m n).transcendental
      ⟨0, by omega⟩) (hzero ▸ isAlgebraic_zero)
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · rw [criticalReciprocalNumerator, map_one, pow_one, one_div]
        exact criticalSourceRecip_zero_eq_inv K (by omega)
      · have hk' : k + 1 < m + n := by omega
        rw [criticalSourceRecip_succ K hk',
          criticalSourceRecip_zero_eq_inv K (by omega),
          criticalReciprocalNumerator, map_neg, map_sum]
        simp only [map_mul, map_pow]
        rw [show k + 1 + 1 = k + 2 by omega]
        rw [eq_div_iff (pow_ne_zero (k + 2) (by
          simpa using hs))]
        rw [Finset.mul_sum]
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hki : k - (i : ℕ) < m + n := by omega
        have hrec := ih (k - (i : ℕ)) (by omega) hki
        rw [hrec hs,
          aeval_criticalSourceRaw_finiteRawX K (by omega : (i : ℕ) + 1 < m + n),
          aeval_criticalSourceRaw_finiteRawX K (by omega : 0 < m + n)]
        field_simp
        have hi_le : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
        have hpow : criticalSourceRaw K m n ⟨0, by omega⟩ *
              criticalSourceRaw K m n ⟨0, by omega⟩ ^ (k - (i : ℕ) + 1) *
                criticalSourceRaw K m n ⟨0, by omega⟩ ^ (i : ℕ) =
            criticalSourceRaw K m n ⟨0, by omega⟩ ^ (k + 2) := by
          calc
            _ = criticalSourceRaw K m n ⟨0, by omega⟩ ^ (1 : ℕ) *
                  criticalSourceRaw K m n ⟨0, by omega⟩ ^ (k - (i : ℕ) + 1) *
                    criticalSourceRaw K m n ⟨0, by omega⟩ ^ (i : ℕ) := by rw [pow_one]
            _ = criticalSourceRaw K m n ⟨0, by omega⟩ ^
                  (1 + (k - (i : ℕ) + 1)) *
                    criticalSourceRaw K m n ⟨0, by omega⟩ ^ (i : ℕ) := by
                      rw [← pow_add]
            _ = criticalSourceRaw K m n ⟨0, by omega⟩ ^
                  (1 + (k - (i : ℕ) + 1) + (i : ℕ)) := by rw [← pow_add]
            _ = _ := by congr 1; omega
        rw [← hpow]
        ring

end

end GaloisForLFunctions.HTGeometry
