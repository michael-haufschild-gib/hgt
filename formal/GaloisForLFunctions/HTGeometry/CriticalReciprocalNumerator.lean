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
      -∑ i ∈ Finset.range (k + 1),
        finiteRawX K L (i + 1) * criticalReciprocalNumerator K L (k - i) *
          finiteRawX K L 0 ^ i
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
        rw [Finset.sum_eq_single 0]
        · rw [aeval_finiteRawX_succ K (by omega), if_pos rfl,
            Nat.sub_zero, ih k (by omega) (by omega),
            aeval_finiteRawX_zero K (by omega), pow_zero, mul_one, one_mul]
          rw [pow_succ]
          ring
        · intro i hi hi0
          have hi' : i < k + 1 := Finset.mem_range.mp hi
          rw [aeval_finiteRawX_succ K (by omega), if_neg hi0, zero_mul, zero_mul]
        · simp

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
        have hmul := congrArg (genericJetFieldMap K (m + n))
          (genericRaw_zero_mul_inv K (m + n))
        rw [map_mul, map_one] at hmul
        apply Subtype.ext
        apply eq_inv_of_mul_eq_one_right
        simpa [criticalSourceRecip, criticalSourceRaw, criticalAmbientRaw,
          criticalAmbientRecip, genericRecip] using hmul
      · have hk' : k + 1 < m + n := by omega
        rw [criticalReciprocalNumerator, map_neg, map_sum]
        simp only [map_mul, map_pow]
        apply Subtype.ext
        change genericJetFieldMap K (m + n)
            (genericRecip K (m + n) (k + 1)) = _
        rw [genericRecip, map_mul, map_neg, map_sum]
        simp only [criticalSourceRaw, criticalAmbientRaw, map_neg, map_mul, map_sum, map_pow]
        have hinv : genericJetFieldMap K (m + n) (genericInv K (m + n)) =
            (criticalAmbientRaw K m n 0)⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          simpa [criticalAmbientRaw] using congrArg
            (genericJetFieldMap K (m + n)) (genericRaw_zero_mul_inv K (m + n))
        rw [hinv]
        simp only [criticalAmbientRaw]
        rw [div_eq_iff (pow_ne_zero (k + 2) (by
          simpa [criticalSourceRaw, criticalAmbientRaw] using hs))]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < k + 1 := Finset.mem_range.mp hi
        have hki : k - i < m + n := by omega
        have hrec := ih (k - i) (by omega) hki
        apply_fun Subtype.val at hrec
        simp only [criticalSourceRecip, criticalSourceRaw, criticalAmbientRaw,
          Subtype.coe_div, Subtype.coe_pow] at hrec
        rw [hrec]
        field_simp
        ring

end

end GaloisForLFunctions.HTGeometry
