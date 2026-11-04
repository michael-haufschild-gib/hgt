import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.DilationPacketOperator
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.BoundedVariationDilationEnergy

/-!
# Exact complete mixed channels

The neutral bilinear form retains the scalar, prime, center, cross and
nonratio terms. Its comparison with finite dilation has an explicit
Mertens correction of uniformly bounded packet norm.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory

/-- The complete neutral bilinear form retains every scalar, prime, center, cross and nonratio channel. -/
theorem complete_neutral_mixed_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    {u y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu1 : u ∈ (conductorSubspace 1 N)ᗮ) (hy1 : y ∈ (conductorSubspace 1 N)ᗮ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u, y⟫ =
      (Real.log N + completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ⟪u, y⟫ -
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, y⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, y⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, y⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, y⟫ -
      ⟪upwardPrimeVector φ c N u, y⟫ := by
  have hI : Matrix.toEuclideanLin
      (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) u = u := by
    ext n
    change Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) u n = u n
    rw [Matrix.one_mulVec]
  rw [completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM hc (by omega)]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hI, inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM hc (by omega),
    inner_add_left, fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one φ c hN hu1 hy1]
  ring

/-- Orthogonal neutral source and receiver retain precisely the prime, center, cross and two nonratio channels. -/
theorem complete_orthogonal_mixed_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    {u y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu1 : u ∈ (conductorSubspace 1 N)ᗮ) (hy1 : y ∈ (conductorSubspace 1 N)ᗮ)
    (huy : ⟪u, y⟫ = 0) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u, y⟫ =
      -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, y⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, y⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, y⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, y⟫ -
      ⟪upwardPrimeVector φ c N u, y⟫ := by
  rw [complete_neutral_mixed_channels hφ hsupp hM hc hN hu1 hy1, huy, mul_zero,
    zero_sub]

#print axioms complete_orthogonal_mixed_channels

/-- The finite quotient-floor and Mertens correction is uniformly bounded on every row. -/
theorem mertens_horizon_row_bound {N n : ℕ} (hn : n ∈ Icc 1 N) :
    |ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N| ≤ Real.log 8 + 4 := by
  have hlo := row_ge (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  have hhi := row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  change Real.log N - (Real.log 8 + 4) ≤ ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n at hlo
  change ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n ≤ Real.log N + (Real.log 4 + 4) at hhi
  have h48 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, h48]

def mertensHorizonRemainder (N : ℕ) (F : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  packetVector (fun n => (ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N) * F n) N

/-- The literal quotient correction has a horizon-independent packet operator norm. -/
theorem mertens_remainder_norm (N : ℕ) (F : ℕ → ℝ) :
    ‖mertensHorizonRemainder N F‖ ≤ (Real.log 8 + 4) * ‖packetVector F N‖ := by
  have hC : 0 ≤ Real.log 8 + 4 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
    linarith only [h]
  have hsq : ‖mertensHorizonRemainder N F‖ ^ 2 ≤
      (Real.log 8 + 4) ^ 2 * ‖packetVector F N‖ ^ 2 := by
    rw [mertensHorizonRemainder, packetVector_norm_sq, packetVector_norm_sq, mul_sum]
    apply sum_le_sum
    intro n hn
    have hd := pow_le_pow_left₀ (abs_nonneg _) (mertens_horizon_row_bound hn) 2
    rw [sq_abs] at hd
    rw [mul_pow]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (sq_nonneg (F n))) (Nat.cast_nonneg n)).trans_eq (by ring)
  have hr : 0 ≤ (Real.log 8 + 4) * ‖packetVector F N‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith only [hsq, norm_nonneg (mertensHorizonRemainder N F), hr]

/-- The dilation row retains exactly its bounded quotient correction beyond the scalar logarithm. -/
theorem dilationPacketVector_split (N : ℕ) (F : ℕ → ℝ) :
    dilationPacketVector N F =
      Real.log N • packetVector F N - Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N) +
        mertensHorizonRemainder N F := by
  ext n
  change (ArithmeticCouplingTheory.mertensSum (N / n) + Real.log (n : ℕ)) * F n / Real.sqrt (n : ℕ) -
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N)) n =
    Real.log N * (F n / Real.sqrt (n : ℕ)) -
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (packetVector F N)) n +
        ((ArithmeticCouplingTheory.mertensSum (N / n) + Real.log (n : ℕ) - Real.log N) * F n / Real.sqrt (n : ℕ))
  ring

/-- Comparison with the finite dilation form retains the exact self and Mertens corrections. -/
theorem complete_neutral_dilation_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    (F G : ℕ → ℝ)
    (hF : packetVector F N ∈ (conductorSubspace 1 N)ᗮ)
    (hG : packetVector G N ∈ (conductorSubspace 1 N)ᗮ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ -
        jumpPairing N F G =
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant + completeWeilSelfError φ c N) *
        ⟪packetVector F N, packetVector G N⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (packetVector F N), packetVector G N⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N), packetVector G N⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N) -
        downwardPrimeVector φ c N (packetVector F N), packetVector G N⟫ -
      ⟪upwardPrimeVector φ c N (packetVector F N), packetVector G N⟫ -
      ⟪mertensHorizonRemainder N F, packetVector G N⟫ := by
  rw [complete_neutral_mixed_channels hφ hsupp hM hc hN hF hG,
    jumpPairing_eq_inner_dilationPacketVector, dilationPacketVector_split]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

#print axioms complete_neutral_dilation_channels

/-- Every complete mixed correction survives explicitly after comparison with the literal dilation form. -/
theorem complete_orthogonal_dilation_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    (F G : ℕ → ℝ)
    (hF : packetVector F N ∈ (conductorSubspace 1 N)ᗮ)
    (hG : packetVector G N ∈ (conductorSubspace 1 N)ᗮ)
    (hFG : ⟪packetVector F N, packetVector G N⟫ = 0) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ -
        jumpPairing N F G =
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
        (packetVector F N), packetVector G N⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N), packetVector G N⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N) -
        downwardPrimeVector φ c N (packetVector F N), packetVector G N⟫ -
      ⟪upwardPrimeVector φ c N (packetVector F N), packetVector G N⟫ -
      ⟪mertensHorizonRemainder N F, packetVector G N⟫ := by
  rw [complete_neutral_dilation_channels hφ hsupp hM hc hN F G hF hG,
    hFG, mul_zero, zero_add]

#print axioms mertens_remainder_norm
#print axioms complete_orthogonal_dilation_channels

end GaloisForLFunctions.ArithmeticCouplingTheory
