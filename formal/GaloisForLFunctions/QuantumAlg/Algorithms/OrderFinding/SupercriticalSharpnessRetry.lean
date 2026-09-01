import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.QuantumAlg.Algorithms.OrderFinding.Probability

/-!
# Supercritical-sharpness retry mechanism for order finding

`[BRIDGE]` The geometric one-touch product mechanism extracted from arXiv:2603.03257 is applied
to Shor's source-certified one-run order-recovery lower bound.  Positive orders are indexed as
`r + 1`, so every theorem below is unconditional and has no proposition-valued premise.
-/

open scoped BigOperators

namespace QuantumAlg.OrderFinding

/-- Shor's source lower bound is strictly positive at every positive order. -/
theorem shorOrderRecoverySuccessLowerBound_succ_pos (r : ℕ) :
    0 < shorOrderRecoverySuccessLowerBound (r + 1) := by
  unfold shorOrderRecoverySuccessLowerBound
  have htotient : 0 < Nat.totient (r + 1) :=
    Nat.totient_pos.mpr (Nat.succ_pos r)
  positivity

/-- Shor's source lower bound is at most one at every positive order. -/
theorem shorOrderRecoverySuccessLowerBound_succ_le_one (r : ℕ) :
    shorOrderRecoverySuccessLowerBound (r + 1) ≤ 1 := by
  unfold shorOrderRecoverySuccessLowerBound
  have htotientNat := Nat.totient_le (r + 1)
  have htotientReal : (Nat.totient (r + 1) : ℝ) ≤ (r + 1 : ℕ) := by
    exact_mod_cast htotientNat
  have hden : 0 < 3 * ((r + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  norm_num at htotientReal ⊢
  linarith

/-- Canonical all-fail envelope after `attempts` independent attempts, using Shor's certified
one-run success lower bound. -/
noncomputable def shorRetryFailureUpperBound (r attempts : ℕ) : ℝ :=
  (1 - shorOrderRecoverySuccessLowerBound (r + 1)) ^ attempts

/-- Retry failure envelope is nonnegative. -/
theorem shorRetryFailureUpperBound_nonneg (r attempts : ℕ) :
    0 ≤ shorRetryFailureUpperBound r attempts := by
  unfold shorRetryFailureUpperBound
  exact pow_nonneg (sub_nonneg.mpr
    (shorOrderRecoverySuccessLowerBound_succ_le_one r)) _

/-- Retry failure envelope never exceeds one. -/
theorem shorRetryFailureUpperBound_le_one (r attempts : ℕ) :
    shorRetryFailureUpperBound r attempts ≤ 1 := by
  unfold shorRetryFailureUpperBound
  exact pow_le_one₀
    (sub_nonneg.mpr (shorOrderRecoverySuccessLowerBound_succ_le_one r))
    (by linarith [shorOrderRecoverySuccessLowerBound_succ_pos r])

/-- Exact one-attempt recurrence for the failure envelope. -/
theorem shorRetryFailureUpperBound_succ (r attempts : ℕ) :
    shorRetryFailureUpperBound r (attempts + 1) =
      (1 - shorOrderRecoverySuccessLowerBound (r + 1)) *
        shorRetryFailureUpperBound r attempts := by
  simp [shorRetryFailureUpperBound, pow_succ, mul_comm]

/-- Paper's geometric product bound, instantiated at every canonical Shor retry stage. -/
theorem shorRetryFailureUpperBound_le_stageProduct (r attempts : ℕ) :
    shorRetryFailureUpperBound r attempts ≤
      ∏ _i : Fin attempts,
        (1 - shorOrderRecoverySuccessLowerBound (r + 1)) := by
  unfold shorRetryFailureUpperBound
  simpa only [Fintype.card_fin] using
    (GaloisForLFunctions.HTGeometry.retention_pow_le_prod
      (fun _i : Fin attempts ↦
        1 - shorOrderRecoverySuccessLowerBound (r + 1))
      (1 - shorOrderRecoverySuccessLowerBound (r + 1))
      (sub_nonneg.mpr (shorOrderRecoverySuccessLowerBound_succ_le_one r))
      (fun _i ↦ le_rfl))

/-- Canonical retry failure tends to zero for every positive order. -/
theorem shorRetryFailureUpperBound_tendsto_zero (r : ℕ) :
    Filter.Tendsto (shorRetryFailureUpperBound r) Filter.atTop (nhds 0) := by
  unfold shorRetryFailureUpperBound
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · exact sub_nonneg.mpr (shorOrderRecoverySuccessLowerBound_succ_le_one r)
  · linarith [shorOrderRecoverySuccessLowerBound_succ_pos r]

end QuantumAlg.OrderFinding
