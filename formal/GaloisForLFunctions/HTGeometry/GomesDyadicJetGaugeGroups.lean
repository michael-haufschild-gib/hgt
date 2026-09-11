import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeScalarBoundary
import GaloisForLFunctions.HTGeometry.GomesDyadicJetSymmetrySelection

/-!
# Actual gauge groups selected by the named dyadic phases

The existing Bottcher multipliers now classify actual invertible symmetry
groups. Increasing depth removes symmetries; the unipotent factor disappears
exactly when the dyadic order reaches the finite horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Named dyadic phases give scalar gauge groups exactly at their known horizon boundary. -/
theorem gomesDyadicJetGaugeGroup_eq_zero_phase_iff (n k : ℕ) :
    gomesTruncatedJetGaugeGroup n (Bottcher.dyadicRoot k) = gomesTruncatedJetGaugeGroup n 0 ↔
      n + 1 ≤ 2 ^ k := by
  rw [gomesTruncatedJetGaugeGroup_eq_iff_algebra, gomesTruncatedJetJointAlgebra_zero,
    gomesDyadicJetJointAlgebra_eq_bot_iff]

/-- Increasing the named dyadic depth can only remove actual invertible symmetries. -/
theorem gomesDyadicJetGaugeGroup_succ_le (n k : ℕ) :
    gomesTruncatedJetGaugeGroup n (Bottcher.dyadicRoot (k + 1)) ≤
      gomesTruncatedJetGaugeGroup n (Bottcher.dyadicRoot k) := by
  rw [gomesTruncatedJetGaugeGroup_le_iff_algebra]
  exact gomesDyadicJetJointAlgebra_succ_le n k

/-- The dyadic unipotent subgroup disappears at precisely the same sharp horizon. -/
theorem gomesDyadicJetUnipotentGroup_eq_bot_iff (n k : ℕ) :
    gomesTruncatedJetUnipotentGroup n (Bottcher.dyadicRoot k) = ⊥ ↔ n + 1 ≤ 2 ^ k := by
  rw [gomesTruncatedJetUnipotentGroup_eq_bot_iff, Bottcher.orderOf_dyadicRoot_named,
    or_iff_right (pow_ne_zero k (Nat.ne_of_gt (Nat.succ_pos 1)))]

/-- Comparison of named dyadic gauge groups is exactly comparison of the integral weights below the horizon. -/
theorem gomesDyadicJetGaugeGroup_le_iff_weights (n k l : ℕ) :
    gomesTruncatedJetGaugeGroup n (Bottcher.dyadicRoot k) ≤
      gomesTruncatedJetGaugeGroup n (Bottcher.dyadicRoot l) ↔
      ∀ j : Fin (n + 1), 2 ^ k ∣ j.val → 2 ^ l ∣ j.val := by
  rw [gomesTruncatedJetGaugeGroup_le_iff_weights,
    Bottcher.orderOf_dyadicRoot_named, Bottcher.orderOf_dyadicRoot_named]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
