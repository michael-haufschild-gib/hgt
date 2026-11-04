import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.MixedChannelDecomposition

/-!
# Norm control of the exact complete mixed corrections

Orthogonal neutral packets have no scalar or pole-error pairing. Every
remaining correction is retained, with a uniform bound for the literal
quotient-floor Mertens remainder.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms

/-- The full mixed correction is bounded by its four geometric channels and the exact Mertens remainder. -/
theorem complete_orthogonal_dilation_error_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N)
    (F G : ℕ → ℝ)
    (hF : packetVector F N ∈ (conductorSubspace 1 N)ᗮ)
    (hG : packetVector G N ∈ (conductorSubspace 1 N)ᗮ)
    (hFG : ⟪packetVector F N, packetVector G N⟫ = 0) :
    |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ -
        jumpPairing N F G| ≤
      (‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) (packetVector F N)‖ +
        ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N)‖ +
        ‖Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N) -
          downwardPrimeVector φ c N (packetVector F N)‖ +
        ‖upwardPrimeVector φ c N (packetVector F N)‖ +
        (Real.log 8 + 4) * ‖packetVector F N‖) * ‖packetVector G N‖ := by
  have htriangle (a b d e f : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
      ‖a - b + d - e - f‖ ≤ ‖a‖ + ‖b‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le a b) (le_refl ‖d‖))) (le_refl ‖e‖)))
      (le_refl ‖f‖))
  calc
    _ = |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (packetVector F N) -
        Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (packetVector F N) +
        (Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N) -
          downwardPrimeVector φ c N (packetVector F N)) -
        upwardPrimeVector φ c N (packetVector F N) - mertensHorizonRemainder N F,
        packetVector G N⟫| := by
      rw [complete_orthogonal_dilation_channels hφ hsupp hM hc hN F G hF hG hFG]
      simp only [inner_sub_left, inner_add_left]
    _ ≤ _ := (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      ((htriangle _ _ _ _ _).trans (add_le_add (le_refl _) (mertens_remainder_norm N F)))
      (norm_nonneg _))

#print axioms complete_orthogonal_dilation_error_le

end GaloisForLFunctions.ArithmeticCouplingTheory
