import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeRampProfile

/-!
# The complete signed complement profile

At every fixed polynomial cutoff-to-horizon ratio, the literal complete
operator has the same pairing as the logarithmic receiving ramp against
every unit vector in the growing conductor complement.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms SelectiveMultiscaleArithmeticPositivity

/-- The complete signed residual is the explicit ramp on every bounded complementary receiver. -/
theorem tendsto_harmonicPrimeCharge_complete_complement_profile {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d)
    (t : ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ᶠ X in atTop, packetVector (G X) (X ^ d) ∈ (conductorSubspace (X ^ a) (X ^ d))ᗮ ∧
      ‖packetVector (G X) (X ^ d)‖ ≤ 1) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
        (completeWeilMatrix φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d))
          (harmonicPrimeChargeVector (X ^ a) (X ^ d) t), packetVector (G X) (X ^ d)⟫ -
      ⟪primeChargeRampVector (X ^ a) (X ^ d) t, packetVector (G X) (X ^ d)⟫)
      atTop (𝓝 0) := by
  have hd : 0 < d := ha.trans_le had
  have hQ : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hN : Tendsto (fun X : ℕ => X ^ d) atTop atTop := tendsto_pow_atTop hd.ne'
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hneutral : ∀ᶠ X in atTop,
      (∑ n ∈ Icc 1 (X ^ d), G X n / (n : ℝ) = 0) ∧ ‖packetVector (G X) (X ^ d)‖ ≤ 1 := by
    filter_upwards [eventually_ge_atTop 2, hG] with X hX hg
    exact ⟨harmonic_neutral_of_conductor_complement (Nat.one_le_pow a X (by omega))
      (hX.trans (Nat.le_pow hd)) (G X) hg.1, hg.2⟩
  have hsq := tendsto_harmonicPrimeCharge_polynomial_mixed_error_sq
    hφ hφ0 hsupp hM hK ha had t G hneutral
  have hrem : Tendsto (fun X : ℕ =>
      (completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (G X) -
      jumpPairing (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (G X)) /
        Real.sqrt (Real.log (X ^ d : ℕ))) atTop (𝓝 0) := by
    have h := hsq.sqrt
    simp only [Real.sqrt_zero] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [] with X
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hsmall := ((tendsto_primeReciprocal_add_div_primePoleScale
    (primeChargeRampErrorConstant + 1)).comp hQ).const_mul (2 * |t|)
  simp only [mul_zero] at hsmall
  have htail : Tendsto (fun X : ℕ =>
      ⟪primeChargeTailVector (X ^ a) (X ^ d) t - primeChargeRampVector (X ^ a) (X ^ d) t,
        packetVector (G X) (X ^ d)⟫) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hsmall
    filter_upwards [eventually_ge_atTop 2, hL.eventually (eventually_ge_atTop 1), hG]
      with X hX hl hg
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖primeChargeTailVector (X ^ a) (X ^ d) t - primeChargeRampVector (X ^ a) (X ^ d) t‖ *
          ‖packetVector (G X) (X ^ d)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖primeChargeTailVector (X ^ a) (X ^ d) t - primeChargeRampVector (X ^ a) (X ^ d) t‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hg.2 (norm_nonneg _)
      _ ≤ _ := primeChargeTailVector_sub_ramp_norm_le (hX.trans (Nat.le_pow ha)) hl t
  have h := hrem.add htail
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2, hG] with X hX hg
  have hj := harmonicPrimeCharge_complement_pairing (Nat.one_le_pow a X (by omega))
    (hX.trans (Nat.le_pow hd)) t (G X) hg.1
  rw [hj, inner_sub_left, primeChargeTailVector, real_inner_smul_left, packetVector_inner,
    harmonicPrimeChargeVector, map_smul, real_inner_smul_left]
  unfold completePacketPairing
  ring

#print axioms tendsto_harmonicPrimeCharge_complete_complement_profile

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
