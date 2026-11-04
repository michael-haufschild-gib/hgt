import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries

/-!
# Receiving charge can survive complete operator cancellation

Choose the prime cutoff to make adjunction and physical input small, then
let the critical overlap grow past that fixed cutoff. The exact receiving
charge persists while the entire complete output tends to zero. Thus a
nonzero complementary residual is not forced by charge and small input alone.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis
  SelectiveMultiscaleArithmeticPositivity

/-- At fixed prime cutoff the complete critical operator annihilates the centered coherent packet. -/
theorem tendsto_fixedPrimeCharge_complete_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (Q : ℕ) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicPrimeChargeVector Q N t)‖) atTop (𝓝 0) :=
  tendsto_harmonicCentered_fixedPacket_complete_norm hc hR hcrit Q
    (primeOnly (fun p => (t / primePoleScale Q) * primePoleWitness p))

/-- Above its cutoff, the coherent physical input is bounded by its adjunction mass. -/
theorem harmonicPrimeChargeVector_sq_le_adjunction {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q ≤ N) (t : ℝ) :
    ‖harmonicPrimeChargeVector Q N t‖ ^ 2 ≤
      (26 / Real.log 2) * (t ^ 2 / primePoleScale Q) := by
  have h := harmonicCentered_prime_input_sq_le hQ hQN
    (fun p => (t / primePoleScale Q) * primePoleWitness p)
  rw [(normalizedPrimeCharge_response_and_energy hQ t).2] at h
  rw [harmonicPrimeChargeVector_norm_sq, packetVector_norm_sq]
  simpa only [conductorHorizonProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using h

/-- Exact charge and arbitrarily small input coexist with cancellation of the entire complete output. -/
theorem exists_primeCharge_complete_cancellation {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (Q₀ : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ 2 ≤ Q ∧ ∃ N₀ : ℕ, Q ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      harmonicSum N (conductorHorizonProfile Q (harmonicPrimeChargeCoefficients Q N t)) = 0 ∧
      packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeChargeCoefficients Q N t)) = t ∧
      primeAdjunctionMass Q (harmonicPrimeChargeCoefficients Q N t) < ε ∧
      ‖harmonicPrimeChargeVector Q N t‖ ^ 2 < ε ∧
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicPrimeChargeVector Q N t)‖ < ε ∧
      |completeWeilEnergy tiltedUnitSpline (c N) N (harmonicPrimeChargeVector Q N t)| < ε := by
  let u : ℝ := 26 / Real.log 2
  have hu : 0 ≤ u := div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  have hcost := (primePoleScale_tendsto_atTop.const_div_atTop (t ^ 2)).const_mul (1 + u)
  simp only [mul_zero] at hcost
  obtain ⟨Q, hQ₀, hQ, hsmall⟩ := ((eventually_ge_atTop Q₀).and
    ((eventually_ge_atTop 2).and (hcost.eventually (gt_mem_nhds hε)))).exists
  have hJ0 : 0 ≤ t ^ 2 / primePoleScale Q := div_nonneg (sq_nonneg _) (primePoleScale_pos hQ).le
  have hJ : t ^ 2 / primePoleScale Q < ε := by
    nlinarith only [hsmall, mul_nonneg hu hJ0]
  have hinput : u * (t ^ 2 / primePoleScale Q) < ε := by
    nlinarith only [hsmall, hJ0]
  have hδ : 0 < ε / (ε + 1) := div_pos hε (by positivity)
  have hδle : ε / (ε + 1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < ε + 1)).mpr
    nlinarith only [sq_nonneg ε]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_fixedPrimeCharge_complete_norm hc hR hcrit Q t).eventually (gt_mem_nhds hδ))
  refine ⟨Q, hQ₀, hQ, max Q N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hQN := (le_max_left Q N₀).trans hN
  have hN1 : 1 ≤ N := by omega
  have hcharge := harmonicPrimeCharge_charge_and_adjunction hQ hN1 t
  have hin := (harmonicPrimeChargeVector_sq_le_adjunction hQ hQN t).trans_lt hinput
  have hout := hN₀ N ((le_max_right Q N₀).trans hN)
  refine ⟨hcharge.1, hcharge.2.1, hcharge.2.2.trans_lt hJ, hin, hout.trans_le hδle, ?_⟩
  have hv : ‖harmonicPrimeChargeVector Q N t‖ ≤ ε + 1 := by
    nlinarith only [hin, sq_nonneg (‖harmonicPrimeChargeVector Q N t‖ - 1 / 2)]
  calc
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicPrimeChargeVector Q N t)‖ * ‖harmonicPrimeChargeVector Q N t‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicPrimeChargeVector Q N t)‖ * (ε + 1) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ < (ε / (ε + 1)) * (ε + 1) := mul_lt_mul_of_pos_right hout (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

/-- The cancellation regime is realized by the explicit canonical critical curve. -/
theorem exists_canonical_primeCharge_complete_cancellation {R : ℝ} (hR : 0 < R)
    (Q₀ : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ 2 ≤ Q ∧ ∃ N₀ : ℕ, Q ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      harmonicSum N (conductorHorizonProfile Q (harmonicPrimeChargeCoefficients Q N t)) = 0 ∧
      packetMean Q (arithmeticPrimeGenerator Q (harmonicPrimeChargeCoefficients Q N t)) = t ∧
      primeAdjunctionMass Q (harmonicPrimeChargeCoefficients Q N t) < ε ∧
      ‖harmonicPrimeChargeVector Q N t‖ ^ 2 < ε ∧
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (canonicalCriticalCurve R N) N)
        (harmonicPrimeChargeVector Q N t)‖ < ε ∧
      |completeWeilEnergy tiltedUnitSpline (canonicalCriticalCurve R N) N
        (harmonicPrimeChargeVector Q N t)| < ε :=
  exists_primeCharge_complete_cancellation (one_le_canonicalCriticalCurve R) hR
    (tendsto_canonicalCriticalCurve_pow_eight hR) Q₀ t hε

#print axioms tendsto_fixedPrimeCharge_complete_norm
#print axioms exists_primeCharge_complete_cancellation
#print axioms exists_canonical_primeCharge_complete_cancellation

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
