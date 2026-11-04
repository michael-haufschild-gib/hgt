import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeCompleteEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries

/-!
# Complete operator cancellation on every fixed receiving fibre

First choose a coprime prime cutoff with small adjunction and physical
input. Increasing the horizon then sends the entire complete output to
zero, while the exact prescribed receiving coordinate remains unchanged.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis
  SelectiveMultiscaleArithmeticPositivity

/-- Fixed coprime prime cutoffs disappear from the full critical operator in every base mode. -/
theorem tendsto_fixedFibreCharge_complete_norm {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (m Q : ℕ) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicFibreChargeVector m Q N t)‖) atTop (𝓝 0) :=
  tendsto_harmonicCentered_fixedPacket_complete_norm hc hR hcrit (m * Q)
    (fibreCoefficients m Q (fibreCharge m Q t))

/-- Every receiving coordinate can persist with arbitrarily small complete output and input. -/
theorem exists_fibreCharge_complete_cancellation {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m : ℕ} (hm : 0 < m) (Q₀ : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ 2 ≤ Q ∧ ∃ N₀ : ℕ, m * Q ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      harmonicSum N (conductorHorizonProfile (m * Q) (harmonicFibreChargeCoefficients m Q N t)) = 0 ∧
      packetMean (m * Q) (fun n =>
        arithmeticPrimeGenerator (m * Q) (harmonicFibreChargeCoefficients m Q N t) n *
          normalizedRamanujanMode m n) = t ∧
      primeAdjunctionMass (m * Q) (harmonicFibreChargeCoefficients m Q N t) < ε ∧
      ‖harmonicFibreChargeVector m Q N t‖ ^ 2 < ε ∧
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicFibreChargeVector m Q N t)‖ < ε ∧
      |completeWeilEnergy tiltedUnitSpline (c N) N (harmonicFibreChargeVector m Q N t)| < ε := by
  have hB := fibreScale_tendsto_atTop hm
  have hcost := (hB.const_div_atTop (t ^ 2)).const_mul (fibreConstant m)
  simp only [mul_zero] at hcost
  obtain ⟨Q, hQ₀, hQ, hb, hsmall⟩ := ((eventually_ge_atTop Q₀).and
    ((eventually_ge_atTop 2).and ((hB.eventually_gt_atTop 0).and
      (hcost.eventually (gt_mem_nhds hε))))).exists
  have hδ : 0 < ε / (ε + 1) := div_pos hε (by positivity)
  have hδle : ε / (ε + 1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < ε + 1)).mpr
    nlinarith only [sq_nonneg ε]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_fixedFibreCharge_complete_norm hc hR hcrit m Q t).eventually (gt_mem_nhds hδ))
  refine ⟨Q, hQ₀, hQ, max (m * Q) N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hQN := (le_max_left (m * Q) N₀).trans hN
  obtain ⟨-, hzero, hadj, hcharge, -, hinput, -⟩ := fibreCharge_bounds hm hQ hQN t hb
  have hin : ‖harmonicFibreChargeVector m Q N t‖ ^ 2 < ε := by
    rw [harmonicFibreChargeVector_norm_sq, packetVector_norm_sq]
    have h := hinput.trans_lt hsmall
    simpa only [conductorHorizonProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using h
  have hout := hN₀ N ((le_max_right (m * Q) N₀).trans hN)
  refine ⟨hzero, hcharge, hadj.trans_lt hsmall, hin, hout.trans_le hδle, ?_⟩
  have hv : ‖harmonicFibreChargeVector m Q N t‖ ≤ ε + 1 := by
    nlinarith only [hin, sq_nonneg (‖harmonicFibreChargeVector m Q N t‖ - 1 / 2)]
  calc
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicFibreChargeVector m Q N t)‖ * ‖harmonicFibreChargeVector m Q N t‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (harmonicFibreChargeVector m Q N t)‖ * (ε + 1) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ < (ε / (ε + 1)) * (ε + 1) := mul_lt_mul_of_pos_right hout (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

/-- The simultaneous small-cost and complete-cancellation conclusion has an explicit critical clock. -/
theorem exists_canonical_fibreCharge_complete_cancellation {R : ℝ} (hR : 0 < R)
    {m : ℕ} (hm : 0 < m) (Q₀ : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ 2 ≤ Q ∧ ∃ N₀ : ℕ, m * Q ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      harmonicSum N (conductorHorizonProfile (m * Q) (harmonicFibreChargeCoefficients m Q N t)) = 0 ∧
      packetMean (m * Q) (fun n =>
        arithmeticPrimeGenerator (m * Q) (harmonicFibreChargeCoefficients m Q N t) n *
          normalizedRamanujanMode m n) = t ∧
      primeAdjunctionMass (m * Q) (harmonicFibreChargeCoefficients m Q N t) < ε ∧
      ‖harmonicFibreChargeVector m Q N t‖ ^ 2 < ε ∧
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (canonicalCriticalCurve R N) N)
        (harmonicFibreChargeVector m Q N t)‖ < ε ∧
      |completeWeilEnergy tiltedUnitSpline (canonicalCriticalCurve R N) N
        (harmonicFibreChargeVector m Q N t)| < ε :=
  exists_fibreCharge_complete_cancellation (one_le_canonicalCriticalCurve R) hR
    (tendsto_canonicalCriticalCurve_pow_eight hR) hm Q₀ t hε

#print axioms tendsto_fixedFibreCharge_complete_norm
#print axioms exists_fibreCharge_complete_cancellation
#print axioms exists_canonical_fibreCharge_complete_cancellation

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
