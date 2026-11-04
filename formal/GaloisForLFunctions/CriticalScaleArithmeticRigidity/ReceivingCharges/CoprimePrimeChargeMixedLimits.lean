import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMomentCosts
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeCompleteEnergy

/-!
# Complete mixed remainders in fixed receiving fibres

The reciprocal-prime moment gain survives multiplication by a fixed mode.
It makes the physically normalized complete remainder vanish against every
unit harmonic-neutral receiver at each fixed polynomial cutoff/horizon ratio.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- One complete mixed-moment bound applies uniformly to every fixed receiving fibre. -/
theorem exists_harmonicFibreCharge_mixed_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m Q N : ℕ) (c t : ℝ),
      0 < m → 1 ≤ Q → 1 ≤ N → 0 < fibreScale m Q →
      1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      ∀ G : ℕ → ℝ, (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) →
      ‖packetVector G N‖ ≤ 1 →
      (completePacketPairing φ c N
          (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) G -
        jumpPairing N
          (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) G) ^ 2 /
          Real.log N ≤ C * c ^ 6 * (Real.log N + 1) * fibreChargeMoment m Q t := by
  obtain ⟨C, hC, hbound⟩ := exists_complete_packet_normalized_moment_cost hφ hφ0 hsupp hM
  refine ⟨C, hC, ?_⟩
  intro m Q N c t hm hQ hN hb hL hc hw G hG hunit
  obtain ⟨hO, hH⟩ := harmonicFibreCharge_moments hm hQ hN t
  have hmass : harmonicMass N ≤ Real.log N + 1 := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h]
  exact hbound N c (fibreChargeMoment m Q t) hN hL hc hw
    (fibreChargeMoment_nonneg _ _ _) _ G (harmonicFibreCharge_charge hm hQ hN t hb).1
    hG hunit (hH.trans (mul_le_mul_of_nonneg_right hmass (fibreChargeMoment_nonneg _ _ _))) hO

/-- At critical overlap every fixed receiving fibre has vanishing normalized mixed remainder. -/
theorem tendsto_harmonicFibreCharge_mixed_error_sq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ᶠ X in atTop,
      (∑ n ∈ Icc 1 (X ^ d), G X n / (n : ℝ) = 0) ∧ ‖packetVector (G X) (X ^ d)‖ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
          (normalizedConductorPacket (m * X ^ a)
            (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) (G X) -
        jumpPairing (X ^ d)
          (normalizedConductorPacket (m * X ^ a)
            (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) (G X)) ^ 2 /
          Real.log (X ^ d : ℕ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicFibreCharge_mixed_error_bound hφ hφ0 hsupp hM
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd
  have hlim := (tendsto_fibreChargePolynomialMoment_cost hm ha had t
    (r := 3 / 4) (by norm_num)).const_mul (C * (2 * K) ^ 6)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hB.eventually (eventually_ge_atTop 1),
    hlog.eventually (eventually_ge_atTop 1),
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK), hG] with X hX hb hL hc hg
  have hQ : 1 ≤ X ^ a := Nat.one_le_pow a X (by omega)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have h := hbound m (X ^ a) (X ^ d)
    (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) t hm hQ hN
    (zero_lt_one.trans_le hb) hL hc.1 hc.2 (G X) hg.1 hg.2
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (6 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [mul_assoc] using h

#print axioms exists_harmonicFibreCharge_mixed_error_bound
#print axioms tendsto_harmonicFibreCharge_mixed_error_sq

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
