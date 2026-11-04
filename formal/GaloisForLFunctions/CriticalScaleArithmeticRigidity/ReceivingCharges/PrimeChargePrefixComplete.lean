import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePrefixPairing
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMomentCosts

/-!
# The complete prime-prefix charge kernel

The full bilinear remainder vanishes when both inputs are coherent prime
prefixes. Their complete critical pairing is therefore the exact nested
prime-incidence kernel, with its cofactor boundary correction retained.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

private def prefixMoment (Q : ℕ) (t : ℝ) : ℝ :=
  (t / primePoleScale Q) ^ 2 *
    (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ))

private theorem prefixMoment_nonneg (Q : ℕ) (t : ℝ) : 0 ≤ prefixMoment Q t := by
  unfold prefixMoment
  positivity

private theorem prefix_moments {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n / (n : ℝ)) = 0 ∧
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n ^ 2 / (n : ℝ)) ≤
      (Real.log N + 1) * prefixMoment Q t ∧
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n ^ 2) ≤
      4 * (N : ℝ) * prefixMoment Q t := by
  have hneutral := (harmonicPrimeCharge_charge_and_adjunction hQ hN t).1
  have hH : harmonicMass N ≤ Real.log N + 1 := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
      div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)] using hneutral
  · have h := harmonicPrimeCharge_harmonic_square_le (by omega : 1 ≤ Q) hN t
    refine h.trans ?_
    convert mul_le_mul_of_nonneg_right hH (prefixMoment_nonneg Q t) using 1
    dsimp only [prefixMoment]
    ring
  · have h := harmonicPrimeCharge_ordinary_square_le (by omega : 1 ≤ Q) hN t
    have h' : (N : ℝ) * prefixMoment Q t ≤ 4 * (N : ℝ) * prefixMoment Q t := by
      have h0 := mul_nonneg (Nat.cast_nonneg N) (prefixMoment_nonneg Q t)
      nlinarith only [h0]
    exact (h.trans_eq (show _ = (N : ℝ) * prefixMoment Q t by
      dsimp only [prefixMoment]
      ring)).trans h'

/-- Two coherent prefixes have a vanishing unnormalized complete mixed remainder. -/
theorem tendsto_primePrefixes_complete_sub_dilation {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a b d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ d) (hbd : b ≤ d) (t u : ℝ) :
    Tendsto (fun X : ℕ =>
      completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
        (normalizedConductorPacket (X ^ b) (harmonicPrimeChargeCoefficients (X ^ b) (X ^ d) u)) -
      jumpPairing (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
        (normalizedConductorPacket (X ^ b) (harmonicPrimeChargeCoefficients (X ^ b) (X ^ d) u)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_complete_packet_bilinear_moment_cost hφ hφ0 hsupp hM
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hlim := ((tendsto_primeChargePolynomialMoment_cost ha had t
      (r := 3 / 8) (by norm_num)).add
    (tendsto_primeChargePolynomialMoment_cost hb hbd u (r := 3 / 8) (by norm_num))).const_mul
      (C * (2 * K) ^ 3)
  simp only [zero_add, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2,
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hX hc
  have hQa : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hQb : 2 ≤ X ^ b := hX.trans (Nat.le_pow hb)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have hma := prefix_moments hQa hN t
  have hmb := prefix_moments hQb hN u
  have h := hbound (X ^ d) (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ))
    (prefixMoment (X ^ a) t) (prefixMoment (X ^ b) u) hN hc.1 hc.2
    (prefixMoment_nonneg _ _) (prefixMoment_nonneg _ _) _ _ hma.1 hmb.1
      hma.2.1 hmb.2.1 hma.2.2 hmb.2.2
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by dsimp only [prefixMoment]; ring)

/-- The literal complete form has the nested prime-prefix kernel at every critical multiple. -/
theorem tendsto_harmonicPrimeCharge_complete_prefix_pairing {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a b d : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbd : b ≤ d) (t u : ℝ) :
    Tendsto (fun X : ℕ =>
      completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
        (normalizedConductorPacket (X ^ b) (harmonicPrimeChargeCoefficients (X ^ b) (X ^ d) u)))
      atTop (𝓝 ((t * u) * ((d : ℝ) / b - (a : ℝ) / (2 * b)))) := by
  have h := (tendsto_primePrefixes_complete_sub_dilation hφ hφ0 hsupp hM hK
    ha (ha.trans_le hab) (hab.trans hbd) hbd t u).add
      (tendsto_harmonicPrimeCharge_prefix_pairing ha hab hbd t u)
  simpa only [sub_add_cancel, zero_add] using h

#print axioms tendsto_harmonicPrimeCharge_complete_prefix_pairing

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
