import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMixedMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy

/-!
# Uniform complete-form comparison against neutral receivers

The complete-form remainder on a coherent charge is small against every
unit harmonic-neutral receiver, including vectors in a growing conductor
complement. Polarization costs six powers of overlap; the critical exponent
still leaves a strictly sublogarithmic moment cost.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- The full mixed remainder, divided by the physical horizon logarithm, has one moment cost. -/
theorem exists_harmonicPrimeCharge_mixed_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q N : ℕ) (c t : ℝ),
      2 ≤ Q → 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      ∀ G : ℕ → ℝ, (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) →
      ‖packetVector G N‖ ≤ 1 →
      (completePacketPairing φ c N
          (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) G -
        jumpPairing N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) G) ^ 2 /
          Real.log N ≤
        C * c ^ 6 * (Real.log N + 1) * (t / primePoleScale Q) ^ 2 *
          (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
            2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_mixed_moment_bound hφ hφ0 hsupp hM
  refine ⟨2 * (1 + A + B) * (A + B), by positivity, ?_⟩
  intro Q N c t hQ hN hL hc hw G hG hunit
  let F := normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)
  let V := (t / primePoleScale Q) ^ 2 *
    (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ))
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0 := by
    have h := (harmonicPrimeCharge_charge_and_adjunction hQ hN t).1
    simpa only [F, SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile, div_div,
      Real.mul_self_sqrt (Nat.cast_nonneg _)] using h
  have hmass : harmonicMass N ≤ Real.log N + 1 := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h]
  have hH : (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * V := by
    calc
      _ ≤ harmonicMass N * V := by
        convert harmonicPrimeCharge_harmonic_square_le (by omega : 1 ≤ Q) hN t using 1
        dsimp only [V]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hV
  have hO : (∑ n ∈ Icc 1 N, F n ^ 2) ≤ (N : ℝ) * V := by
    convert harmonicPrimeCharge_ordinary_square_le (by omega : 1 ≤ Q) hN t using 1
    dsimp only [V]
    ring
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have hc3 : 1 ≤ c ^ 3 := (show 1 ≤ c ^ 2 by nlinarith only [hc]).trans hc23
  have hweight : 1 ≤ c ^ 3 * (Real.log N + 1) := by
    have h := mul_le_mul hc3 (show 1 ≤ Real.log N + 1 by linarith only [hL])
      zero_le_one (by positivity : 0 ≤ c ^ 3)
    simpa only [one_mul] using h
  have hcost : A * c ^ 2 * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
      (B * c ^ 3 * (Real.log N + 1) / N) * ∑ n ∈ Icc 1 N, F n ^ 2 ≤
        (A + B) * c ^ 3 * (Real.log N + 1) * V := by
    calc
      _ ≤ A * c ^ 2 * ((Real.log N + 1) * V) +
          (B * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * V) :=
        add_le_add (mul_le_mul_of_nonneg_left hH (by positivity))
          (mul_le_mul_of_nonneg_left hO (by positivity))
      _ ≤ A * c ^ 3 * ((Real.log N + 1) * V) +
          (B * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * V) :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc23 hA) (by positivity)) le_rfl
      _ = _ := by field_simp [hN0.ne']
  have hfactor : 1 + A * c ^ 2 + B * c ^ 3 * (Real.log N + 1) ≤
      (1 + A + B) * c ^ 3 * (Real.log N + 1) := by
    have hAterm : A * c ^ 2 ≤ A * c ^ 3 * (Real.log N + 1) := by
      calc
        _ ≤ A * c ^ 3 := mul_le_mul_of_nonneg_left hc23 hA
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith only [hL])
    nlinarith only [hweight, hAterm]
  have h := (hbound c N hc hN hw F G hF hG hunit).trans
    (mul_le_mul hfactor hcost (by positivity) (by positivity))
  have hratio : (Real.log N + 1) ^ 2 / Real.log N ≤ 2 * (Real.log N + 1) := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hL, sq_nonneg (Real.log N - 1)]
  refine (div_le_div_of_nonneg_right h hL0.le).trans ?_
  calc
    _ = (1 + A + B) * (A + B) * c ^ 6 * V *
        ((Real.log N + 1) ^ 2 / Real.log N) := by ring
    _ ≤ (1 + A + B) * (A + B) * c ^ 6 * V * (2 * (Real.log N + 1)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [V]; ring

/-- At critical overlap, normalized mixed errors vanish uniformly on unit neutral receivers. -/
theorem tendsto_harmonicPrimeCharge_polynomial_mixed_error_sq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d)
    (t : ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ᶠ X in atTop,
      (∑ n ∈ Icc 1 (X ^ d), G X n / (n : ℝ) = 0) ∧ ‖packetVector (G X) (X ^ d)‖ ≤ 1) :
    Tendsto (fun X : ℕ =>
      (completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
          (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
          (G X) -
        jumpPairing (X ^ d)
          (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
          (G X)) ^ 2 / Real.log (X ^ d : ℕ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicPrimeCharge_mixed_error_bound hφ hφ0 hsupp hM
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd
  have hlim := (tendsto_primeChargePolynomialMoment_cost ha had t
    (r := 3 / 4) (by norm_num)).const_mul (C * (2 * K) ^ 6)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 1),
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK), hG] with X hX hL hc hg
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have h := hbound (X ^ a) (X ^ d)
    (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) t hQ hN hL hc.1 hc.2 (G X) hg.1 hg.2
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (6 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [mul_assoc] using h

#print axioms exists_harmonicPrimeCharge_mixed_error_bound
#print axioms tendsto_harmonicPrimeCharge_polynomial_mixed_error_sq

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
