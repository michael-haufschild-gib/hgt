import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeTailPairing
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeComplementReceiver
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMixedLimits

/-!
# A nonzero signed receiver in the exact conductor complement

At cutoff `X²` and horizon `X⁴⁰`, the complete form pairs the physical
coherent charge with a bounded complementary terminal contrast to `t/80`.
The same charge has vanishing complete physical energy and input norm.
The receiving term is the completed dilation tail; the full mixed remainder
vanishes without deleting any term of the complete form.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity CompletedArithmeticForms ArithmeticEffectivityTheory

/-- The completed coherent tail in physical horizon coordinates. -/
def primeChargeTailVector (Q N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => completedPrimeDilationTail Q
      (primeIncidenceCoefficients (fun _ => t / primePoleScale Q)) (N / n) n) N

/-- The physical tail and physical terminal contrast have the literal normalized harmonic pairing. -/
theorem primeChargeTailVector_inner_window (Q A B C N : ℕ) (t : ℝ) :
    ⟪primeChargeTailVector Q N t, primeChargeWindowVector A B C N⟫ =
      (∑ n ∈ Icc 1 N, completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / primePoleScale Q)) (N / n) n *
          primeChargeWindowContrast A B C n / (n : ℝ)) / Real.log N := by
  rw [primeChargeTailVector, primeChargeWindowVector,
    real_inner_smul_left, real_inner_smul_right, packetVector_inner]
  have hs : (Real.sqrt (Real.log (N : ℝ)))⁻¹ * (Real.sqrt (Real.log (N : ℝ)))⁻¹ =
      (Real.log N)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← mul_assoc, hs]
  ring

/-- The coherent receiving tail stays bounded in physical norm. -/
theorem primeChargeTailVector_norm_le {Q N : ℕ}
    (hB : 8 ≤ primePoleScale Q) (hL : 1 ≤ Real.log N) (t : ℝ) :
    ‖primeChargeTailVector Q N t‖ ≤ 3 * |t| := by
  have hB0 : 0 < primePoleScale Q := lt_of_lt_of_le (by norm_num) hB
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hact : primeActivityMass Q ≤ 2 * primePoleScale Q := by
    have h := primeActivityMass_le_primePoleScale_add_eight Q
    linarith only [h, hB]
  have hrow (n : ℕ) :
      |completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / primePoleScale Q)) (N / n) n| ≤ 2 * |t| := by
    have h := (abs_completedPrimeDilationTail_coherent_le_activity Q (N / n) n
      (t / primePoleScale Q)).trans (mul_le_mul_of_nonneg_left hact (abs_nonneg _))
    rw [abs_div, abs_of_pos hB0] at h
    exact h.trans_eq (by field_simp [hB0.ne'])
  have hmass : harmonicMass N ≤ 2 * Real.log N := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h, hL]
  have hsum : (∑ n ∈ Icc 1 N,
      completedPrimeDilationTail Q
        (primeIncidenceCoefficients (fun _ => t / primePoleScale Q)) (N / n) n ^ 2 / (n : ℝ)) ≤
      4 * t ^ 2 * harmonicMass N := by
    rw [harmonicMass, mul_sum]
    apply sum_le_sum
    intro n _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hrow n) 2
    rw [sq_abs, mul_pow, sq_abs] at h
    exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg n)).trans_eq (by ring)
  have hsq : ‖primeChargeTailVector Q N t‖ ^ 2 ≤ 8 * t ^ 2 := by
    rw [primeChargeTailVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq]
    calc
      _ ≤ (Real.log N)⁻¹ * (4 * t ^ 2 * harmonicMass N) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hL0.le)
      _ ≤ (Real.log N)⁻¹ * (4 * t ^ 2 * (2 * Real.log N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity))
          (inv_nonneg.mpr hL0.le)
      _ = _ := by field_simp [hL0.ne']; ring
  nlinarith only [hsq, sq_abs t, abs_nonneg t, norm_nonneg (primeChargeTailVector Q N t)]

/-- Projection of the contrast changes its tail pairing by a vanishing amount. -/
theorem tendsto_primeChargeTail_projection_pairing (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪primeChargeTailVector (X ^ 2) (X ^ 40) t,
        (conductorSubspace (X ^ 2) (X ^ 40)).starProjection
          (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))⟫)
      atTop (𝓝 0) := by
  have hQ : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hN : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hB := primePoleScale_tendsto_atTop.comp hQ
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hlim := tendsto_primeChargeTerminal_projection_norm.const_mul (3 * |t|)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hB.eventually (eventually_ge_atTop 8),
    hL.eventually (eventually_ge_atTop 1)] with X hb hl
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (primeChargeTailVector_norm_le hb hl t) (norm_nonneg _))

/-- The exact growing conductor complement reads a nonzero signed charge. -/
theorem tendsto_primeChargeTail_terminalReceiver_pairing (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪primeChargeTailVector (X ^ 2) (X ^ 40) t, primeChargeTerminalReceiver X⟫)
      atTop (𝓝 (t / 80)) := by
  have hwindow : Tendsto (fun X : ℕ =>
      ⟪primeChargeTailVector (X ^ 2) (X ^ 40) t,
        primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)⟫)
      atTop (𝓝 (t / 80)) := by
    simpa only [primeChargeTailVector_inner_window, Nat.reduceAdd, Nat.cast_ofNat,
      show (2 : ℝ) * (38 + 2) = 80 by norm_num] using
      tendsto_primeChargeTail_window_pairing (a := 38) (by omega) t
  simpa only [primeChargeTerminalReceiver, primeChargeWindowComplement, inner_sub_right, sub_zero] using
    hwindow.sub (tendsto_primeChargeTail_projection_pairing t)

/-- Packet coordinates of the exact complementary receiver. -/
def primeChargeTerminalProfile (X n : ℕ) : ℝ :=
  Real.sqrt n * primeHorizonExtension (primeChargeTerminalReceiver X) n

theorem packetVector_primeChargeTerminalProfile (X : ℕ) :
    packetVector (primeChargeTerminalProfile X) (X ^ 40) = primeChargeTerminalReceiver X :=
  packetVector_sqrt_extension _

theorem eventually_primeChargeTerminalProfile_neutral_unit :
    ∀ᶠ X : ℕ in atTop,
      (∑ n ∈ Icc 1 (X ^ 40), primeChargeTerminalProfile X n / (n : ℝ) = 0) ∧
        ‖packetVector (primeChargeTerminalProfile X) (X ^ 40)‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_primeChargeTerminalReceiver_norm_le_one] with X hX hnorm
  have hN : 2 ≤ X ^ 40 := hX.trans (Nat.le_pow (by omega : 0 < 40))
  have hQ : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X (by omega)
  refine ⟨harmonic_neutral_of_conductor_complement hQ hN _ ?_, ?_⟩
  · rw [packetVector_primeChargeTerminalProfile]
    exact primeChargeTerminalReceiver_mem X
  · simpa only [packetVector_primeChargeTerminalProfile] using hnorm

/-- On the exact receiver, the physically normalized dilation pairing is its completed tail. -/
theorem primeChargeTerminal_dilation_pairing {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    jumpPairing (X ^ 40)
      (normalizedConductorPacket (X ^ 2) (harmonicPrimeChargeCoefficients (X ^ 2) (X ^ 40) t))
      (primeChargeTerminalProfile X) / Real.sqrt (Real.log (X ^ 40 : ℕ)) =
        ⟪primeChargeTailVector (X ^ 2) (X ^ 40) t, primeChargeTerminalReceiver X⟫ := by
  have hN : 2 ≤ X ^ 40 := hX.trans (Nat.le_pow (by omega : 0 < 40))
  have hQ : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X (by omega)
  have hmem : packetVector (primeChargeTerminalProfile X) (X ^ 40) ∈
      (conductorSubspace (X ^ 2) (X ^ 40))ᗮ := by
    rw [packetVector_primeChargeTerminalProfile]
    exact primeChargeTerminalReceiver_mem X
  rw [harmonicPrimeCharge_complement_pairing hQ hN _ _ hmem,
    primeChargeTailVector, real_inner_smul_left,
    ← packetVector_primeChargeTerminalProfile, packetVector_inner]
  ring

/-- The full mixed remainder vanishes on the explicit complementary receiver. -/
theorem tendsto_primeChargeTerminal_complete_sub_dilation {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      (completePacketPairing φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (normalizedConductorPacket (X ^ 2) (harmonicPrimeChargeCoefficients (X ^ 2) (X ^ 40) t))
        (primeChargeTerminalProfile X) -
      jumpPairing (X ^ 40)
        (normalizedConductorPacket (X ^ 2) (harmonicPrimeChargeCoefficients (X ^ 2) (X ^ 40) t))
        (primeChargeTerminalProfile X)) / Real.sqrt (Real.log (X ^ 40 : ℕ))) atTop (𝓝 0) := by
  have hsq := tendsto_harmonicPrimeCharge_polynomial_mixed_error_sq
    hφ hφ0 hsupp hM hK (a := 2) (d := 40) (by omega) (by omega) t
    primeChargeTerminalProfile eventually_primeChargeTerminalProfile_neutral_unit
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [] with X
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The complete critical form retains the signed complement charge `t/80`. -/
theorem tendsto_harmonicPrimeCharge_complete_terminalReceiver {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t), primeChargeTerminalReceiver X⟫)
      atTop (𝓝 (t / 80)) := by
  have h := (tendsto_primeChargeTerminal_complete_sub_dilation hφ hφ0 hsupp hM hK t).add
    (tendsto_primeChargeTail_terminalReceiver_pairing t)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [← primeChargeTerminal_dilation_pairing hX,
    harmonicPrimeChargeVector, map_smul, real_inner_smul_left,
    ← packetVector_primeChargeTerminalProfile]
  unfold completePacketPairing
  ring

#print axioms primeChargeTailVector_norm_le
#print axioms tendsto_primeChargeTail_terminalReceiver_pairing
#print axioms tendsto_harmonicPrimeCharge_complete_terminalReceiver

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
