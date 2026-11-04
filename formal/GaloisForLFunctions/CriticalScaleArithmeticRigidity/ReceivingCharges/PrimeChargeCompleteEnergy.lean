import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeBoundaryCorrection
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePolynomialScales

/-!
# Complete energy of coherent charge on polynomial horizons

At critical overlap every complete-form correction to the dilation energy
vanishes on the harmonic-neutral coherent family. The exact cofactor
boundary gives the exact energy at each fixed polynomial ratio of conductor
cutoff to horizon. Logarithmic physical normalization makes this energy vanish.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

private theorem charge_harmonic_neutral {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N) (t : ℝ) :
    ∑ n ∈ Icc 1 N,
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n / (n : ℝ) = 0 := by
  have h := (harmonicPrimeCharge_charge_and_adjunction hQ hN t).1
  simpa only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile, div_div,
    Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

private theorem harmonicMass_le_log (N : ℕ) : harmonicMass N ≤ Real.log N + 1 := by
  have h := harmonic_le_one_add_log N
  have heq : (harmonic N : ℝ) = harmonicMass N := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
  rw [heq] at h
  linarith only [h]

/-- The exact complete-form remainder on coherent charge is controlled by its reciprocal-prime moment. -/
theorem exists_harmonicPrimeCharge_complete_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q N : ℕ) (c t : ℝ),
      2 ≤ Q → 1 ≤ N → 1 ≤ c → c / N ≤ 1 / 3 →
      |completeWeilEnergy φ c N
          (packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N) -
        jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t))| ≤
        C * c ^ 3 * (Real.log N + 1) * (t / primePoleScale Q) ^ 2 *
          (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
            2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro Q N c t hQ hN hc hw
  let F := normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)
  let V := (t / primePoleScale Q) ^ 2 *
    (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ))
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * V := by
    have h := harmonicPrimeCharge_harmonic_square_le (by omega : 1 ≤ Q) hN t
    calc
      _ ≤ (t / primePoleScale Q) ^ 2 * harmonicMass N *
          (4 * (∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
            2 * ∑ p ∈ (Icc 1 Q).filter Nat.Prime, 1 / (p : ℝ)) := h
      _ = harmonicMass N * V := by dsimp only [V]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (harmonicMass_le_log N) hV
  have hO : (∑ n ∈ Icc 1 N, F n ^ 2) ≤ (N : ℝ) * V := by
    convert harmonicPrimeCharge_ordinary_square_le (by omega : 1 ≤ Q) hN t using 1
    dsimp only [V]
    ring
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have h := add_le_add (mul_le_mul_of_nonneg_left hH (mul_nonneg hA (sq_nonneg c)))
    (mul_le_mul_of_nonneg_left hO
      (show 0 ≤ B * c ^ 3 * (Real.log N + 1) / N by positivity))
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc23 hA)
      (mul_nonneg (by positivity : 0 ≤ Real.log N + 1) hV)
  refine (hbound c N hc hN hw F (charge_harmonic_neutral hQ hN t)).trans (h.trans ?_)
  calc
    _ ≤ A * c ^ 3 * ((Real.log N + 1) * V) +
        (B * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * V) := add_le_add h' le_rfl
    _ = _ := by
      dsimp only [V]
      field_simp [hN0.ne']

/-- At every fixed critical multiple, the full remainder vanishes on the cutoff charge family. -/
theorem tendsto_harmonicPrimeCharge_complete_sub_jump {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun N : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
        (packetVector (normalizedConductorPacket N (harmonicPrimeChargeCoefficients N N t)) N) -
      jumpEnergy N (normalizedConductorPacket N (harmonicPrimeChargeCoefficients N N t)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicPrimeCharge_complete_error_bound hφ hφ0 hsupp hM
  have hlim := (tendsto_primeChargeMoment_cost t (r := 3 / 8) (by norm_num)).const_mul
    (C * (2 * K) ^ 3)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, eventually_primeCharge_criticalOverlap_facts hK] with N hN hc
  have h := hbound N N (2 * K * Real.log N ^ (1 / 8 : ℝ)) t hN (by omega) hc.1 hc.2
  have hp : (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) = Real.log N ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg N)]
    norm_num
  rw [mul_pow, hp] at h
  simpa only [Real.norm_eq_abs, mul_assoc] using h

/-- The raw complete energy retains exactly half the squared receiving charge at the cutoff horizon. -/
theorem tendsto_harmonicPrimeCharge_complete_cutoff_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun N : ℕ => completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
      (packetVector (normalizedConductorPacket N (harmonicPrimeChargeCoefficients N N t)) N))
      atTop (𝓝 (t ^ 2 / 2)) := by
  have h := (tendsto_harmonicPrimeCharge_complete_sub_jump hφ hφ0 hsupp hM hK t).add
    (tendsto_harmonicPrimeCharge_cutoff_energy t)
  simpa only [sub_add_cancel, zero_add] using h

/-- The same coefficients in the logarithmically normalized physical horizon. -/
def harmonicPrimeChargeVector (Q N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ •
    packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N

/-- Physical normalization divides the literal complete form by the horizon logarithm. -/
theorem harmonicPrimeChargeVector_energy (φ : ℝ → ℝ) (c : ℝ) (Q N : ℕ) (t : ℝ) :
    completeWeilEnergy φ c N (harmonicPrimeChargeVector Q N t) =
      completeWeilEnergy φ c N
        (packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N) /
          Real.log N := by
  simp only [harmonicPrimeChargeVector, completeWeilEnergy, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  have hs : (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  calc
    _ = (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N),
        packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N⟫ := by ring
    _ = _ := by rw [hs]; ring

/-- Physical input uses exactly the same logarithmic normalization as its complete energy. -/
theorem harmonicPrimeChargeVector_norm_sq (Q N : ℕ) (t : ℝ) :
    ‖harmonicPrimeChargeVector Q N t‖ ^ 2 =
      ‖packetVector (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) N‖ ^ 2 /
        Real.log N := by
  rw [harmonicPrimeChargeVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- Even the raw input norm tends to zero at every fixed polynomial conductor ratio. -/
theorem tendsto_harmonicPrimeCharge_polynomial_input_norm_sq {a d : ℕ}
    (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (X ^ a)
        (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (X ^ d)‖ ^ 2) atTop (𝓝 0) := by
  have hlim := tendsto_primeChargePolynomialMoment_cost ha had t (r := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hQ : 1 ≤ X ^ a := Nat.one_le_pow a X (by omega)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), packetVector_norm_sq]
  have h := harmonicPrimeCharge_harmonic_square_le hQ hN t
  have hmass := mul_le_mul_of_nonneg_right (harmonicMass_le_log (X ^ d))
    (show 0 ≤ (t / primePoleScale (X ^ a)) ^ 2 *
      (4 * (∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
        2 * ∑ p ∈ (Icc 1 (X ^ a)).filter Nat.Prime, 1 / (p : ℝ)) by positivity)
  refine h.trans ?_
  convert hmass using 1 <;> ring

/-- Adjunction energy vanishes while the coefficients keep their exact generator charge. -/
theorem tendsto_harmonicPrimeCharge_polynomial_adjunction {a : ℕ}
    (ha : 0 < a) (d : ℕ) (t : ℝ) :
    Tendsto (fun X : ℕ => primeAdjunctionMass (X ^ a)
      (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hlim := (primePoleScale_tendsto_atTop.comp hXa).const_div_atTop (t ^ 2)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  exact (harmonicPrimeCharge_charge_and_adjunction
    (hX.trans (Nat.le_pow ha)) (Nat.one_le_pow d X (by omega)) t).2.2.symm

/-- The physical input norm vanishes at every fixed polynomial conductor ratio. -/
theorem tendsto_harmonicPrimeCharge_polynomial_physical_norm_sq {a d : ℕ}
    (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => ‖harmonicPrimeChargeVector (X ^ a) (X ^ d) t‖ ^ 2)
      atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  simpa only [harmonicPrimeChargeVector_norm_sq, Function.comp_def] using
    (tendsto_harmonicPrimeCharge_polynomial_input_norm_sq ha had t).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)

/-- Every fixed critical multiple erases the complete physical energy of the cutoff charge. -/
theorem tendsto_harmonicPrimeChargeVector_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun N : ℕ => completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
      (harmonicPrimeChargeVector N N t)) atTop (𝓝 0) := by
  simpa only [harmonicPrimeChargeVector_energy, Function.comp_def] using
    (tendsto_harmonicPrimeCharge_complete_cutoff_energy hφ hφ0 hsupp hM hK t).div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- At a fixed polynomial conductor ratio, all complete-form corrections vanish together. -/
theorem tendsto_harmonicPrimeCharge_polynomial_complete_sub_jump {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (X ^ a)
          (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (X ^ d)) -
      jumpEnergy (X ^ d) (normalizedConductorPacket (X ^ a)
        (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicPrimeCharge_complete_error_bound hφ hφ0 hsupp hM
  have hd : 0 < d := ha.trans_le had
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop := tendsto_pow_atTop hd.ne'
  have hlim := (tendsto_primeChargePolynomialMoment_cost ha had t
    (r := 3 / 8) (by norm_num)).const_mul (C * (2 * K) ^ 3)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2,
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hX hc
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have h := hbound (X ^ a) (X ^ d)
    (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) t hQ hN hc.1 hc.2
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  simpa only [Real.norm_eq_abs, mul_assoc] using h

/-- The full raw energy reads the conductor/horizon ratio and the negative half-charge boundary. -/
theorem tendsto_harmonicPrimeCharge_polynomial_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (X ^ a)
          (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (X ^ d)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  have h := (tendsto_harmonicPrimeCharge_polynomial_complete_sub_jump
    hφ hφ0 hsupp hM hK ha had t).add
      (tendsto_harmonicPrimeCharge_polynomial_dilation_energy ha had t)
  simpa only [sub_add_cancel, zero_add] using h

/-- Every fixed polynomial family has zero limiting complete physical energy and exact charge `t`. -/
theorem tendsto_harmonicPrimeCharge_polynomial_physical_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (harmonicPrimeChargeVector (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  simpa only [harmonicPrimeChargeVector_energy, Function.comp_def] using
    (tendsto_harmonicPrimeCharge_polynomial_complete_energy hφ hφ0 hsupp hM hK ha had t).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)

#print axioms exists_harmonicPrimeCharge_complete_error_bound
#print axioms tendsto_harmonicPrimeCharge_complete_cutoff_energy
#print axioms tendsto_harmonicPrimeChargeVector_complete_energy
#print axioms tendsto_harmonicPrimeCharge_polynomial_complete_energy
#print axioms tendsto_harmonicPrimeCharge_polynomial_physical_energy
#print axioms tendsto_harmonicPrimeCharge_polynomial_input_norm_sq
#print axioms tendsto_harmonicPrimeCharge_polynomial_adjunction

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
