import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeDilationScales
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments

/-!
# The complete critical form on a fixed receiving fibre

Global harmonic centering preserves the exact conductor receiving charge.
The ordinary and harmonic fibre moments make the entire complete-form
remainder vanish at every fixed polynomial conductor/horizon ratio.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity ArithmeticIntersectionTheory

/-- Exact global pole neutrality and exact receiving charge hold on the same fibre coefficients. -/
theorem harmonicFibreCharge_charge {m Q N : ℕ}
    (hm : 0 < m) (hQ : 1 ≤ Q) (hN : 1 ≤ N) (t : ℝ) (hB : 0 < fibreScale m Q) :
    (∑ n ∈ Icc 1 N,
      normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n / (n : ℝ)) = 0 ∧
    packetMean (m * Q) (fun n =>
      arithmeticPrimeGenerator (m * Q) (harmonicFibreChargeCoefficients m Q N t) n *
        normalizedRamanujanMode m n) = t ∧
    primeAdjunctionMass (m * Q) (harmonicFibreChargeCoefficients m Q N t) ≤
      (2 * (Real.log m + tameDifferent m) + 1) * (t ^ 2 / fibreScale m Q) := by
  have hmQ : 1 ≤ m * Q := Nat.mul_pos hm hQ
  constructor
  · have h := harmonicSum_centeredCoefficients hmQ hN (fibreCoefficients m Q (fibreCharge m Q t))
    simpa only [harmonicFibreChargeCoefficients, SelectiveMultiscaleArithmeticPositivity.harmonicSum,
      conductorHorizonProfile, div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h
  constructor
  · simp only [harmonicFibreChargeCoefficients, arithmeticPrimeGenerator_harmonicCentered]
    exact packetMean_fibre_retains hm hQ t hB.ne'
  · rw [harmonicFibreChargeCoefficients, primeAdjunctionMass_harmonicCentered]
    exact primeAdjunctionMass_fibreCharge hm t hB

private theorem fibre_harmonicMass_le_log (N : ℕ) : harmonicMass N ≤ Real.log N + 1 := by
  have h := harmonic_le_one_add_log N
  have he : (harmonic N : ℝ) = harmonicMass N := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
  rw [he] at h
  linarith only [h]

/-- One atom-dependent constant controls every fixed-fibre complete remainder by its exact moments. -/
theorem exists_harmonicFibreCharge_complete_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m Q N : ℕ) (c t : ℝ),
      0 < m → 1 ≤ Q → 1 ≤ N → 0 < fibreScale m Q → 1 ≤ c → c / N ≤ 1 / 3 →
      |completeWeilEnergy φ c N
          (packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N) -
        jumpEnergy N (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t))| ≤
          C * c ^ 3 * (Real.log N + 1) * fibreChargeMoment m Q t := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  refine ⟨A + 4 * B, by positivity, ?_⟩
  intro m Q N c t hm hQ hN hb hc hw
  let F := normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)
  have hV := fibreChargeMoment_nonneg m Q t
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  obtain ⟨hO, hH⟩ := harmonicFibreCharge_moments hm hQ hN t
  have hH' := hH.trans (mul_le_mul_of_nonneg_right (fibre_harmonicMass_le_log N) hV)
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have h := hbound c N hc hN hw F (harmonicFibreCharge_charge hm hQ hN t hb).1
  calc
    _ ≤ A * c ^ 2 * ((Real.log N + 1) * fibreChargeMoment m Q t) +
        (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * fibreChargeMoment m Q t) :=
      h.trans (add_le_add (mul_le_mul_of_nonneg_left hH' (by positivity))
        (mul_le_mul_of_nonneg_left hO (by positivity)))
    _ ≤ A * c ^ 3 * ((Real.log N + 1) * fibreChargeMoment m Q t) +
        (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * fibreChargeMoment m Q t) :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc23 hA)
        (by positivity)) le_rfl
    _ = _ := by field_simp [hN0.ne']

/-- Every complete-form correction vanishes on a fixed coprime fibre at critical overlap. -/
theorem tendsto_harmonicFibreCharge_complete_sub_jump {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (m * X ^ a)
          (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) (X ^ d)) -
      jumpEnergy (X ^ d) (normalizedConductorPacket (m * X ^ a)
        (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonicFibreCharge_complete_error_bound hφ hφ0 hsupp hM
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hlim := (tendsto_fibreChargePolynomialMoment_cost hm ha had t
    (r := 3 / 8) (by norm_num)).const_mul (C * (2 * K) ^ 3)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hB.eventually (eventually_ge_atTop 1),
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hX hb hc
  have hQ : 1 ≤ X ^ a := Nat.one_le_pow a X (by omega)
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X (by omega)
  have h := hbound m (X ^ a) (X ^ d)
    (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) t hm hQ hN
    (zero_lt_one.trans_le hb) hc.1 hc.2
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  simpa only [Real.norm_eq_abs, mul_assoc] using h

/-- Even the raw harmonic fibre input tends to zero at fixed polynomial scales. -/
theorem tendsto_harmonicFibreCharge_input_norm_sq {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (m * X ^ a)
        (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) (X ^ d)‖ ^ 2)
      atTop (𝓝 0) := by
  have hlim := tendsto_fibreChargePolynomialMoment_cost hm ha had t (r := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), packetVector_norm_sq]
  exact (harmonicFibreCharge_moments hm
    (Nat.one_le_pow a X (by omega)) (Nat.one_le_pow d X (by omega)) t).2.trans
      (mul_le_mul_of_nonneg_right (fibre_harmonicMass_le_log (X ^ d))
        (fibreChargeMoment_nonneg _ _ _))

/-- The complete raw energy has the same exact limit on every fixed coprime fibre. -/
theorem tendsto_harmonicFibreCharge_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (m * X ^ a)
          (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) (X ^ d)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  have h := (tendsto_harmonicFibreCharge_complete_sub_jump
    hφ hφ0 hsupp hM hK hm ha had t).add
      (tendsto_harmonicFibreCharge_dilation_energy hm ha had t)
  simpa only [sub_add_cancel, zero_add] using h

/-- A harmonic-neutral receiving fibre in the logarithmically normalized physical horizon. -/
def harmonicFibreChargeVector (m Q N : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ •
    packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N

theorem harmonicFibreChargeVector_energy (φ : ℝ → ℝ) (c : ℝ) (m Q N : ℕ) (t : ℝ) :
    completeWeilEnergy φ c N (harmonicFibreChargeVector m Q N t) =
      completeWeilEnergy φ c N
        (packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N) /
          Real.log N := by
  simp only [harmonicFibreChargeVector, completeWeilEnergy, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  have hs : (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  calc
    _ = (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
        (packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N),
        packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N⟫ := by ring
    _ = _ := by rw [hs]; ring

theorem harmonicFibreChargeVector_norm_sq (m Q N : ℕ) (t : ℝ) :
    ‖harmonicFibreChargeVector m Q N t‖ ^ 2 =
      ‖packetVector (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) N‖ ^ 2 /
        Real.log N := by
  rw [harmonicFibreChargeVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- The physical complete energy vanishes despite the exact receiving charge on each fibre. -/
theorem tendsto_harmonicFibreCharge_physical_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (harmonicFibreChargeVector m (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  simpa only [harmonicFibreChargeVector_energy, Function.comp_def] using
    (tendsto_harmonicFibreCharge_complete_energy hφ hφ0 hsupp hM hK hm ha had t).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)

theorem tendsto_harmonicFibreCharge_physical_norm_sq {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => ‖harmonicFibreChargeVector m (X ^ a) (X ^ d) t‖ ^ 2)
      atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  simpa only [harmonicFibreChargeVector_norm_sq, Function.comp_def] using
    (tendsto_harmonicFibreCharge_input_norm_sq hm ha had t).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)

/-- Each fixed receiving mode keeps its charge while its adjunction energy tends to zero. -/
theorem tendsto_harmonicFibreCharge_adjunction {m : ℕ} (hm : 0 < m)
    {a : ℕ} (ha : 0 < a) (d : ℕ) (t : ℝ) :
    Tendsto (fun X : ℕ => primeAdjunctionMass (m * X ^ a)
      (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hlim := (hB.const_div_atTop (t ^ 2)).const_mul
    (2 * (Real.log m + tameDifferent m) + 1)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1, hB.eventually (eventually_gt_atTop 0)] with X hX hb
  rw [Real.norm_eq_abs, abs_of_nonneg (primeAdjunctionMass_nonneg _ _)]
  exact (harmonicFibreCharge_charge hm (Nat.one_le_pow a X hX)
    (Nat.one_le_pow d X hX) t hb).2.2

#print axioms harmonicFibreCharge_charge
#print axioms tendsto_harmonicFibreCharge_complete_sub_jump
#print axioms tendsto_harmonicFibreCharge_input_norm_sq
#print axioms tendsto_harmonicFibreCharge_complete_energy
#print axioms tendsto_harmonicFibreCharge_physical_energy
#print axioms tendsto_harmonicFibreCharge_adjunction

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
