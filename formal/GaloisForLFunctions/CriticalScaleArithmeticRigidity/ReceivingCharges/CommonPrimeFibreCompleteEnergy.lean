import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreDilation
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMomentCosts

/-!
# Complete critical energy of a prescribed finite receiving vector

The finite period Gram is the Euclidean Gram of the receiving coordinates.
The common incidence moments make every complete-form correction vanish,
including the global pole, shell and archimedean terms.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

private theorem common_harmonicMass_le_log (N : ℕ) : harmonicMass N ≤ Real.log N + 1 := by
  have h := harmonic_le_one_add_log N
  have he : (harmonic N : ℝ) = harmonicMass N := by
    simpa only [harmonicMass, one_div] using
      _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
  rw [he] at h
  linarith only [h]

/-- Harmonic pole removal leaves the finite receiving-vector dilation energy unchanged. -/
theorem commonPrimeFibre_jumpEnergy {M Q : ℕ} (hM : 0 < M) (hQ : 1 ≤ Q)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (N : ℕ) (t : ℕ → ℝ) :
    jumpEnergy N (normalizedConductorPacket (M * Q) (commonPrimeFibreCoefficients S M Q N t)) =
      jumpEnergy N (commonPrimeFibreProfile S M Q t) := by
  rw [funext (commonPrimeFibre_packet_formula hM hQ S hS N t), jumpEnergy_sub_const]

/-- All corrections of the literal complete form vanish on a finite prescribed receiving vector. -/
theorem tendsto_commonPrimeFibre_complete_sub_jump {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (M * X ^ a)
          (commonPrimeFibreCoefficients S M (X ^ a) (X ^ d) t)) (X ^ d)) -
        jumpEnergy (X ^ d) (commonPrimeFibreProfile S M (X ^ a) t)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_complete_packet_bilinear_moment_cost hφ hφ0 hsupp hφM
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  have hlim := (tendsto_commonPrimeFibreMoment_cost hM S t ha had
    (r := 3 / 8) (by norm_num)).const_mul (2 * C * (2 * K) ^ 3)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1,
    hNd.eventually (eventually_primeCharge_criticalOverlap_facts hK)] with X hX hc
  have hQ : 1 ≤ X ^ a := Nat.one_le_pow a X hX
  have hN : 1 ≤ X ^ d := Nat.one_le_pow d X hX
  let F := normalizedConductorPacket (M * X ^ a)
    (commonPrimeFibreCoefficients S M (X ^ a) (X ^ d) t)
  have hzero : ∑ n ∈ Icc 1 (X ^ d), F n / (n : ℝ) = 0 := by
    simpa only [SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile, div_div,
      Real.mul_self_sqrt (Nat.cast_nonneg _)] using commonPrimeFibre_neutral hM hQ hN S t
  obtain ⟨hO, hH⟩ := commonPrimeFibre_centered_moments hM hQ hN S hS t
  have hH' := hH.trans (mul_le_mul_of_nonneg_right (common_harmonicMass_le_log (X ^ d))
    (commonPrimeFibreMoment_nonneg S M (X ^ a) t))
  have h := hbound (X ^ d) (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ))
    (commonPrimeFibreMoment S M (X ^ a) t) (commonPrimeFibreMoment S M (X ^ a) t)
    hN hc.1 hc.2 (commonPrimeFibreMoment_nonneg _ _ _ _) (commonPrimeFibreMoment_nonneg _ _ _ _)
    F F hzero hzero hH' hH' hO hO
  rw [jumpPairing_self] at h
  change |completeWeilEnergy φ _ (X ^ d) (packetVector F (X ^ d)) - jumpEnergy (X ^ d) F| ≤ _ at h
  rw [commonPrimeFibre_jumpEnergy hM hQ S hS (X ^ d) t] at h
  have hp : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) =
      Real.log (X ^ d : ℕ) ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg (X ^ d))]
    norm_num
  rw [mul_pow, hp] at h
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by ring)

/-- The complete raw limit is the scalar horizon law times the squared receiving-coordinate norm. -/
theorem tendsto_commonPrimeFibre_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (M * X ^ a)
          (commonPrimeFibreCoefficients S M (X ^ a) (X ^ d) t)) (X ^ d)))
      atTop (𝓝 ((∑ m ∈ S, t m ^ 2) * ((d : ℝ) / a - 1 / 2))) := by
  simpa only [sub_add_cancel, zero_add] using
    (tendsto_commonPrimeFibre_complete_sub_jump hφ hφ0 hsupp hφM hK hM S hS t ha had).add
      (tendsto_commonPrimeFibre_dilation_energy hM S hS t ha had)

/-- Simultaneous coherent receiving coordinates have vanishing raw input square. -/
theorem tendsto_commonPrimeFibre_input_norm_sq {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (M * X ^ a)
        (commonPrimeFibreCoefficients S M (X ^ a) (X ^ d) t)) (X ^ d)‖ ^ 2) atTop (𝓝 0) := by
  have hlim := tendsto_commonPrimeFibreMoment_cost hM S t ha had (r := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), packetVector_norm_sq]
  exact (commonPrimeFibre_centered_moments hM (Nat.one_le_pow a X hX)
    (Nat.one_le_pow d X hX) S hS t).2.trans
      (mul_le_mul_of_nonneg_right (common_harmonicMass_le_log (X ^ d))
        (commonPrimeFibreMoment_nonneg S M (X ^ a) t))

/-- Physical coordinates of the exact finite receiving vector. -/
def commonPrimeFibreVector (S : Finset ℕ) (M Q N : ℕ) (t : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ •
    packetVector (normalizedConductorPacket (M * Q) (commonPrimeFibreCoefficients S M Q N t)) N

theorem commonPrimeFibreVector_energy (φ : ℝ → ℝ) (c : ℝ)
    (S : Finset ℕ) (M Q N : ℕ) (t : ℕ → ℝ) :
    completeWeilEnergy φ c N (commonPrimeFibreVector S M Q N t) =
      completeWeilEnergy φ c N
        (packetVector (normalizedConductorPacket (M * Q) (commonPrimeFibreCoefficients S M Q N t)) N) /
          Real.log N := by
  simp only [commonPrimeFibreVector, completeWeilEnergy, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- Complete physical energy vanishes for every fixed finite prescribed receiving vector. -/
theorem tendsto_commonPrimeFibre_physical_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (commonPrimeFibreVector S M (X ^ a) (X ^ d) t)) atTop (𝓝 0) := by
  have hNd : Tendsto (fun X : ℕ => X ^ d) atTop atTop :=
    tendsto_pow_atTop (ha.trans_le had).ne'
  simpa only [commonPrimeFibreVector_energy, Function.comp_def] using
    (tendsto_commonPrimeFibre_complete_energy hφ hφ0 hsupp hφM hK hM S hS t ha had).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hNd)

#print axioms tendsto_commonPrimeFibre_complete_energy
#print axioms tendsto_commonPrimeFibre_input_norm_sq
#print axioms tendsto_commonPrimeFibre_physical_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
