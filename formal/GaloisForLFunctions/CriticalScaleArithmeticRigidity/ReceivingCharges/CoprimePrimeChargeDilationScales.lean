import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeDilation
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeScales

/-!
# The exact scalar energy limit survives deletion of fixed conductor primes

Deleting the primes of a fixed base conductor removes only a bounded prime
Mertens mass. Its finite dilation cost is bounded by that mass times the
harmonic horizon. Coherent normalization makes this error vanish.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity ArithmeticIntersectionTheory

private theorem harmonicMass_natDiv_le (N p : ℕ) : harmonicMass (N / p) ≤ harmonicMass N := by
  exact sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc le_rfl (Nat.div_le_self N p)) (fun n _ _ => by positivity)

private theorem badPrime_cofactor_mass_le {m : ℕ} (hm : 0 < m) (Q N : ℕ) :
    (∑ p ∈ ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ∣ m),
      Real.log p / p * harmonicMass (N / p)) ≤ harmonicMass N * fibreLoss m := by
  have hsub : ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ∣ m) ⊆ m.primeFactors := by
    intro p hp
    obtain ⟨hp', hpm⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp').2, hpm, hm.ne'⟩
  calc
    _ ≤ harmonicMass N * ∑ p ∈ ((Icc 1 Q).filter Nat.Prime).filter (fun p => p ∣ m),
        Real.log p / p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p _
      exact (mul_le_mul_of_nonneg_left (harmonicMass_natDiv_le N p)
        (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))).trans_eq (mul_comm _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
        div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      (sum_nonneg fun n _ => by positivity)

/-- The deleted base primes have an explicit finite cofactor error. -/
theorem fibreIncidence_dilation_error_le {m Q : ℕ} (hm : 0 < m) (hQ : 2 ≤ Q)
    (N : ℕ) (t : ℝ) (hB : 0 < fibreScale m Q) :
    |jumpEnergy N (incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q)) -
      (primePoleScale Q / fibreScale m Q) ^ 2 *
        jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t))| ≤
      (t / fibreScale m Q) ^ 2 * harmonicMass N * fibreLoss m := by
  let P := (Icc 1 Q).filter Nat.Prime
  let bad := P.filter (fun p => p ∣ m)
  let D := ∑ p ∈ bad, Real.log p / p * harmonicMass (N / p)
  have hD0 : 0 ≤ D := by
    exact sum_nonneg fun p _ => mul_nonneg
      (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      (sum_nonneg fun n _ => by positivity)
  have hsplit := sum_filter_add_sum_filter_not P (fun p => p ∣ m)
    (fun p => Real.log p / p * harmonicMass (N / p))
  have hfib : P.filter (fun p => ¬ p ∣ m) = fibrePrimes m Q := by
    ext p
    simp only [P, mem_filter, fibrePrimes]
    tauto
  rw [hfib] at hsplit
  have hJ : jumpEnergy N (incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q)) =
      (t / fibreScale m Q) ^ 2 *
        ∑ p ∈ fibrePrimes m Q, Real.log p / p * harmonicMass (N / p) := by
    rw [jumpEnergy_incidencePacket_diagonal (fun p hp => (mem_fibrePrimes.mp hp).2.1), mul_sum]
    rfl
  have hscale : (primePoleScale Q / fibreScale m Q) ^ 2 * (t / primePoleScale Q) ^ 2 =
      (t / fibreScale m Q) ^ 2 := by
    field_simp [hB.ne', (primePoleScale_pos hQ).ne']
  have he : jumpEnergy N (incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q)) -
      (primePoleScale Q / fibreScale m Q) ^ 2 *
        jumpEnergy N (normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t)) =
      -((t / fibreScale m Q) ^ 2 * D) := by
    rw [hJ, harmonicPrimeCharge_jumpEnergy (by omega : 1 ≤ Q), ← mul_assoc, hscale]
    change _ - _ * (∑ p ∈ P, Real.log p / p * harmonicMass (N / p)) = _
    rw [← hsplit]
    dsimp only [D, bad]
    ring
  rw [he, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) hD0)]
  exact (mul_le_mul_of_nonneg_left (badPrime_cofactor_mass_le hm Q N)
    (sq_nonneg _)).trans_eq (by ring)

/-- The finite deletion error tends to zero at every fixed polynomial scale. -/
theorem tendsto_fibreIncidence_dilation_error {m : ℕ} (hm : 0 < m)
    {a : ℕ} (ha : 0 < a) (d : ℕ) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      jumpEnergy (X ^ d) (incidencePacket (fibrePrimes m (X ^ a))
        (fun _ => t / fibreScale m (X ^ a))) -
      (primePoleScale (X ^ a) / fibreScale m (X ^ a)) ^ 2 *
        jumpEnergy (X ^ d) (normalizedConductorPacket (X ^ a)
          (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hlim := (tendsto_fibreCharge_log_cost hm ha d t).mul_const (fibreLoss m)
  simp only [zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2, hB.eventually (eventually_ge_atTop 1)] with X hX hb
  have hQ : 2 ≤ X ^ a := hX.trans (Nat.le_pow ha)
  have hH : harmonicMass (X ^ d) ≤ Real.log (X ^ d : ℕ) + 1 := by
    have h := harmonic_le_one_add_log (X ^ d)
    have he : (harmonic (X ^ d) : ℝ) = harmonicMass (X ^ d) := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (X ^ d)
    rw [he] at h
    linarith only [h]
  have hloss : 0 ≤ fibreLoss m := sum_nonneg fun p _ =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  rw [Real.norm_eq_abs]
  refine (fibreIncidence_dilation_error_le hm hQ (X ^ d) t (zero_lt_one.trans_le hb)).trans ?_
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (sq_nonneg _)) hloss).trans_eq
    (by ring)

/-- Coprime prime restriction preserves the full scalar half-charge boundary. -/
theorem tendsto_fibreIncidence_dilation_energy {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => jumpEnergy (X ^ d)
      (incidencePacket (fibrePrimes m (X ^ a)) (fun _ => t / fibreScale m (X ^ a))))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have h := (tendsto_fibreIncidence_dilation_error hm ha d t).add
    ((((tendsto_primePoleScale_div_fibreScale hm).comp hXa).pow 2).mul
      (tendsto_harmonicPrimeCharge_polynomial_dilation_energy ha had t))
  simpa only [Function.comp_apply, one_pow, one_mul, zero_add, sub_add_cancel] using h

/-- The fixed base mode has precisely a coefficient-mass and an input-moment discrepancy. -/
theorem fibreCharge_dilation_error_le {m Q : ℕ} (hm : 0 < m) (N : ℕ) (t : ℝ)
    (hB : 0 < fibreScale m Q) :
    |jumpEnergy N (normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t))) -
      jumpEnergy N (incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q))| ≤
      2 * (m : ℝ) ^ 2 * (t ^ 2 / fibreScale m Q) +
      (m : ℝ) * (Real.log m + tameDifferent m) *
        ∑ n ∈ Icc 1 N, incidencePacket (fibrePrimes m Q) (fun _ => t / fibreScale m Q) n ^ 2 / (n : ℝ) := by
  have he := funext (normalizedConductorPacket_fibreCharge_incidence hm Q t)
  rw [he]
  have h := abs_jumpEnergy_coprime_mode_sub_le hm (P := fibrePrimes m Q)
    (fun p hp => (mem_fibrePrimes.mp hp).2.1)
    (fun p hp => (coprime_of_mem_fibrePrimes hp).symm)
    (fun _ => t / fibreScale m Q) N
  have hmass : (∑ p ∈ fibrePrimes m Q, (t / fibreScale m Q) ^ 2 * (Real.log p / p)) =
      t ^ 2 / fibreScale m Q := by
    rw [← mul_sum]
    change (t / fibreScale m Q) ^ 2 * fibreScale m Q = _
    field_simp [hB.ne']
  rw [hmass] at h
  exact h

/-- Multiplication by the fixed conductor preserves the polynomial dilation limit. -/
theorem tendsto_fibreCharge_dilation_error {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      jumpEnergy (X ^ d) (normalizedConductorPacket (m * X ^ a)
        (fibreCoefficients m (X ^ a) (fibreCharge m (X ^ a) t))) -
      jumpEnergy (X ^ d) (incidencePacket (fibrePrimes m (X ^ a))
        (fun _ => t / fibreScale m (X ^ a)))) atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hm).comp hXa
  have hcost := tendsto_fibreIncidencePolynomialMoment_cost hm ha had t (r := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hcost
  have hlim := ((hB.const_div_atTop (t ^ 2)).const_mul (2 * (m : ℝ) ^ 2)).add
    (hcost.const_mul ((m : ℝ) * (Real.log m + tameDifferent m)))
  simp only [Function.comp_apply, mul_zero, zero_add] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hB.eventually (eventually_ge_atTop 1)] with X hb
  have hP : ∀ p ∈ fibrePrimes m (X ^ a), p.Prime := fun p hp => (mem_fibrePrimes.mp hp).2.1
  have hH := incidencePacket_const_harmonic_square_le hP (t / fibreScale m (X ^ a)) (X ^ d)
  have hmass : harmonicMass (X ^ d) ≤ Real.log (X ^ d : ℕ) + 1 := by
    have h := harmonic_le_one_add_log (X ^ d)
    have he : (harmonic (X ^ d) : ℝ) = harmonicMass (X ^ d) := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (X ^ d)
    rw [he] at h
    linarith only [h]
  have hquad : 0 ≤ 4 * (∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ fibrePrimes m (X ^ a), 1 / (p : ℝ) := by positivity
  have hH' := hH.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)) hquad)
  have hC : 0 ≤ (m : ℝ) * (Real.log m + tameDifferent m) :=
    mul_nonneg (Nat.cast_nonneg m) (add_nonneg (Real.log_natCast_nonneg m) (tameDifferent_nonneg m))
  rw [Real.norm_eq_abs]
  refine (fibreCharge_dilation_error_le hm (X ^ d) t (zero_lt_one.trans_le hb)).trans ?_
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hH' hC)).trans_eq (by ring)

/-- The literal uncentered fibre has the same raw positive energy and half-charge boundary. -/
theorem tendsto_fibreCharge_dilation_energy {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => jumpEnergy (X ^ d)
      (normalizedConductorPacket (m * X ^ a)
        (fibreCoefficients m (X ^ a) (fibreCharge m (X ^ a) t))))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  simpa only [sub_add_cancel, zero_add] using
    (tendsto_fibreCharge_dilation_error hm ha had t).add
      (tendsto_fibreIncidence_dilation_energy hm ha had t)

/-- Harmonic pole removal leaves fibre dilation energy exactly unchanged. -/
theorem harmonicFibreCharge_jumpEnergy {m Q : ℕ} (hm : 0 < m) (hQ : 1 ≤ Q) (N : ℕ) (t : ℝ) :
    jumpEnergy N (normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t)) =
      jumpEnergy N (normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t))) := by
  have he (n : ℕ) : normalizedConductorPacket (m * Q) (harmonicFibreChargeCoefficients m Q N t) n =
      normalizedConductorPacket (m * Q) (fibreCoefficients m Q (fibreCharge m Q t)) n -
        harmonicSum N (conductorHorizonProfile (m * Q) (fibreCoefficients m Q (fibreCharge m Q t))) /
          harmonicMass N := by
    rw [harmonicFibreChargeCoefficients, harmonicCenteredCoefficients,
      normalizedConductorPacket_addConstantConductor (Nat.mul_pos hm hQ)]
    rfl
  rw [funext he, jumpEnergy_sub_const]

/-- The exact harmonic-neutral fibre retains the scalar polynomial dilation limit. -/
theorem tendsto_harmonicFibreCharge_dilation_energy {m : ℕ} (hm : 0 < m)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ => jumpEnergy (X ^ d)
      (normalizedConductorPacket (m * X ^ a) (harmonicFibreChargeCoefficients m (X ^ a) (X ^ d) t)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) := by
  apply (tendsto_fibreCharge_dilation_energy hm ha had t).congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  exact (harmonicFibreCharge_jumpEnergy hm (Nat.one_le_pow a X hX) (X ^ d) t).symm

#print axioms fibreIncidence_dilation_error_le
#print axioms tendsto_fibreIncidence_dilation_energy
#print axioms tendsto_harmonicFibreCharge_dilation_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
