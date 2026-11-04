import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCapacity
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePrefixComplete
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormLinearAlgebra

/-!
# Finite distributions of prime-prefix receiving charge

Several polynomial prime prefixes can be placed in one harmonic-neutral
conductor packet. Its generator charge is exactly the sum of the prescribed
prefix charges. Its complete critical energy is the quadratic form of the
explicit symmetric prefix kernel.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
  RenormalizedArithmeticPotentialTheory

/-- Coefficients of a charged prime prefix, extended by zero past its own cutoff. -/
def prefixChargeWeight (Q : ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  if p ≤ Q then t / primePoleScale Q else 0

private theorem incidencePacket_sum_profiles {ι : Type*} (P : Finset ℕ) (S : Finset ι)
    (b : ι → ℕ → ℝ) (n : ℕ) :
    incidencePacket P (fun p => ∑ i ∈ S, b i p) n = ∑ i ∈ S, incidencePacket P (b i) n := by
  simp only [incidencePacket, sum_mul]
  rw [sum_comm]

/-- Harmonic centering commutes with every finite sum of incidence profiles. -/
theorem harmonicPrimeIncidence_packet_sum {ι : Type*} {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ)
    (S : Finset ι) (b : ι → ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N (fun p => ∑ i ∈ S, b i p)) n =
      ∑ i ∈ S, normalizedConductorPacket Q (harmonicPrimeIncidenceCoefficients Q N (b i)) n := by
  simp only [harmonicPrimeIncidence_packet_formula hQ, incidencePacket_sum_profiles, sum_div]
  rw [sum_comm, ← sum_sub_distrib]

/-- Extending a prefix does not change its centered horizon profile. -/
theorem harmonicPrimeIncidence_prefix {Q R : ℕ} (hQ : 1 ≤ Q) (hQR : Q ≤ R)
    (N : ℕ) (t : ℝ) (n : ℕ) :
    normalizedConductorPacket R (harmonicPrimeIncidenceCoefficients R N (prefixChargeWeight Q t)) n =
      normalizedConductorPacket Q (harmonicPrimeChargeCoefficients Q N t) n := by
  rw [harmonicPrimeCharge_eq_incidence, harmonicPrimeIncidence_packet_formula (hQ.trans hQR),
    harmonicPrimeIncidence_packet_formula hQ]
  have he (j : ℕ) : incidencePacket ((Icc 1 R).filter Nat.Prime) (prefixChargeWeight Q t) j =
      incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => t / primePoleScale Q) j :=
    (incidencePacket_primePrefix_extend hQR (fun _ => t / primePoleScale Q) j).symm
  simp only [he]

/-- Zero extension preserves the literal receiving charge of each prime prefix. -/
theorem prefixChargeWeight_receiving_charge {Q R : ℕ} (hQ : 2 ≤ Q) (hQR : Q ≤ R) (t : ℝ) :
    primeIncidenceReceivingCharge ((Icc 1 R).filter Nat.Prime) (prefixChargeWeight Q t) = t := by
  simp only [primeIncidenceReceivingCharge, prefixChargeWeight, ite_mul, zero_mul]
  rw [← sum_filter, primePrefix_filter hQR, ← mul_sum]
  exact div_mul_cancel₀ t (primePoleScale_pos hQ).ne'

/-- A finite charge distribution synthesized at the common polynomial horizon cutoff. -/
def primeChargeCombinationCoefficients {ι : Type*} (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ)
    (d X : ℕ) : ℕ → ℝ :=
  harmonicPrimeIncidenceCoefficients (X ^ d) (X ^ d)
    (fun p => ∑ i ∈ S, prefixChargeWeight (X ^ a i) (t i) p)

/-- Extension of a coherent prefix preserves its exact adjunction mass. -/
theorem prefixChargeWeight_adjunction {Q R : ℕ} (hQ : 2 ≤ Q) (hQR : Q ≤ R)
    (N : ℕ) (t : ℝ) :
    primeAdjunctionMass R (harmonicPrimeIncidenceCoefficients R N (prefixChargeWeight Q t)) =
      t ^ 2 / primePoleScale Q := by
  rw [harmonicPrimeIncidence_adjunction]
  simp only [prefixChargeWeight, ite_pow, zero_pow two_ne_zero, ite_mul, zero_mul]
  rw [← sum_filter, primePrefix_filter hQR, ← mul_sum]
  change (t / primePoleScale Q) ^ 2 * primePoleScale Q = _
  field_simp [(primePoleScale_pos hQ).ne']

/-- The common packet is exactly the sum of its centered coherent prefixes. -/
theorem primeChargeCombination_packet {ι : Type*} (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ)
    {d X : ℕ} (hX : 2 ≤ X) (had : ∀ i ∈ S, a i ≤ d) (n : ℕ) :
    normalizedConductorPacket (X ^ d) (primeChargeCombinationCoefficients S a t d X) n =
      ∑ i ∈ S, normalizedConductorPacket (X ^ a i)
        (harmonicPrimeChargeCoefficients (X ^ a i) (X ^ d) (t i)) n := by
  rw [primeChargeCombinationCoefficients, harmonicPrimeIncidence_packet_sum
    (Nat.one_le_pow d X (by omega))]
  apply sum_congr rfl
  intro i hi
  exact harmonicPrimeIncidence_prefix (Nat.one_le_pow (a i) X (by omega))
    (Nat.pow_le_pow_right (by omega) (had i hi)) (X ^ d) (t i) n

/-- Finite prefix distributions retain their total receiving charge exactly. -/
theorem primeChargeCombination_receiving_charge {ι : Type*} (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ)
    {d X : ℕ} (hX : 2 ≤ X) (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    packetMean (X ^ d) (arithmeticPrimeGenerator (X ^ d)
      (primeChargeCombinationCoefficients S a t d X)) = ∑ i ∈ S, t i := by
  rw [primeChargeCombinationCoefficients, harmonicPrimeIncidence_receiving_charge]
  simp only [primeIncidenceReceivingCharge, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  exact prefixChargeWeight_receiving_charge (hX.trans (Nat.le_pow (ha i hi)))
    (Nat.pow_le_pow_right (by omega) (had i hi)) (t i)

/-- Every finite prefix distribution is exactly harmonic-pole neutral. -/
theorem primeChargeCombination_neutral {ι : Type*} (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ)
    (d : ℕ) {X : ℕ} (hX : 1 ≤ X) :
    harmonicSum (X ^ d) (conductorHorizonProfile (X ^ d)
      (primeChargeCombinationCoefficients S a t d X)) = 0 :=
  harmonicPrimeIncidence_neutral (Nat.one_le_pow d X hX) (Nat.one_le_pow d X hX) _

/-- The symmetric prefix kernel, expressed in cutoff exponents. -/
def primePrefixReceivingKernel (a b d : ℕ) : ℝ :=
  (d : ℝ) / (max a b : ℕ) - (min a b : ℕ) / (2 * (max a b : ℕ))

/-- The complete mixed limit is the symmetric prefix kernel in either cutoff order. -/
theorem tendsto_primeCharge_prefix_kernel {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a b d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (had : a ≤ d) (hbd : b ≤ d) (t u : ℝ) :
    Tendsto (fun X : ℕ =>
      completePacketPairing φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (normalizedConductorPacket (X ^ a) (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t))
        (normalizedConductorPacket (X ^ b) (harmonicPrimeChargeCoefficients (X ^ b) (X ^ d) u)))
      atTop (𝓝 (t * u * primePrefixReceivingKernel a b d)) := by
  rcases le_total a b with hab | hba
  · simpa only [primePrefixReceivingKernel, max_eq_right hab, min_eq_left hab] using
      tendsto_harmonicPrimeCharge_complete_prefix_pairing hφ hφ0 hsupp hM hK ha hab hbd t u
  · have h := tendsto_harmonicPrimeCharge_complete_prefix_pairing hφ hφ0 hsupp hM hK hb hba had u t
    simpa only [primePrefixReceivingKernel, max_eq_left hba, min_eq_right hba,
      completePacketPairing_symm, mul_comm u t] using h

/-- The full critical form evaluates every finite coherent charge distribution by its explicit kernel. -/
theorem tendsto_primeChargeCombination_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {ι : Type*} (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (X ^ d)
          (primeChargeCombinationCoefficients S a t d X)) (X ^ d)))
      atTop (𝓝 (∑ i ∈ S, ∑ j ∈ S, t i * t j * primePrefixReceivingKernel (a i) (a j) d)) := by
  have h := tendsto_finsetSum S (fun i hi => tendsto_finsetSum S (fun j hj =>
    tendsto_primeCharge_prefix_kernel hφ hφ0 hsupp hM hK
      (ha i hi) (ha j hj) (had i hi) (had j hj) (t i) (t j)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [funext (primeChargeCombination_packet S a t hX had), completeWeilEnergy_packet_sum]

/-- Finite coherent charge distributions have vanishing raw input norm. -/
theorem tendsto_primeChargeCombination_input_norm {ι : Type*}
    (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (X ^ d)
        (primeChargeCombinationCoefficients S a t d X)) (X ^ d)‖) atTop (𝓝 0) := by
  have hsingle (i : ι) (hi : i ∈ S) : Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (X ^ a i)
        (harmonicPrimeChargeCoefficients (X ^ a i) (X ^ d) (t i))) (X ^ d)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (tendsto_harmonicPrimeCharge_polynomial_input_norm_sq (ha i hi) (had i hi) (t i)).sqrt
  have hsum := tendsto_finsetSum S hsingle
  simp only [sum_const_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    funext (primeChargeCombination_packet S a t hX had), packetVector_finset_sum]
  exact norm_sum_le _ _

/-- Exact receiving charge distributions have vanishing adjunction mass. -/
theorem tendsto_primeChargeCombination_adjunction {ι : Type*}
    (S : Finset ι) (a : ι → ℕ) (t : ι → ℝ) {d : ℕ}
    (ha : ∀ i ∈ S, 0 < a i) (had : ∀ i ∈ S, a i ≤ d) :
    Tendsto (fun X : ℕ => primeAdjunctionMass (X ^ d)
      (primeChargeCombinationCoefficients S a t d X)) atTop (𝓝 0) := by
  have hsingle (i : ι) (hi : i ∈ S) : Tendsto
      (fun X : ℕ => t i ^ 2 / primePoleScale (X ^ a i)) atTop (𝓝 0) :=
    (primePoleScale_tendsto_atTop.comp (tendsto_pow_atTop (ha i hi).ne')).const_div_atTop _
  have hsum := (tendsto_finsetSum S hsingle).const_mul (S.card : ℝ)
  simp only [sum_const_zero, mul_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (primeAdjunctionMass_nonneg _ _)]
  refine (harmonicPrimeIncidence_sum_adjunction_le S
    (fun i => prefixChargeWeight (X ^ a i) (t i)) (X ^ d) (X ^ d)).trans_eq ?_
  congr 1
  apply sum_congr rfl
  intro i hi
  exact prefixChargeWeight_adjunction (hX.trans (Nat.le_pow (ha i hi)))
    (Nat.pow_le_pow_right (by omega) (had i hi)) (X ^ d) (t i)

#print axioms primeChargeCombination_receiving_charge
#print axioms primeChargeCombination_neutral
#print axioms tendsto_primeChargeCombination_complete_energy
#print axioms tendsto_primeChargeCombination_input_norm
#print axioms tendsto_primeChargeCombination_adjunction

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
