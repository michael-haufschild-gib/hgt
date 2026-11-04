import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargePairing
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeDilationScales

/-!
# The period Gram of simultaneous receiving charges

Using one common prime exclusion preserves exact receiving coordinates.
The mixed coprime product law evaluates the dilation energy of any finite
receiving vector by its Euclidean square mass and the scalar horizon law.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SelectiveMultiscaleArithmeticPositivity

private theorem common_prime_coprime {M m Q p : ℕ} (hmM : m ∣ M)
    (hp : p ∈ fibrePrimes M Q) : p.Coprime m := by
  have hpP := (mem_fibrePrimes.mp hp).2.1
  exact hpP.coprime_iff_not_dvd.mpr (fun h => (mem_fibrePrimes.mp hp).2.2 (h.trans hmM))

/-- Unit prime charge carried by a base mode, using a common coprime prime set. -/
def commonPrimeFibreUnit (m M Q n : ℕ) : ℝ :=
  normalizedRamanujanMode m n *
    incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n

/-- The common prime restriction leaves only the finite harmonic-Gram and base-jump errors. -/
theorem commonPrimeFibreUnit_pairing_error {M m l Q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    (N : ℕ) (hB : 0 < fibreScale M Q) :
    |jumpPairing N (commonPrimeFibreUnit m M Q) (commonPrimeFibreUnit l M Q) -
      (if m = l then 1 else 0) *
        jumpEnergy N (incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q))| ≤
      2 * (m : ℝ) * l / fibreScale M Q +
        (((m : ℝ) * (Real.log m + tameDifferent m) +
          (l : ℝ) * (Real.log l + tameDifferent l)) / 2) *
          ∑ n ∈ Icc 1 N,
            incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n ^ 2 / (n : ℝ) := by
  have h := abs_jumpPairing_coprime_modes_sub_le hm hl (P := fibrePrimes M Q)
    (fun p hp => (mem_fibrePrimes.mp hp).2.1)
    (fun _ hp => common_prime_coprime hmM hp)
    (fun _ hp => common_prime_coprime hlM hp)
    (fun _ => 1 / fibreScale M Q) (fun _ => 1 / fibreScale M Q) N
  have hmass : (∑ p ∈ fibrePrimes M Q,
      |(1 / fibreScale M Q) * (1 / fibreScale M Q)| * (Real.log p / p)) =
        1 / fibreScale M Q := by
    rw [← mul_sum, abs_of_nonneg (by positivity)]
    change _ * fibreScale M Q = _
    field_simp [hB.ne']
  rw [jumpPairing_self, hmass] at h
  exact h.trans_eq (by ring)

/-- Fixed coprime receiving modes become exactly diagonal in the dilation limit. -/
theorem tendsto_commonPrimeFibreUnit_pairing_error {M m l : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      jumpPairing (X ^ d) (commonPrimeFibreUnit m M (X ^ a)) (commonPrimeFibreUnit l M (X ^ a)) -
        (if m = l then 1 else 0) * jumpEnergy (X ^ d)
          (incidencePacket (fibrePrimes M (X ^ a)) (fun _ => 1 / fibreScale M (X ^ a))))
      atTop (𝓝 0) := by
  have hXa : Tendsto (fun X : ℕ => X ^ a) atTop atTop := tendsto_pow_atTop ha.ne'
  have hB := (fibreScale_tendsto_atTop hM).comp hXa
  let C := (((m : ℝ) * (Real.log m + tameDifferent m) +
    (l : ℝ) * (Real.log l + tameDifferent l)) / 2)
  have hC : 0 ≤ C := by
    have hmD := tameDifferent_nonneg m
    have hlD := tameDifferent_nonneg l
    have hmL := Real.log_natCast_nonneg m
    have hlL := Real.log_natCast_nonneg l
    dsimp only [C]
    positivity
  have hcost := tendsto_fibreIncidencePolynomialMoment_cost hM ha had (1 : ℝ)
    (r := 0) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at hcost
  have hlim := (hB.const_div_atTop (2 * (m : ℝ) * l)).add (hcost.const_mul C)
  simp only [Function.comp_apply, mul_zero, zero_add] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hB.eventually (eventually_gt_atTop 0)] with X hb
  have hH := incidencePacket_const_harmonic_square_le (P := fibrePrimes M (X ^ a))
    (fun p hp => (mem_fibrePrimes.mp hp).2.1) (1 / fibreScale M (X ^ a)) (X ^ d)
  have hmass : harmonicMass (X ^ d) ≤ Real.log (X ^ d : ℕ) + 1 := by
    have h := harmonic_le_one_add_log (X ^ d)
    have he : (harmonic (X ^ d) : ℝ) = harmonicMass (X ^ d) := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum (X ^ d)
    rw [he] at h
    linarith only [h]
  have hquad : 0 ≤ 4 * (∑ p ∈ fibrePrimes M (X ^ a), 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ fibrePrimes M (X ^ a), 1 / (p : ℝ) := by positivity
  have hH' := hH.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)) hquad)
  rw [Real.norm_eq_abs]
  exact (commonPrimeFibreUnit_pairing_error hm hl hmM hlM (X ^ d) hb).trans
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hH' hC)).trans_eq (by dsimp only [C]; ring))

/-- The scalar half-charge boundary is tensored with the exact base-mode period Gram. -/
theorem tendsto_commonPrimeFibreUnit_pairing {M m l : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ =>
      jumpPairing (X ^ d) (commonPrimeFibreUnit m M (X ^ a)) (commonPrimeFibreUnit l M (X ^ a)))
      atTop (𝓝 ((if m = l then 1 else 0) * ((d : ℝ) / a - 1 / 2))) := by
  have h := (tendsto_commonPrimeFibreUnit_pairing_error hM hm hl hmM hlM ha had).add
    ((tendsto_fibreIncidence_dilation_energy hM ha had (1 : ℝ)).const_mul (if m = l then 1 else 0))
  simpa only [one_pow, one_mul, zero_add, sub_add_cancel] using h

/-- Finite dilation pairing is bilinear in both scalar amplitudes. -/
theorem jumpPairing_scalar_profiles (N : ℕ) (F G : ℕ → ℝ) (s t : ℝ) :
    jumpPairing N (fun n => s * F n) (fun n => t * G n) = s * t * jumpPairing N F G := by
  unfold jumpPairing
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- Finite dilation pairing commutes with arbitrary finite profile sums. -/
theorem jumpPairing_sum_profiles {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (F : ι → ℕ → ℝ) (G : κ → ℕ → ℝ) (N : ℕ) :
    jumpPairing N (fun n => ∑ i ∈ S, F i n) (fun n => ∑ j ∈ T, G j n) =
      ∑ i ∈ S, ∑ j ∈ T, jumpPairing N (F i) (G j) := by
  simp only [jumpPairing, ← sum_sub_distrib, sum_mul, mul_sum,
    div_eq_mul_inv]
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]

/-- The prescribed common packet is the finite scalar combination of its unit fibres. -/
theorem commonPrimeFibreProfile_sum_units (S : Finset ℕ) (M Q : ℕ) (t : ℕ → ℝ) (n : ℕ) :
    commonPrimeFibreProfile S M Q t n = ∑ m ∈ S, t m * commonPrimeFibreUnit m M Q n := by
  unfold commonPrimeFibreProfile commonPrimeFibreUnit
  apply sum_congr rfl
  intro m _
  simp only [incidencePacket_const_eq_count]
  ring

/-- Every finite receiving vector has the scalar dilation cost times its squared coordinate norm. -/
theorem tendsto_commonPrimeFibre_dilation_energy {M : ℕ} (hM : 0 < M)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m ∧ m ∣ M) (t : ℕ → ℝ)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun X : ℕ => jumpEnergy (X ^ d) (commonPrimeFibreProfile S M (X ^ a) t))
      atTop (𝓝 ((∑ m ∈ S, t m ^ 2) * ((d : ℝ) / a - 1 / 2))) := by
  have h := tendsto_finsetSum S (fun m hm => tendsto_finsetSum S (fun l hl =>
    (tendsto_commonPrimeFibreUnit_pairing hM (hS m hm).1 (hS l hl).1
      (hS m hm).2 (hS l hl).2 ha had).const_mul (t m * t l)))
  have hlimit : (∑ m ∈ S, ∑ l ∈ S,
      t m * t l * ((if m = l then 1 else 0) * ((d : ℝ) / a - 1 / 2))) =
      (∑ m ∈ S, t m ^ 2) * ((d : ℝ) / a - 1 / 2) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single_of_mem m hm]
    · rw [if_pos rfl]
      ring
    · intro l _ hl
      rw [if_neg (Ne.symm hl)]
      ring
  rw [hlimit] at h
  apply h.congr
  intro X
  rw [funext (commonPrimeFibreProfile_sum_units S M (X ^ a) t), ← jumpPairing_self,
    jumpPairing_sum_profiles]
  simp only [jumpPairing_scalar_profiles]

#print axioms tendsto_commonPrimeFibreUnit_pairing
#print axioms tendsto_commonPrimeFibre_dilation_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
