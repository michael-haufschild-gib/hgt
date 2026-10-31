import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorDilationMoments
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon

/-!
# Prime heads measured in the packet's exact arithmetic energy

Only prime towers below the conductor cutoff act on a packet. Their finite
total Mangoldt mass and the exact dilation-square identity give a sector
bound uniform in the prime head. The right side retains the packet's
adjunction energy instead of replacing it by the worst conductor weight.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SuccessorShellArithmetic RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory CriticalArithmeticCorrelationTheory

/-- Total reciprocal Mangoldt mass of the prime towers that can act below `Q`. -/
def primeActivityMass (Q : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)

/-- Exact prime-dilation square energy in normalized conductor coordinates. -/
def primeAdjunctionMass (Q : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2

/-- Coefficients of an arbitrary finite head of the literal prime generator. -/
def primeHeadCoefficient (Q : ℕ) (a : ℕ → ℝ) (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ k ∈ S, vonMangoldt k / (k : ℝ) * primeConductorDilationJump Q a k m

/-- The arithmetic packet in orthonormal conductor coordinates. -/
def normalizedConductorPacket (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n

theorem primeActivityMass_nonneg (Q : ℕ) : 0 ≤ primeActivityMass Q := by
  apply sum_nonneg
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  exact div_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hpR.le)

theorem primeActivityMass_le_log {Q : ℕ} (hQ : 1 ≤ Q) :
    primeActivityMass Q ≤ 14 * (1 + Real.log Q) :=
  sum_primeDilationMass_le_log hQ

private theorem primeJump_energy_head_le (Q : ℕ) (a : ℕ → ℝ) (S : Finset ℕ) :
    (∑ k ∈ S, vonMangoldt k / (k : ℝ) *
      ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) ≤
        primeAdjunctionMass Q a := by
  have hs := hasSum_primeConductorDilationJump_sq Q a
  have h := hs.summable.sum_le_tsum S (fun k _ =>
    mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      (sum_nonneg fun _ _ => sq_nonneg _))
  simpa only [hs.tsum_eq, primeAdjunctionMass] using h

theorem primeAdjunctionMass_nonneg (Q : ℕ) (a : ℕ → ℝ) :
    0 ≤ primeAdjunctionMass Q a := by
  simpa only [sum_empty] using primeJump_energy_head_le Q a ∅

private def activePrimeTower (Q k : ℕ) : Prop :=
  ∃ p ∈ (Icc 1 Q).filter Nat.Prime, p ∣ k

private theorem primeJump_weighted_eq_zero_of_inactive {Q k m : ℕ}
    (a : ℕ → ℝ) (hm : m ∈ Icc 1 Q) (hk : ¬activePrimeTower Q k) :
    vonMangoldt k / (k : ℝ) * primeConductorDilationJump Q a k m = 0 := by
  by_cases hΛ : vonMangoldt k = 0
  · rw [hΛ, zero_div, zero_mul]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff k).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hQp : Q < p := by
    by_contra h
    apply hk
    exact ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, Nat.le_of_not_gt h⟩, hp⟩,
      dvd_pow_self p hj.ne'⟩
  rw [primeConductorDilationJump_eq_zero_of_prime_gt a hp hQp hm j, mul_zero]

private theorem active_prime_mass_le (Q : ℕ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, activePrimeTower Q k) :
    (∑ k ∈ S, vonMangoldt k / (k : ℝ)) ≤ primeActivityMass Q := by
  have hp (k : ℕ) (hk : k ∈ S) :
      vonMangoldt k / (k : ℝ) ≤
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, if p ∣ k then vonMangoldt k / (k : ℝ) else 0 := by
    obtain ⟨p, hp, hpk⟩ := hS k hk
    have h := single_le_sum (f := fun p : ℕ =>
      if p ∣ k then vonMangoldt k / (k : ℝ) else 0)
      (fun p _ => by
        split_ifs
        · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
        · exact le_rfl) hp
    simpa only [if_pos hpk] using h
  calc
    _ ≤ ∑ k ∈ S, ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if p ∣ k then vonMangoldt k / (k : ℝ) else 0 := sum_le_sum hp
    _ = ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ k ∈ S,
        if p ∣ k then vonMangoldt k / (k : ℝ) else 0 := sum_comm
    _ ≤ _ := sum_le_sum fun p hp => sum_dvd_vonMangoldt_div_le (mem_filter.mp hp).2 S

/-- Cauchy–Schwarz in a finite nonnegative arithmetic measure. -/
theorem nonnegative_weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * x i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * x i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * x i)
  have h1 : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * x i)) =
      ∑ i ∈ S, w i * x i := by
    apply sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i hi)]
  have h2 : (∑ i ∈ S, Real.sqrt (w i) ^ 2) = ∑ i ∈ S, w i :=
    sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have h3 : (∑ i ∈ S, (Real.sqrt (w i) * x i) ^ 2) =
      ∑ i ∈ S, w i * x i ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [h1, h2, h3] at h

/-- The active-prime mass controls each literal row before any row-dependent head is chosen. -/
theorem primeHead_value_sq_le (Q : ℕ) (a : ℕ → ℝ) (S : Finset ℕ) (n : ℕ) :
    (∑ k ∈ S, vonMangoldt k / (k : ℝ) *
      (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n)) ^ 2 ≤
      primeActivityMass Q * ∑ k ∈ S, vonMangoldt k / (k : ℝ) *
        (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n) ^ 2 := by
  let T := S.filter (activePrimeTower Q)
  let d := fun k => normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n
  have hzero (k : ℕ) (hk : ¬activePrimeTower Q k) :
      vonMangoldt k / (k : ℝ) * d k = 0 := by
    dsimp only [d, normalizedConductorPacket]
    rw [← primeConductorDilationJump_packet, mul_sum]
    apply sum_eq_zero
    intro m hm
    rw [← mul_assoc, primeJump_weighted_eq_zero_of_inactive a hm hk, zero_mul]
  have heq : (∑ k ∈ S, vonMangoldt k / (k : ℝ) * d k) =
      ∑ k ∈ T, vonMangoldt k / (k : ℝ) * d k := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro k hk hnot
    exact hzero k (fun ha => hnot (mem_filter.mpr ⟨hk, ha⟩))
  have hmass := active_prime_mass_le Q T (fun k hk => (mem_filter.mp hk).2)
  have henergy : (∑ k ∈ T, vonMangoldt k / (k : ℝ) * d k ^ 2) ≤
      ∑ k ∈ S, vonMangoldt k / (k : ℝ) * d k ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
      mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) (sq_nonneg _)
  change (∑ k ∈ S, vonMangoldt k / (k : ℝ) * d k) ^ 2 ≤ _
  rw [heq]
  exact (nonnegative_weighted_sum_sq_le T _ d (fun k _ =>
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans
      (mul_le_mul hmass henergy
        (sum_nonneg fun k _ => mul_nonneg
          (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) (sq_nonneg _))
        (primeActivityMass_nonneg Q))

/-- The first logarithmic prime moment preserves the exact adjunction mass. -/
theorem primeDilation_logWeightedEnergy_le {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ((18 * (1 + Real.log Q) + Real.log k) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) ≤
      19 * (1 + Real.log Q) * primeAdjunctionMass Q a := by
  have henergy := primeJump_energy_head_le Q a (Icc 1 K)
  have hmoment := sum_primeConductorDilationJump_logMoment_le hQ a K
  change _ ≤ (1 + Real.log Q) * primeAdjunctionMass Q a at hmoment
  have heq : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ((18 * (1 + Real.log Q) + Real.log k) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) =
      18 * (1 + Real.log Q) * (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) +
      ∑ k ∈ Icc 1 K, vonMangoldt k * Real.log k / (k : ℝ) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  rw [heq]
  have h := add_le_add (mul_le_mul_of_nonneg_left henergy
    (by positivity : 0 ≤ 18 * (1 + Real.log (Q : ℝ)))) hmoment
  nlinarith only [h]

/-- Every finite prime head is bounded in the packet's exact adjunction energy. -/
theorem primeHeadCoefficient_sq_sum_le (Q : ℕ) (a : ℕ → ℝ) (S : Finset ℕ) :
    (∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m ^ 2) ≤
      primeActivityMass Q * primeAdjunctionMass Q a := by
  let T := S.filter (activePrimeTower Q)
  have heq (m : ℕ) (hm : m ∈ Icc 1 Q) : primeHeadCoefficient Q a S m =
      ∑ k ∈ T, vonMangoldt k / (k : ℝ) * primeConductorDilationJump Q a k m := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro k hk hnot
    apply primeJump_weighted_eq_zero_of_inactive a hm
    intro ha
    exact hnot (mem_filter.mpr ⟨hk, ha⟩)
  have hcs (m : ℕ) (hm : m ∈ Icc 1 Q) :
      primeHeadCoefficient Q a S m ^ 2 ≤ (∑ k ∈ T, vonMangoldt k / (k : ℝ)) *
        ∑ k ∈ T, vonMangoldt k / (k : ℝ) * primeConductorDilationJump Q a k m ^ 2 := by
    rw [heq m hm]
    exact nonnegative_weighted_sum_sq_le T _ _ (fun k _ =>
      div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  have hsum := sum_le_sum hcs
  rw [← mul_sum, sum_comm] at hsum
  simp only [← mul_sum] at hsum
  have hmass := active_prime_mass_le Q T (fun k hk => (mem_filter.mp hk).2)
  have henergy := primeJump_energy_head_le Q a T
  exact hsum.trans (mul_le_mul hmass henergy
    (sum_nonneg fun k _ => mul_nonneg
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) (sum_nonneg fun _ _ => sq_nonneg _))
    (primeActivityMass_nonneg Q))

/-- The mixed prime interaction costs the energy of its source packet, with no inverse
completed-energy floor. -/
theorem primeHeadCoefficient_mixed_sq_le (Q : ℕ) (a b : ℕ → ℝ) (S : Finset ℕ) :
    (∑ m ∈ Icc 1 Q, b m * primeHeadCoefficient Q a S m) ^ 2 ≤
      primeActivityMass Q * (∑ m ∈ Icc 1 Q, b m ^ 2) * primeAdjunctionMass Q a := by
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) b (primeHeadCoefficient Q a S)
  have h := hcs.trans (mul_le_mul_of_nonneg_left (primeHeadCoefficient_sq_sum_le Q a S)
    (sum_nonneg fun _ _ => sq_nonneg _))
  simpa only [mul_left_comm, mul_assoc] using h

/-- A logarithmic active-prime cost suffices for every head length. -/
theorem primeHeadCoefficient_sq_sum_le_log {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (S : Finset ℕ) :
    (∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m ^ 2) ≤
      14 * (1 + Real.log Q) * primeAdjunctionMass Q a :=
  (primeHeadCoefficient_sq_sum_le Q a S).trans
    (mul_le_mul_of_nonneg_right (primeActivityMass_le_log hQ) (primeAdjunctionMass_nonneg Q a))

/-- The coefficient head is the literal prime-weighted dilation difference at every integer. -/
theorem primeHeadCoefficient_packet (Q : ℕ) (a : ℕ → ℝ) (S : Finset ℕ) (n : ℕ) :
    (∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m * normalizedRamanujanMode m n) =
      ∑ k ∈ S, vonMangoldt k / (k : ℝ) *
        ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
          ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) := by
  simp only [primeHeadCoefficient, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← primeConductorDilationJump_packet, mul_sum]
  apply sum_congr rfl
  intro m _
  ring

/-- Actual finite-window prime-head energy satisfies the same relative source bound,
with the sharp quadratic separation loss. -/
theorem primeHead_window_sq_le {Q : ℕ} (hQ : 2 ≤ Q)
    (a : ℕ → ℝ) (S : Finset ℕ) (A K : ℕ) :
    (∑ n ∈ Icc (A + 1) (A + K),
      (∑ k ∈ S, vonMangoldt k / (k : ℝ) *
        ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
          ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n)) ^ 2) ≤
      ((K : ℝ) + (Q : ℝ) * ((Q : ℝ) - 1)) *
        primeActivityMass Q * primeAdjunctionMass Q a := by
  have hw := (abs_le.mp (abs_ramanujanPacket_window_discrepancy_le hQ
    (primeHeadCoefficient Q a S) A K)).2
  have hframe : (∑ n ∈ Icc (A + 1) (A + K),
      (∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m * normalizedRamanujanMode m n) ^ 2) ≤
      ((K : ℝ) + (Q : ℝ) * ((Q : ℝ) - 1)) *
        ∑ m ∈ Icc 1 Q, primeHeadCoefficient Q a S m ^ 2 := by linarith only [hw]
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hscale : 0 ≤ (K : ℝ) + (Q : ℝ) * ((Q : ℝ) - 1) :=
    add_nonneg (Nat.cast_nonneg K) (mul_nonneg (Nat.cast_nonneg Q) (sub_nonneg.mpr hQ1))
  have h := hframe.trans (mul_le_mul_of_nonneg_left (primeHeadCoefficient_sq_sum_le Q a S) hscale)
  simpa only [primeHeadCoefficient_packet, mul_assoc] using h

#print axioms primeHeadCoefficient_sq_sum_le
#print axioms primeHeadCoefficient_mixed_sq_le
#print axioms primeHead_window_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
