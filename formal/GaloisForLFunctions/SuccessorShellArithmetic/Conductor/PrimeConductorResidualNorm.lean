import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorDilationMoments
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicPacketQuotientTails
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.ScalarPrimePacketNorm

set_option autoImplicit false

/-!
# A logarithmic conductor cost for the complete prime residual

Only primes below the conductor cutoff change a packet. Their total reciprocal
Mangoldt mass is logarithmic. The exact dilation square energy and its first
logarithmic moment pay the complementary row tails before the prime cutoff is
removed. The common scalar Mertens residual then completes the literal row.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory SignedArithmeticHodgeTheory
  BezoutValuationIncidence ArithmeticIntersectionTheory CriticalArithmeticCorrelationTheory
  ArithmeticElectrostatics ArithmeticEffectivityTheory

private def primePacketValue (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n

private def primePacketUpTail (Q : ℕ) (a : ℕ → ℝ) (y K n : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 K).filter (fun k => y < k), vonMangoldt k / (k : ℝ) *
    (primePacketValue Q a (k * n) - primePacketValue Q a n)

private def primePacketActive (Q k : ℕ) : Prop :=
  ∃ p ∈ (Icc 1 Q).filter Nat.Prime, p ∣ k

private theorem primePacket_up_eq_zero_of_not_active {Q k : ℕ} (a : ℕ → ℝ)
    (ha : ¬primePacketActive Q k) (n : ℕ) :
    vonMangoldt k / (k : ℝ) *
      (primePacketValue Q a (k * n) - primePacketValue Q a n) = 0 := by
  by_cases hΛ : vonMangoldt k = 0
  · rw [hΛ, zero_div, zero_mul]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff k).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hQp : Q < p := by
    by_contra h
    apply ha
    exact ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos, Nat.le_of_not_gt h⟩, hp⟩,
      dvd_pow_self p hj.ne'⟩
  have hz : primePacketValue Q a (p ^ j * n) - primePacketValue Q a n = 0 := by
    rw [primePacketValue, primePacketValue, ← primeConductorDilationJump_packet]
    apply sum_eq_zero
    intro m hm
    rw [primeConductorDilationJump_eq_zero_of_prime_gt a hp hQp hm j, zero_mul]
  rw [hz, mul_zero]

private theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * x i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * x i ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * x i)
  have h1 : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * x i)) =
      ∑ i ∈ S, w i * x i := by
    apply sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i hi)]
  have h2 : (∑ i ∈ S, Real.sqrt (w i) ^ 2) = ∑ i ∈ S, w i := by
    exact sum_congr rfl fun i hi => Real.sq_sqrt (hw i hi)
  have h3 : (∑ i ∈ S, (Real.sqrt (w i) * x i) ^ 2) =
      ∑ i ∈ S, w i * x i ^ 2 := by
    apply sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [h1, h2, h3] at h

private theorem sum_activePrimeMass_le {Q : ℕ} (hQ : 1 ≤ Q) (S : Finset ℕ)
    (hS : ∀ k ∈ S, primePacketActive Q k) :
    (∑ k ∈ S, vonMangoldt k / (k : ℝ)) ≤ 14 * (1 + Real.log Q) := by
  have hpoint (k : ℕ) (hk : k ∈ S) :
      vonMangoldt k / (k : ℝ) ≤
        ∑ p ∈ (Icc 1 Q).filter Nat.Prime, localMangoldtMass p k := by
    obtain ⟨p, hp, hpk⟩ := hS k hk
    have h := single_le_sum (fun p _ => localMangoldtMass_nonneg p k) hp
    simpa only [localMangoldtMass, if_pos hpk] using h
  calc
    _ ≤ ∑ k ∈ S, ∑ p ∈ (Icc 1 Q).filter Nat.Prime, localMangoldtMass p k := sum_le_sum hpoint
    _ = ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ k ∈ S, localMangoldtMass p k := sum_comm
    _ ≤ ∑ p ∈ (Icc 1 Q).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) :=
      sum_le_sum fun p hp => sum_dvd_vonMangoldt_div_le (mem_filter.mp hp).2 S
    _ ≤ _ := sum_primeDilationMass_le_log hQ

private theorem primePacketUpTail_sq_le {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (y K n : ℕ) :
    primePacketUpTail Q a y K n ^ 2 ≤ 14 * (1 + Real.log Q) *
      ∑ k ∈ (Icc 1 K).filter (fun k => y < k), vonMangoldt k / (k : ℝ) *
        (primePacketValue Q a (k * n) - primePacketValue Q a n) ^ 2 := by
  classical
  let T := (Icc 1 K).filter (fun k => y < k)
  let S := T.filter (primePacketActive Q)
  have heq : primePacketUpTail Q a y K n = ∑ k ∈ S, vonMangoldt k / (k : ℝ) *
      (primePacketValue Q a (k * n) - primePacketValue Q a n) := by
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro k hk hnot
    have ha : ¬primePacketActive Q k := by
      intro ha
      exact hnot (mem_filter.mpr ⟨hk, ha⟩)
    exact primePacket_up_eq_zero_of_not_active a ha n
  have hmass := sum_activePrimeMass_le hQ S (fun k hk => (mem_filter.mp hk).2)
  have henergy : (∑ k ∈ S, vonMangoldt k / (k : ℝ) *
      (primePacketValue Q a (k * n) - primePacketValue Q a n) ^ 2) ≤
      ∑ k ∈ T, vonMangoldt k / (k : ℝ) *
        (primePacketValue Q a (k * n) - primePacketValue Q a n) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
      mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) (sq_nonneg _)
  rw [heq]
  exact (weighted_sum_sq_le S (fun k => vonMangoldt k / (k : ℝ))
    (fun k => primePacketValue Q a (k * n) - primePacketValue Q a n)
    (fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans
    (mul_le_mul hmass henergy
      (sum_nonneg fun k _ => mul_nonneg
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)) (sq_nonneg _))
      (by positivity))

private theorem nat_quotient_lt_iff_real {N n k : ℕ} (hn : 0 < n) :
    N / n < k ↔ (N : ℝ) / n < k := by
  rw [Nat.div_lt_iff_lt_mul hn, div_lt_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  exact_mod_cast (Iff.rfl : N < k * n ↔ N < k * n)

private theorem jumpPacket_quotient_tail_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ n ∈ (Icc 1 N).filter (fun n => N / n < k),
      (primePacketValue Q a (k * n) - primePacketValue Q a n) ^ 2 / (n : ℝ)) ≤
      (18 * (1 + Real.log Q) + Real.log k) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
  have hset : (Icc 1 N).filter (fun n => N / n < k) =
      (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < k) := by
    apply filter_congr
    intro n hn
    exact nat_quotient_lt_iff_real (mem_Icc.mp hn).1
  have htail := harmonicConductorPacket_quotient_tail_le hQ hN
    (by exact_mod_cast hk : (1 : ℝ) ≤ k) (primeConductorDilationJump Q a k)
  have hcoef : 1 + Real.log (2 * (k : ℝ)) + 2 * (6 * Real.log Q + Real.log 4 + 5) ≤
      18 * (1 + Real.log Q) + Real.log k := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (Nat.ne_of_gt hk) : (k : ℝ) ≠ 0)]
    have htwo := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith only [htwo, hfour, Real.log_natCast_nonneg Q]
  rw [hset]
  simp only [primeConductorDilationJump_packet] at htail
  exact htail.trans (mul_le_mul_of_nonneg_right hcoef (sum_nonneg fun _ _ => sq_nonneg _))

private theorem adjunctionPacket_le_log (Q : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2) ≤
      2 * (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  have hlog : Real.log (m : ℝ) ≤ Real.log Q := Real.log_le_log
    (by exact_mod_cast (mem_Icc.mp hm).1 : (0 : ℝ) < m)
    (by exact_mod_cast (mem_Icc.mp hm).2)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith only [hlog, tameDifferent_le_log (mem_Icc.mp hm).1]

private theorem weighted_dilation_energy_le {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ((18 * (1 + Real.log Q) + Real.log k) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2)) ≤
      38 * (1 + Real.log Q) ^ 2 * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let L := ∑ m ∈ Icc 1 Q, (Real.log m + tameDifferent m) * a m ^ 2
  let b := fun k => ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2
  have hsum := hasSum_primeConductorDilationJump_sq Q a
  change HasSum (fun k : ℕ => vonMangoldt k / (k : ℝ) * b k) L at hsum
  have henergy : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * b k) ≤ L := by
    have h := hsum.summable.sum_le_tsum (Icc 1 K) (fun k _ =>
      mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
        (sum_nonneg fun _ _ => sq_nonneg _))
    rwa [hsum.tsum_eq] at h
  have hmoment := sum_primeConductorDilationJump_logMoment_le hQ a K
  have hH : 0 ≤ 1 + Real.log Q := by positivity
  have heq : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ((18 * (1 + Real.log Q) + Real.log k) * b k)) =
      18 * (1 + Real.log Q) * (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * b k) +
        ∑ k ∈ Icc 1 K, vonMangoldt k * Real.log k / (k : ℝ) * b k := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  change (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
    ((18 * (1 + Real.log Q) + Real.log k) * b k)) ≤ _
  rw [heq]
  calc
    _ ≤ 18 * (1 + Real.log Q) * L + (1 + Real.log Q) * L :=
      add_le_add (mul_le_mul_of_nonneg_left henergy (by positivity)) hmoment
    _ = 19 * (1 + Real.log Q) * L := by ring
    _ ≤ 19 * (1 + Real.log Q) *
        (2 * (1 + Real.log Q) * ∑ m ∈ Icc 1 Q, a m ^ 2) :=
      mul_le_mul_of_nonneg_left (adjunctionPacket_le_log Q a) (by positivity)
    _ = _ := by ring

private theorem primePacketUpTail_norm_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Icc 1 N, primePacketUpTail Q a (N / n) K n ^ 2 / (n : ℝ)) ≤
      532 * (1 + Real.log Q) ^ 3 * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let F := primePacketValue Q a
  have hH : 0 ≤ 14 * (1 + Real.log Q) := by positivity
  have hrow : (∑ n ∈ Icc 1 N, primePacketUpTail Q a (N / n) K n ^ 2 / (n : ℝ)) ≤
      14 * (1 + Real.log Q) *
        ∑ n ∈ Icc 1 N, ∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
          vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    have h := div_le_div_of_nonneg_right (primePacketUpTail_sq_le (by omega : 1 ≤ Q) a (N / n) K n)
      (Nat.cast_nonneg n)
    simpa only [F, sum_div, mul_div_assoc] using h
  -- Each prime jump pays only the rows beyond its complementary quotient.
  have hswap : (∑ n ∈ Icc 1 N, ∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
      vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ)) =
      ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ∑ n ∈ (Icc 1 N).filter (fun n => N / n < k), (F (k * n) - F n) ^ 2 / (n : ℝ) := by
    simp only [sum_filter, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  have htail : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ∑ n ∈ (Icc 1 N).filter (fun n => N / n < k), (F (k * n) - F n) ^ 2 / (n : ℝ)) ≤
      ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ((18 * (1 + Real.log Q) + Real.log k) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) :=
    sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
      (jumpPacket_quotient_tail_le hQ hN a (mem_Icc.mp hk).1)
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  rw [hswap] at hrow
  exact (hrow.trans (mul_le_mul_of_nonneg_left
    (htail.trans (weighted_dilation_energy_le (by omega : 1 ≤ Q) a K)) hH)).trans_eq (by ring)

private def primePacketCompletedTail (Q : ℕ) (a : ℕ → ℝ) (y n : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 Q, a m *
    (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
      (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) -
    ∑ k ∈ Icc 1 y, vonMangoldt k / (k : ℝ) *
      (primePacketValue Q a (k * n) - primePacketValue Q a n)

private theorem tendsto_primePacketUpTail (Q : ℕ) (a : ℕ → ℝ) (y n : ℕ) :
    Tendsto (fun K => primePacketUpTail Q a y K n) atTop
      (𝓝 (primePacketCompletedTail Q a y n)) := by
  let g : ℕ → ℝ := fun k => vonMangoldt k / (k : ℝ) *
    (primePacketValue Q a (k * n) - primePacketValue Q a n)
  have h := ((hasSum_normalizedRamanujanPacket_up Q a n).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)).sub_const (∑ k ∈ Icc 1 y, g k)
  change Tendsto (fun K => (∑ k ∈ range (K + 1), g k) - ∑ k ∈ Icc 1 y, g k)
    atTop (𝓝 (primePacketCompletedTail Q a y n)) at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop y] with K hK
  have hrange : range (K + 1) =
      insert 0 (Icc 1 y ∪ (Icc 1 K).filter (fun k => y < k)) := by
    ext k
    simp only [mem_range, mem_insert, mem_union, mem_filter, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 y) ((Icc 1 K).filter (fun k => y < k)) := by
    rw [disjoint_left]
    intro k hk hyk
    have := (mem_Icc.mp hk).2
    have := (mem_filter.mp hyk).2
    omega
  have hzero : (0 : ℕ) ∉ Icc 1 y ∪ (Icc 1 K).filter (fun k => y < k) := by
    simp only [mem_union, mem_Icc, mem_filter]
    omega
  rw [hrange, sum_insert hzero, sum_union hdisj]
  have hg0 : g 0 = 0 := by simp only [g, Nat.cast_zero, div_zero, zero_mul]
  rw [hg0, zero_add]
  change (∑ k ∈ Icc 1 y, g k) +
    (∑ k ∈ (Icc 1 K).filter (fun k => y < k), g k) - (∑ k ∈ Icc 1 y, g k) =
      ∑ k ∈ (Icc 1 K).filter (fun k => y < k), g k
  ring

private theorem primePacketCompletedTail_norm_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, primePacketCompletedTail Q a (N / n) n ^ 2 / (n : ℝ)) ≤
      532 * (1 + Real.log Q) ^ 3 * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hlim : Tendsto
      (fun K => ∑ n ∈ Icc 1 N, primePacketUpTail Q a (N / n) K n ^ 2 / (n : ℝ)) atTop
      (𝓝 (∑ n ∈ Icc 1 N, primePacketCompletedTail Q a (N / n) n ^ 2 / (n : ℝ))) :=
    tendsto_finsetSum _ fun n _ => ((tendsto_primePacketUpTail Q a (N / n) n).pow 2).div_const n
  exact le_of_tendsto hlim (Eventually.of_forall (primePacketUpTail_norm_le hQ hN a))

private theorem normalized_correction_eq_up_sub_jet {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (y : ℕ) :
    poleProfileCorrection (normalizedRamanujanMode m) y n =
      (∑ k ∈ Icc 1 y, vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
      ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) := by
  have hg : normalizedRamanujanMode m =
      fun j => ramanujanLagCoefficient m j / Real.sqrt (m.totient : ℝ) :=
    funext (normalizedRamanujanMode_eq_coefficient hm)
  rw [hg, poleProfileCorrection_div, poleProfileCorrection_eq_divisor_jumps]
  change ((∑ k ∈ Icc 1 y,
    (ramanujanLagCoefficient m (n * k) - ramanujanLagCoefficient m n) * vonMangoldt k / (k : ℝ)) +
      ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) = _
  rw [ramanujanDownCorrection_eq_neg_logDivisorJet m hn, add_div, neg_div, ← sub_eq_add_neg]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  rw [Nat.mul_comm n k]
  ring

private theorem primeResidual_mode_eq {m N n : ℕ} (hm : 0 < m) (hn : n ∈ Icc 1 N) :
    ramanujanPrimeResidual m N n =
      ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
          normalizedRamanujanMode m n +
        (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
          (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n := by
  rw [ramanujanPrimeResidual]
  simp only [ramanujanPoleProfile_eq_mul_poleVector]
  rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m)
    (mem_Icc.mp hn).1 (mem_Icc.mp hn).2,
    normalized_correction_eq_up_sub_jet hm (mem_Icc.mp hn).1]
  dsimp only [ramanujanAdjunctionEnergy]
  ring

private theorem primeResidual_packet_eq {Q N n : ℕ} (a : ℕ → ℝ) (hn : n ∈ Icc 1 N) :
    (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) =
      ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
        primePacketValue Q a n - primePacketCompletedTail Q a (N / n) n) * poleVector n := by
  have hsum : (∑ m ∈ Icc 1 Q, a m *
      (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))) =
      ∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
        (primePacketValue Q a (k * n) - primePacketValue Q a n) := by
    simp only [primePacketValue, mul_sum, ← sum_sub_distrib]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro m _
    ring
  calc
    _ = (∑ m ∈ Icc 1 Q, a m *
        ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
            normalizedRamanujanMode m n +
          (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
            (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
          (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n))) * poleVector n := by
      rw [sum_mul]
      apply sum_congr rfl
      intro m hm
      rw [primeResidual_mode_eq (mem_Icc.mp hm).1 hn]
      ring
    _ = ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
        primePacketValue Q a n +
        (∑ m ∈ Icc 1 Q, a m *
          (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
            (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))) -
        (∑ m ∈ Icc 1 Q, a m *
          (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n))) * poleVector n := by
      congr 1
      rw [primePacketValue, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro m _
      ring
    _ = _ := by rw [hsum, primePacketCompletedTail]; ring

/-- The literal full prime residual has a cubic logarithmic conductor cost, uniformly in every horizon. -/
theorem exists_primeResidual_packet_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N ≤
        C * (1 + Real.log Q) ^ 3 / Real.log N * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  obtain ⟨C, hC, hscalar⟩ := exists_scalarPrimeResidual_packet_sq_le
  refine ⟨2 * C + 1064, by positivity, ?_⟩
  intro Q N hQ hN a
  let M := ∑ m ∈ Icc 1 Q, a m ^ 2
  let H := 1 + Real.log (Q : ℝ)
  let r : ℕ → ℝ := fun n => mertensSum (N / n) + Real.log n -
    (Real.log N - Real.eulerMascheroniConstant)
  have hM : 0 ≤ M := sum_nonneg fun _ _ => sq_nonneg _
  have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg Q)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHcube : H ≤ H ^ 3 := by
    have h := mul_nonneg (show 0 ≤ H * (H + 1) by positivity) (sub_nonneg.mpr hH)
    nlinarith only [h]
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2 ≤
        2 * (r n ^ 2 * primePacketValue Q a n ^ 2 / (n : ℝ)) +
          2 * (primePacketCompletedTail Q a (N / n) n ^ 2 / (n : ℝ)) := by
    rw [primeResidual_packet_eq a hn, mul_pow, poleVector, div_pow, one_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), mul_one_div]
    have hsq : (r n * primePacketValue Q a n - primePacketCompletedTail Q a (N / n) n) ^ 2 ≤
        2 * (r n ^ 2 * primePacketValue Q a n ^ 2) +
          2 * primePacketCompletedTail Q a (N / n) n ^ 2 := by
      nlinarith only [sq_nonneg (r n * primePacketValue Q a n +
        primePacketCompletedTail Q a (N / n) n)]
    exact (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)).trans_eq (by ring)
  have hsplit := div_le_div_of_nonneg_right (sum_le_sum hrow) hlog.le
  simp only [sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] at hsplit
  have hs : (∑ n ∈ Icc 1 N, r n ^ 2 * (primePacketValue Q a n ^ 2 / (n : ℝ))) /
      Real.log N ≤ C * H / Real.log N * M := by
    simpa only [r, primePacketValue, H, M, mul_div_assoc] using hscalar Q N hQ hN a
  have ht := div_le_div_of_nonneg_right
    (primePacketCompletedTail_norm_le hQ (by omega : 1 ≤ N) a) hlog.le
  have hsc : C * H / Real.log N * M ≤ C * H ^ 3 / Real.log N * M :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHcube hC.le) hlog.le) hM
  calc
    _ ≤ 2 * (C * H ^ 3 / Real.log N * M) + 2 * (532 * H ^ 3 * M / Real.log N) :=
      hsplit.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hs.trans hsc) (by norm_num))
        (mul_le_mul_of_nonneg_left ht (by norm_num)))
    _ = _ := by dsimp only [H, M]; ring

#print axioms exists_primeResidual_packet_sq_le

end GaloisForLFunctions.SuccessorShellArithmetic
