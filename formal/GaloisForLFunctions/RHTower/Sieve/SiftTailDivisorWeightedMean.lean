import GaloisForLFunctions.RHTower.Sieve.DivisorSubmultiplicative
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.Sieve.MinorantDecomposition
import GaloisForLFunctions.RHTower.Sieve.TruncationDefect
import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture

/-!
# Divisor-weighted mean for large smooth divisors

The `c₁,n` truncation error exposes a divisor `e > D` of the sifting modulus.  This file retains
that divisor, reindexes its multiples, and preserves the harmonic factor `1/e` under any fixed
power of the divisor function.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Divisors of the sifting modulus discarded above `D`. -/
def largeSiftDivisors (z D : ℕ) : Finset ℕ :=
  (siftModulus z).divisors.filter (fun e => D < e)

/-- Discarded sifting divisors which also divide `n`. -/
def siftTailDivisorSet (z D n : ℕ) : Finset ℕ :=
  (largeSiftDivisors z D).filter (fun e => e ∣ n)

/-- Real cardinality of the discarded smooth divisors of `n`. -/
def siftTailDivisorCount (z D n : ℕ) : ℝ :=
  ((siftTailDivisorSet z D n).card : ℝ)

/-- Indicator-sum form of the tail divisor count. -/
theorem siftTailDivisorCount_eq_sum (z D n : ℕ) :
    siftTailDivisorCount z D n =
      ∑ e ∈ largeSiftDivisors z D, if e ∣ n then 1 else 0 := by
  unfold siftTailDivisorCount siftTailDivisorSet
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

/-- Every divisor discarded from a quotient `k ∣ n` is a discarded smooth divisor of `n`. -/
theorem truncTail_le_siftTailDivisorCount
    {k n z D : ℕ} (hkn : k ∣ n) :
    (truncTail k z D : ℝ) ≤ siftTailDivisorCount z D n := by
  unfold truncTail siftTailDivisorCount siftTailDivisorSet largeSiftDivisors
  have hsubset :
      (Nat.gcd k (siftModulus z)).divisors.filter (fun e => ¬e ≤ D) ⊆
        ((siftModulus z).divisors.filter (fun e => D < e)).filter (fun e => e ∣ n) := by
    intro e he
    rw [Finset.mem_filter, Nat.mem_divisors] at he
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    have heGcd : e ∣ Nat.gcd k (siftModulus z) := he.1.1
    have hePos : 0 < e := Nat.pos_of_dvd_of_pos heGcd (Nat.pos_of_ne_zero he.1.2)
    exact ⟨⟨⟨heGcd.trans (Nat.gcd_dvd_right k (siftModulus z)),
      (siftModulus_pos z).ne'⟩, by omega⟩,
      (heGcd.trans (Nat.gcd_dvd_left k (siftModulus z))).trans hkn⟩
  exact_mod_cast Finset.card_le_card hsubset

/-- Exact floor-scale divisor-moment bound along multiples of an arbitrary positive integer. -/
theorem sum_card_divisors_pow_dvd_le_floorPolylog
    (K Y : ℕ) {e : ℕ} (he : 0 < e) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if e ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      ((e.divisors.card : ℝ) ^ K) * ((Y / e : ℕ) : ℝ) *
        (1 + Real.log ((Y / e : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
  rw [← Finset.sum_filter]
  rw [sum_Icc_dvd_reindex e Y he]
  let N := Y / e
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [N, hN]
  · have hmoment := sum_card_divisors_pow_le_polylog K N hN
    calc
      ∑ k ∈ Finset.Icc 1 N, ((((e * k).divisors.card : ℝ) ^ K)) ≤
          ∑ k ∈ Finset.Icc 1 N,
            ((e.divisors.card : ℝ) ^ K) * ((k.divisors.card : ℝ) ^ K) := by
        apply Finset.sum_le_sum
        intro k hkMem
        exact card_divisors_mul_pow_le K he (by
          rw [Finset.mem_Icc] at hkMem
          omega)
      _ = ((e.divisors.card : ℝ) ^ K) *
          ∑ k ∈ Finset.Icc 1 N, ((k.divisors.card : ℝ) ^ K) := by
        rw [Finset.mul_sum]
      _ ≤ ((e.divisors.card : ℝ) ^ K) *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1)) := by
        exact mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = ((e.divisors.card : ℝ) ^ K) * ((Y / e : ℕ) : ℝ) *
          (1 + Real.log ((Y / e : ℕ) : ℝ)) ^ (2 ^ K - 1) := by
        simp only [N]
        ring

/-- Common-scale form with the harmonic factor of the prescribed divisor exposed. -/
theorem sum_card_divisors_pow_dvd_le_polylog
    (K Y : ℕ) (hY : 1 ≤ Y) {e : ℕ} (he : 0 < e) :
    ∑ n ∈ Finset.Icc 1 Y,
        (if e ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
      ((e.divisors.card : ℝ) ^ K) * ((Y : ℝ) / (e : ℝ)) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
  have hbase := sum_card_divisors_pow_dvd_le_floorPolylog K Y he
  let N := Y / e
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hzero : ∀ n ∈ Finset.Icc 1 Y, ¬e ∣ n := by
      intro n hn hdvd
      have hnpos : 0 < n := by
        rw [Finset.mem_Icc] at hn
        omega
      have hle : e ≤ Y := (Nat.le_of_dvd hnpos hdvd).trans (Finset.mem_Icc.mp hn).2
      have hdiv : 1 ≤ Y / e := (Nat.one_le_div_iff he).mpr hle
      have : 1 ≤ N := by simpa only [N] using hdiv
      omega
    have hlhs : ∑ n ∈ Finset.Icc 1 Y,
        (if e ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [hzero n hn]
    rw [hlhs]
    positivity
  · have hNY : N ≤ Y := Nat.div_le_self Y e
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlog : Real.log (N : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log hNR (by exact_mod_cast hNY)
    have hpow : (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) ≤
        (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      apply pow_le_pow_left₀
      · have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
        linarith
      · linarith
    have hdiv : (N : ℝ) ≤ (Y : ℝ) / (e : ℝ) := Nat.cast_div_le
    have hpoly0 : 0 ≤ (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by positivity
    have hpolyY0 : 0 ≤ (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
      have : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
      positivity
    calc
      ∑ n ∈ Finset.Icc 1 Y,
          (if e ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) ≤
        ((e.divisors.card : ℝ) ^ K) * (N : ℝ) *
          (1 + Real.log (N : ℝ)) ^ (2 ^ K - 1) := by
            simpa only [N] using hbase
      _ ≤ ((e.divisors.card : ℝ) ^ K) * ((Y : ℝ) / (e : ℝ)) *
          (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) := by
        gcongr

/-- Divisor-power weighted count of discarded smooth divisors of `n`. -/
def weightedSiftTailDivisorCount (K z D n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ K * siftTailDivisorCount z D n

/-- Mean bound retaining the weighted harmonic mass of discarded smooth divisors. -/
theorem sum_weightedSiftTailDivisorCount_le
    (K z D Y : ℕ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 Y, weightedSiftTailDivisorCount K z D n ≤
      (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ e ∈ largeSiftDivisors z D,
          ((e.divisors.card : ℝ) ^ K) / (e : ℝ) := by
  let C : ℝ := (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1)
  calc
    ∑ n ∈ Finset.Icc 1 Y, weightedSiftTailDivisorCount K z D n =
        ∑ e ∈ largeSiftDivisors z D, ∑ n ∈ Finset.Icc 1 Y,
          (if e ∣ n then ((n.divisors.card : ℝ) ^ K) else 0) := by
      unfold weightedSiftTailDivisorCount
      simp_rw [siftTailDivisorCount_eq_sum, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ largeSiftDivisors z D,
        C * (((e.divisors.card : ℝ) ^ K) / (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro e heMem
      have heDiv : e ∈ (siftModulus z).divisors :=
        (Finset.mem_filter.mp heMem).1
      have he : 0 < e := Nat.pos_of_mem_divisors heDiv
      have h := sum_card_divisors_pow_dvd_le_polylog K Y hY he
      dsimp [C]
      convert h using 1 <;> try rfl
      ring
    _ = (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ (2 ^ K - 1) *
        ∑ e ∈ largeSiftDivisors z D,
          ((e.divisors.card : ℝ) ^ K) / (e : ℝ) := by
      dsimp [C]
      rw [Finset.mul_sum]

end

end RHTower.Sieve
