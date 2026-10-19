import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-! Pointwise error bounds for literal sieve signals in Ramanujan coordinates. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open BezoutValuationIncidence
set_option autoImplicit false

/-- The arithmetic Ramanujan kernel expands the signal at every natural argument. -/
theorem sieveSeq_ramanujan_expansion (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    sieveSeq N c n = ∑ q ∈ Icc 1 N,
      selbergMultiplesCoord N c q * ramanujanLagCoefficient q n := by
  symm
  calc
    _ = ∑ d ∈ Icc 1 N, c d / (d : ℝ) *
        ∑ q ∈ d.divisors, ramanujanLagCoefficient q n := by
      simp only [selbergMultiplesCoord, sum_filter, sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      have hset : (Icc 1 N).filter (fun q => q ∣ d) = d.divisors := by
        ext q
        simp only [mem_filter, mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hqd⟩
          exact ⟨hqd, by have := (mem_Icc.mp hd).1; omega⟩
        · rintro ⟨hqd, hd0⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hqd (Nat.pos_of_ne_zero hd0),
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans (mem_Icc.mp hd).2⟩, hqd⟩
      rw [← sum_filter, hset, mul_sum]
    _ = sieveSeq N c n := by
      simp only [sum_divisors_ramanujanLagCoefficient, sieveSeq, sum_filter]
      apply sum_congr rfl
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by have := (mem_Icc.mp hd).1; omega : d ≠ 0)
      by_cases hdn : d ∣ n <;> simp [hdn, hd0]

private theorem abs_moebius_ratio_le_one (q : ℕ) :
    |moebiusReal q / (q.totient : ℝ)| ≤ 1 := by
  have hmu : |moebiusReal q| ≤ 1 := by
    unfold moebiusReal
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  by_cases ht : q.totient = 0
  · simp [ht]
  · have ht1 : (1 : ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht)
    rw [abs_div, abs_of_nonneg (a := (q.totient : ℝ)) (Nat.cast_nonneg q.totient)]
    exact (div_le_one (by linarith)).mpr (hmu.trans ht1)

/-- The kernel never exceeds its zero-lag totient value. -/
theorem abs_ramanujanLagCoefficient_le_totient (q n : ℕ) :
    |ramanujanLagCoefficient q n| ≤ (q.totient : ℝ) := by
  rw [ramanujanLagCoefficient_eq_totient_mul,
    sieveLagMultiplier_eq_moebius_totient_quotient, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _)]
  simpa using mul_le_mul_of_nonneg_left
    (abs_moebius_ratio_le_one (q / q.gcd n)) (Nat.cast_nonneg q.totient)

/-- Weighted coordinate error controls the signal uniformly, before or after any shift. -/
theorem sieveSeq_error_le_coordinate_sum (N : ℕ) (c e : ℕ → ℝ) (n : ℕ) :
    |sieveSeq N c n - sieveSeq N e n| ≤
      ∑ q ∈ Icc 1 N, (q.totient : ℝ) *
        |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| := by
  rw [sieveSeq_ramanujan_expansion, sieveSeq_ramanujan_expansion, ← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ q ∈ Icc 1 N,
        |(selbergMultiplesCoord N c q - selbergMultiplesCoord N e q) *
          ramanujanLagCoefficient q n| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro q _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_ramanujanLagCoefficient_le_totient q n)
        (abs_nonneg _)

/-- Uniform coordinate error has an explicit totient-sum amplification constant. -/
theorem sieveSeq_error_le_totient_sum (N : ℕ) (c e : ℕ → ℝ) (η : ℝ)
    (h : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| ≤ η)
    (n : ℕ) : |sieveSeq N c n - sieveSeq N e n| ≤
      (∑ q ∈ Icc 1 N, (q.totient : ℝ)) * η := by
  calc
    _ ≤ ∑ q ∈ Icc 1 N, (q.totient : ℝ) *
        |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| :=
      sieveSeq_error_le_coordinate_sum N c e n
    _ ≤ ∑ q ∈ Icc 1 N, (q.totient : ℝ) * η :=
      sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (h q hq) (Nat.cast_nonneg _)
    _ = _ := (sum_mul _ _ _).symm

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
