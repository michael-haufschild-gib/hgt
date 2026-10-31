import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeGeneratorPole

/-!
# Prime incidence coordinates for the actual dilation source

Rescaling a prime conductor by `sqrt(p-1)/p` turns it into the centered
divisibility indicator `1_(p∣n)-1/p`. Its dilation jump is exactly the
incidence event `p∣k` and `p∤n`. This gives a positive arithmetic cone
and a nonnegative complementary prime tail without an analytic assumption.
-/

noncomputable section

open Finset Filter Topology ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  SuccessorShellArithmetic CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory

/-- Prime coefficients whose packet is a linear combination of centered divisibility indicators. -/
def primeIncidenceCoefficients (b : ℕ → ℝ) : ℕ → ℝ :=
  primeOnly (fun p => primePoleWitness p * b p)

theorem normalizedConductorPacket_primeOnly (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q (primeOnly a) n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, a p * normalizedRamanujanMode p n := by
  rw [normalizedConductorPacket, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp only [primeOnly, if_pos hp]
  · simp only [primeOnly, if_neg hp, zero_mul]

/-- A prime conductor has only its divisible and nondivisible values. -/
theorem ramanujanCoefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramanujanLagCoefficient p n = if p ∣ n then (p : ℝ) - 1 else -1 := by
  by_cases hn : p ∣ n
  · rw [if_pos hn, ramanujanLagCoefficient_of_dvd hn, Nat.totient_prime hp,
      Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  · rw [if_neg hn]
    simpa only [pow_zero, Nat.zero_add, pow_one] using
      ramanujanLagCoefficient_prime_pow_critical (a := 0) hp
        (by simpa only [pow_zero] using one_dvd n) (by simpa only [Nat.zero_add, pow_one] using hn)

/-- The coherent prime coefficient is exactly a centered divisibility indicator. -/
theorem primePoleWitness_mul_mode {p : ℕ} (hp : p.Prime) (n : ℕ) :
    primePoleWitness p * normalizedRamanujanMode p n =
      (if p ∣ n then 1 else 0) - 1 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs : Real.sqrt (p.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hp.pos)).ne'
  have he : primePoleWitness p * normalizedRamanujanMode p n =
      ramanujanLagCoefficient p n / (p : ℝ) := by
    rw [primePoleWitness, normalizedRamanujanMode_eq_coefficient hp.pos]
    field_simp [hp0, hs]
  rw [he, ramanujanCoefficient_prime hp]
  by_cases hn : p ∣ n
  · rw [if_pos hn, if_pos hn]
    field_simp [hp0]
  · simp only [if_neg hn, zero_sub, neg_div]

/-- A prime incidence packet retains its literal divisibility statistics. -/
theorem primeIncidencePacket_eq (Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    normalizedConductorPacket Q (primeIncidenceCoefficients b) n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, b p * ((if p ∣ n then 1 else 0) - 1 / (p : ℝ)) := by
  rw [primeIncidenceCoefficients, normalizedConductorPacket_primeOnly]
  apply sum_congr rfl
  intro p hp
  rw [mul_right_comm, primePoleWitness_mul_mode (mem_filter.mp hp).2]
  ring

/-- Dilation of a prime incidence mode is a nonnegative arithmetic event. -/
theorem primePoleWitness_dilation_jump {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    primePoleWitness p * (normalizedRamanujanMode p (k * n) - normalizedRamanujanMode p n) =
      if p ∣ k ∧ ¬p ∣ n then 1 else 0 := by
  rw [mul_sub, primePoleWitness_mul_mode hp, primePoleWitness_mul_mode hp]
  by_cases hk : p ∣ k <;> by_cases hn : p ∣ n <;> simp [hp.dvd_mul, hk, hn]

/-- The packet jump is the exact prime-divisor incidence sum, with every coefficient retained. -/
theorem primeIncidencePacket_dilation_jump (Q : ℕ) (b : ℕ → ℝ) (k n : ℕ) :
    normalizedConductorPacket Q (primeIncidenceCoefficients b) (k * n) -
      normalizedConductorPacket Q (primeIncidenceCoefficients b) n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, if p ∣ k ∧ ¬p ∣ n then b p else 0 := by
  rw [primeIncidenceCoefficients, normalizedConductorPacket_primeOnly,
    normalizedConductorPacket_primeOnly, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  calc
    _ = b p * (primePoleWitness p *
        (normalizedRamanujanMode p (k * n) - normalizedRamanujanMode p n)) := by ring
    _ = _ := by
      rw [primePoleWitness_dilation_jump (mem_filter.mp hp).2]
      split_ifs <;> ring

/-- The explicit coherent prime witness has nonnegative jumps under every integer dilation. -/
theorem primeWitnessPacket_dilation_nonneg (Q k n : ℕ) :
    0 ≤ normalizedConductorPacket Q (primeOnly primePoleWitness) (k * n) -
      normalizedConductorPacket Q (primeOnly primePoleWitness) n := by
  have h := primeIncidencePacket_dilation_jump Q (fun _ => 1) k n
  simp only [primeIncidenceCoefficients, mul_one] at h
  rw [h]
  exact sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- Every complementary cutoff of the literal coherent prime source remains nonnegative. -/
theorem completedPrimeDilationTail_primeWitness_nonneg (Q y n : ℕ) :
    0 ≤ completedPrimeDilationTail Q (primeOnly primePoleWitness) y n := by
  have hfinite (K : ℕ) : 0 ≤ finitePrimeDilationTail Q (primeOnly primePoleWitness) y K n :=
    sum_nonneg fun k _ => mul_nonneg
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      (primeWitnessPacket_dilation_nonneg Q k n)
  have hlim := (tendsto_finitePrimeDilationTail Q (primeOnly primePoleWitness) y n).neg
  have h := le_of_tendsto hlim (Eventually.of_forall fun K => neg_nonpos.mpr (hfinite K))
  exact neg_nonpos.mp h

/-- The prime divisor jet has one constant row and one prime row. -/
theorem ramanujanDivisorJet_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramanujanLogDivisorJet p n = Real.log p * (ramanujanLagCoefficient p n + 1) := by
  have h1 : ramanujanLagCoefficient 1 n = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using
      ramanujanLagCoefficient_of_dvd (one_dvd n)
  rw [ramanujanLogDivisorJet_eq_weighted_conductors hp.pos, hp.divisors,
    sum_pair (Ne.symm hp.ne_one)]
  simp only [ramanujanJetConductorWeight, if_neg (Ne.symm hp.ne_one), ite_true,
    Nat.div_one, Nat.div_self hp.pos, vonMangoldt_apply_prime hp, vonMangoldt_apply_one,
    zero_add, add_zero, h1, mul_one]
  ring

private theorem primeIncidence_generator_term {p : ℕ} (hp : p.Prime) (b : ℝ) (n : ℕ) :
    (primePoleWitness p * b) *
      (ramanujanLogDivisorJet p n / Real.sqrt (p.totient : ℝ) -
        (Real.log p + tameDifferent p) * normalizedRamanujanMode p n) =
      if p ∣ n then 0 else b * Real.log p / ((p : ℝ) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hpR).ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hs : Real.sqrt ((p : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hpR)).ne'
  have ht := tameDifferent_prime_pow hp (show (1 : ℕ) ≠ 0 by decide)
  simp only [pow_one] at ht
  rw [ramanujanDivisorJet_prime hp, normalizedRamanujanMode_eq_coefficient hp.pos,
    primePoleWitness, ht, Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one,
    ramanujanCoefficient_prime hp]
  by_cases hn : p ∣ n
  · simp only [if_pos hn]
    field_simp [hp0, hp1, hs]
    ring
  · simp only [if_neg hn]
    field_simp [hp0, hp1, hs]
    ring

/-- The full generator on prime incidence coordinates is an explicit nondivisibility sum. -/
theorem primeIncidenceGenerator_eq (Q : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    arithmeticPrimeGenerator Q (primeIncidenceCoefficients b) n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if p ∣ n then 0 else b p * Real.log p / ((p : ℝ) - 1) := by
  rw [arithmeticPrimeGenerator_eq_jet, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · rw [primeIncidenceCoefficients, primeOnly, if_pos hp, if_pos hp]
    exact primeIncidence_generator_term hp (b p) n
  · simp only [primeIncidenceCoefficients, primeOnly, if_neg hp, zero_mul]

/-- The remaining reciprocal Mangoldt mass in one prime tower. -/
def primeTowerRemainder (p y : ℕ) : ℝ :=
  Real.log p / ((p : ℝ) - 1) -
    ∑ k ∈ Icc 1 y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0

theorem primeTowerRemainder_nonneg {p : ℕ} (hp : p.Prime) (y : ℕ) :
    0 ≤ primeTowerRemainder p y :=
  sub_nonneg.mpr (sum_dvd_vonMangoldt_div_le hp (Icc 1 y))

/-- A cutoff below the prime has not removed any part of its tower. -/
theorem primeTowerRemainder_eq_of_lt {p y : ℕ} (hy : y < p) :
    primeTowerRemainder p y = Real.log p / ((p : ℝ) - 1) := by
  have hzero : (∑ k ∈ Icc 1 y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0) = 0 := by
    apply sum_eq_zero
    intro k hk
    have hpk : ¬p ∣ k := by
      intro h
      have hle := Nat.le_of_dvd (mem_Icc.mp hk).1 h
      have hky := (mem_Icc.mp hk).2
      omega
    rw [if_neg hpk]
  rw [primeTowerRemainder, hzero, sub_zero]

/-- The complementary prime tail has exact positive tower coefficients in incidence coordinates. -/
theorem completedPrimeDilationTail_primeIncidence_eq (Q : ℕ) (b : ℕ → ℝ) (y n : ℕ) :
    completedPrimeDilationTail Q (primeIncidenceCoefficients b) y n =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if p ∣ n then 0 else b p * primeTowerRemainder p y := by
  have hhead : (∑ k ∈ Icc 1 y, vonMangoldt k / (k : ℝ) *
      (normalizedConductorPacket Q (primeIncidenceCoefficients b) (k * n) -
        normalizedConductorPacket Q (primeIncidenceCoefficients b) n)) =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
        if p ∣ n then 0 else b p *
          ∑ k ∈ Icc 1 y, if p ∣ k then vonMangoldt k / (k : ℝ) else 0 := by
    calc
      _ = ∑ k ∈ Icc 1 y, ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
          vonMangoldt k / (k : ℝ) * (if p ∣ k ∧ ¬p ∣ n then b p else 0) := by
        apply sum_congr rfl
        intro k _
        rw [primeIncidencePacket_dilation_jump, mul_sum]
      _ = ∑ p ∈ (Icc 1 Q).filter Nat.Prime, ∑ k ∈ Icc 1 y,
          vonMangoldt k / (k : ℝ) * (if p ∣ k ∧ ¬p ∣ n then b p else 0) := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro p _
        by_cases hn : p ∣ n
        · simp only [hn, not_true_eq_false, and_false, if_false, mul_zero, sum_const_zero, if_true]
        · rw [if_neg hn, mul_sum]
          apply sum_congr rfl
          intro k _
          by_cases hk : p ∣ k <;> simp [hk, hn, mul_comm]
  rw [completedPrimeDilationTail, ← arithmeticPrimeGenerator_eq_jet,
    primeIncidenceGenerator_eq, hhead, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hn : p ∣ n
  · simp only [if_pos hn, sub_self]
  · simp only [if_neg hn, primeTowerRemainder]
    ring

/-- The high-prime part of the coherent arithmetic generator. -/
def highPrimeCoherentSource (P Q n : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime,
    if P < p then (if p ∣ n then 0 else Real.log p / ((p : ℝ) - 1)) else 0

theorem highPrimeCoherentSource_nonneg (P Q n : ℕ) :
    0 ≤ highPrimeCoherentSource P Q n := by
  apply sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.log_natCast_nonneg p) (sub_nonneg.mpr hp1.le)
  · exact le_rfl

/-- Primes beyond the complementary quotient contribute their complete positive towers. -/
theorem highPrimeCoherentSource_le_completedTail {P y : ℕ} (hy : y ≤ P) (Q n : ℕ) :
    highPrimeCoherentSource P Q n ≤
      completedPrimeDilationTail Q (primeOnly primePoleWitness) y n := by
  have heq := completedPrimeDilationTail_primeIncidence_eq Q (fun _ => 1) y n
  simp only [primeIncidenceCoefficients, mul_one, one_mul] at heq
  rw [heq, highPrimeCoherentSource]
  apply sum_le_sum
  intro p hp
  by_cases hP : P < p
  · rw [if_pos hP, primeTowerRemainder_eq_of_lt (hy.trans_lt hP)]
  · rw [if_neg hP]
    by_cases hn : p ∣ n
    · rw [if_pos hn]
    · rw [if_neg hn]
      exact primeTowerRemainder_nonneg (mem_filter.mp hp).2 y

#print axioms primePoleWitness_mul_mode
#print axioms primeIncidencePacket_dilation_jump
#print axioms completedPrimeDilationTail_primeWitness_nonneg
#print axioms primeIncidenceGenerator_eq
#print axioms completedPrimeDilationTail_primeIncidence_eq
#print axioms highPrimeCoherentSource_le_completedTail

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
