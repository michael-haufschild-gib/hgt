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

#print axioms primePoleWitness_mul_mode
#print axioms primeIncidencePacket_dilation_jump
#print axioms completedPrimeDilationTail_primeWitness_nonneg

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
