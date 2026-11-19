import GaloisForLFunctions.RHTower.PrimeSquareMobiusDensityFracture
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# Sampling a prime-divisor test beyond its period

Möbius inversion writes an arbitrary bounded test of the complete local gcd
as a sum over divisibility indicators. Each sharp floor error is at most
the smaller of one and the expected number of multiples. Interpolating
these two bounds gives an Euler-product error independent of the test.
-/

noncomputable section

open Finset
open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def patternCoefficient (f : ℕ → ℝ) (d : ℕ) :=
  ∑ b ∈ d.divisors, (μ (d/b):ℝ)*f b

private theorem recover_test (f : ℕ → ℝ) :
    ∀ m > 0, ∑ d ∈ (m:ℕ).divisors, patternCoefficient f d=f m := by
  apply ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr
  intro n _
  exact Nat.sum_divisorsAntidiagonal' (fun a b => (μ a:ℝ)*f b)

private theorem coefficient_bound {f : ℕ → ℝ} (hf : ∀ d, |f d| ≤ 1) (d : ℕ) :
    |patternCoefficient f d| ≤ d.divisors.card := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _b ∈ d.divisors, (1:ℝ) := by
         apply sum_le_sum
         intro b _
         rw [abs_mul]
         have hμ : |(μ (d/b):ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d/b)
         simpa only [one_mul] using mul_le_mul hμ (hf b) (abs_nonneg _) zero_le_one
       _ = _ := by simp

/-- The arithmetic mean of a divisor test in a complete period. -/
def primePatternMean (M : ℕ) (f : ℕ → ℝ) :=
  ∑ d ∈ M.divisors, patternCoefficient f d/(d:ℝ)

private theorem gcd_test_expansion {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, f (n.gcd M) = ∑ d ∈ M.divisors, patternCoefficient f d*((X/d:ℕ):ℝ) := by
  have indicators (n : ℕ) : f (n.gcd M) =
      ∑ d ∈ M.divisors, if d ∣ n then patternCoefficient f d else 0 := by
    have hg : 0 < n.gcd M := Nat.gcd_pos_of_pos_right _ hM
    have he : (n.gcd M).divisors = M.divisors.filter (· ∣ n) := by
      ext d
      simp only [Nat.mem_divisors,mem_filter,Nat.dvd_gcd_iff]
      exact ⟨fun h => ⟨⟨h.1.2,hM.ne'⟩,h.1.1⟩,fun h => ⟨⟨h.2,h.1.1⟩,hg.ne'⟩⟩
    rw [←recover_test f _ hg,he,sum_filter]
  rw [sum_congr rfl (fun n _ => indicators n),sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  rw [←sum_filter,RHTower.sum_Icc_dvd_reindex d X hd0]
  simp [mul_comm]

/-- The divisor mean agrees exactly with counting through a full period. -/
theorem complete_prime_pattern_mean {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 M, f (n.gcd M) = (M:ℝ)*primePatternMean M f := by
  rw [gcd_test_expansion hM,primePatternMean,mul_sum]
  apply sum_congr rfl
  intro d hd
  have hd0 : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hmul : ((M/d:ℕ):ℝ)*d=M := by exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  field_simp [hd0.ne']
  linear_combination (patternCoefficient f d)*hmul

/-- A complete residue system may include zero or the upper endpoint. -/
theorem full_period_prime_pattern {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    ∑ n ∈ range M, f (n.gcd M) = (M:ℝ)*primePatternMean M f := by
  rw [←complete_prime_pattern_mean hM f]
  let S := Ioo 0 M
  have hr : range M=insert 0 S := by
    ext n
    simp only [S,mem_range,mem_insert,mem_Ioo]
    omega
  have hi : Icc 1 M=insert M S := by
    ext n
    simp only [S,mem_Icc,mem_insert,mem_Ioo]
    omega
  have hz : 0 ∉ S := fun h => (mem_Ioo.mp h).1.false
  have hu : M ∉ S := fun h => (mem_Ioo.mp h).2.false
  rw [hr,hi,sum_insert hz,sum_insert hu,Nat.gcd_zero_left,Nat.gcd_self]

private theorem floor_cost {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (X d : ℕ) (hd : 0 < d) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/d| ≤ (X:ℝ)^s/(d:ℝ)^s := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hlo : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/d :=
    (le_div_iff₀ hd0).2 (by exact_mod_cast Nat.div_mul_le_self X d)
  rw [abs_of_nonpos (sub_nonpos.mpr hlo),neg_sub,←Real.div_rpow (Nat.cast_nonneg _) hd0.le]
  by_cases ht : (X:ℝ)/d ≤ 1
  · exact (sub_le_self _ (Nat.cast_nonneg _)).trans
      (Real.self_le_rpow_of_le_one (div_nonneg (Nat.cast_nonneg _) hd0.le) ht hs1)
  · have hrem := Nat.mod_lt X hd
    have hsplit := Nat.mod_add_div X d
    have hupper : X < (X/d+1)*d := by
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (X/d)]
      omega
    have hreal : (X:ℝ)/d < ((X/d:ℕ):ℝ)+1 := (div_lt_iff₀ hd0).2 (by exact_mod_cast hupper)
    exact (by linarith only [hreal] : (X:ℝ)/d-((X/d:ℕ):ℝ) ≤ 1).trans
      (Real.one_le_rpow (le_of_not_ge ht) hs)

/-- A uniform bound for sampling *every* bounded function of the prime
divisibility pattern at a sharp prefix. The modulus may exceed the cutoff. -/
theorem prime_pattern_sampling {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℝ} (hf : ∀ d, |f d| ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (X : ℕ) :
    let M := ∏ p ∈ P, p
    |(∑ n ∈ Icc 1 X, f (n.gcd M)) - (X:ℝ)*primePatternMean M f| ≤
      (X:ℝ)^s*∏ p ∈ P, (2/(p:ℝ)^s+1) := by
  let M := ∏ p ∈ P, p
  have hM : 0 < M := prod_pos (fun p h => (hp p h).pos)
  have hsq : Squarefree M := _root_.Sieve.prodDistinctPrimes_squarefree P hp
  have factor {d : ℕ} (hd : d ∈ M.divisors) :
      (d.divisors.card:ℝ)/(d:ℝ)^s = ∏ p ∈ d.primeFactors, (2/(p:ℝ)^s) := by
    have hsd := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    have he : (∏ p ∈ d.primeFactors, (p:ℝ))=(d:ℝ) := by
      rw [←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hsd]
    rw [RHTower.Sieve.card_divisors_of_squarefree_squarefreeDivisorCount hsd (Nat.pos_of_mem_divisors hd).ne',
      Nat.cast_pow,Nat.cast_ofNat,prod_div_distrib,prod_const]
    congr 1
    rw [←he]
    exact (Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) _).symm
  dsimp only
  rw [gcd_test_expansion hM,primePatternMean,mul_sum,←sum_sub_distrib]
  calc _ ≤ ∑ d ∈ M.divisors, |patternCoefficient f d*((X/d:ℕ):ℝ)-(X:ℝ)*(patternCoefficient f d/d)| :=
           abs_sum_le_sum_abs _ _
       _ ≤ ∑ d ∈ M.divisors, (X:ℝ)^s*(∏ p ∈ d.primeFactors, (2/(p:ℝ)^s)) := by
           apply sum_le_sum
           intro d hd
           rw [←factor hd,show (X:ℝ)*(patternCoefficient f d/d)=patternCoefficient f d*((X:ℝ)/d) by ring,
             ←mul_sub,abs_mul]
           calc _ ≤ (d.divisors.card:ℝ)*((X:ℝ)^s/(d:ℝ)^s) :=
                    mul_le_mul (coefficient_bound hf d) (floor_cost hs hs1 X d (Nat.pos_of_mem_divisors hd))
                      (abs_nonneg _) (Nat.cast_nonneg _)
                _ = _ := by ring
       _ = _ := by rw [←mul_sum,RHTower.Sieve.sum_divisors_prod_primes_eq_prod hp]

#print axioms prime_pattern_sampling

end GaloisForLFunctions.RestrictedFactorizationCalculus
