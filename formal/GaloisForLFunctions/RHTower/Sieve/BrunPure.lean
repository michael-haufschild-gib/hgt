import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples
import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius

/-!
# Brun's pure sieve on an integer interval

Combining the Bonferroni inequalities with the interval remainder bound gives two-sided control of

`S(a, b; m) = #{n ∈ Ioc a b : gcd n m = 1}`

for a squarefree sifting modulus `m`.  Truncating inclusion–exclusion at `r` prime factors
produces the main term

`(b - a) ∑_{d ∣ m, ω d ≤ r} μ d / d`

together with an error of at most one unit per surviving divisor.  The direction of the inequality
is the parity of `r`: even truncation is an upper sieve, odd truncation a lower sieve.

The error term is the number of truncated divisors, so the whole bound is unconditional and
completely explicit; no smoothness, level-of-distribution, or optimization hypothesis appears.
-/

namespace RHTower.Sieve

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The divisors of `m` retained by a Brun truncation at `r` prime factors. -/
def truncDivisors (m r : ℕ) : Finset ℕ := {d ∈ m.divisors | d.primeFactors.card ≤ r}

theorem mem_truncDivisors {m r d : ℕ} :
    d ∈ truncDivisors m r ↔ (d ∣ m ∧ m ≠ 0) ∧ d.primeFactors.card ≤ r := by
  simp [truncDivisors, Nat.mem_divisors]

/-- Restricting a truncated divisor set to a gcd is the same as further filtering by divisibility. -/
theorem truncDivisors_gcd {m n r : ℕ} (hm : m ≠ 0) :
    truncDivisors (Nat.gcd n m) r = {d ∈ truncDivisors m r | d ∣ n} := by
  ext d
  have hgcd : Nat.gcd n m ≠ 0 := Nat.gcd_ne_zero_right hm
  simp only [mem_truncDivisors, Finset.mem_filter, Nat.dvd_gcd_iff, hgcd, hm, ne_eq,
    not_false_eq_true, and_true]
  tauto

/-- **Interchange.**  Summing the truncated Möbius indicator over an interval regroups into a
weighted count of multiples. -/
theorem sum_truncMoebius_gcd_eq (m a b r : ℕ) (hm : m ≠ 0) :
    ∑ n ∈ Ioc a b, ∑ d ∈ truncDivisors (Nat.gcd n m) r, (μ d : ℤ)
      = ∑ d ∈ truncDivisors m r, (μ d : ℤ) * (#{n ∈ Ioc a b | d ∣ n} : ℤ) := by
  have hrewrite :
      ∑ n ∈ Ioc a b, ∑ d ∈ truncDivisors (Nat.gcd n m) r, (μ d : ℤ)
        = ∑ n ∈ Ioc a b, ∑ d ∈ truncDivisors m r, (if d ∣ n then (μ d : ℤ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [truncDivisors_gcd (n := n) hm, Finset.sum_filter]
  rw [hrewrite, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Every divisor retained by the truncation of a squarefree modulus is squarefree, so its Möbius
value has absolute value one. -/
theorem abs_moebius_eq_one_of_mem_truncDivisors {m r d : ℕ} (hm : Squarefree m)
    (hd : d ∈ truncDivisors m r) : |(μ d : ℝ)| = 1 := by
  have hdvd : d ∣ m := (mem_truncDivisors.1 hd).1.1
  have hsq : Squarefree d := hm.squarefree_of_dvd hdvd
  have : (μ d : ℤ) = (-1) ^ d.primeFactors.card :=
    moebius_eq_neg_one_pow_card_primeFactors hsq
  have hcast : (μ d : ℝ) = (-1) ^ d.primeFactors.card := by exact_mod_cast this
  rw [hcast, abs_pow, abs_neg, abs_one, one_pow]

/-- The truncated main term together with a one-per-divisor error controls the truncated
inclusion–exclusion sum from both sides. -/
theorem abs_sum_truncMoebius_sub_mainTerm_le (m a b r : ℕ) (hm : Squarefree m) (hab : a ≤ b) :
    |(∑ d ∈ truncDivisors m r, (μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ))
        - ((b : ℝ) - a) * ∑ d ∈ truncDivisors m r, (μ d : ℝ) / d|
      ≤ (truncDivisors m r).card := by
  have hmain : ((b : ℝ) - a) * ∑ d ∈ truncDivisors m r, (μ d : ℝ) / d
      = ∑ d ∈ truncDivisors m r, (μ d : ℝ) * (((b : ℝ) - a) / d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ truncDivisors m r,
      |(μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ) - (μ d : ℝ) * (((b : ℝ) - a) / d)| ≤ 1 := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (by
      simpa [truncDivisors, Nat.mem_divisors] using (Finset.mem_filter.1 hd).1)
    have hrem := abs_card_filter_dvd_Ioc_sub_lt d a b hdpos hab
    have hfactor : (μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ) - (μ d : ℝ) * (((b : ℝ) - a) / d)
        = (μ d : ℝ) * ((#{n ∈ Ioc a b | d ∣ n} : ℝ) - ((b : ℝ) - a) / d) := by ring
    rw [hfactor, abs_mul, abs_moebius_eq_one_of_mem_truncDivisors hm hd, one_mul]
    exact hrem.le
  calc ∑ d ∈ truncDivisors m r,
        |(μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ) - (μ d : ℝ) * (((b : ℝ) - a) / d)|
      ≤ ∑ _d ∈ truncDivisors m r, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (truncDivisors m r).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Brun's pure sieve, upper bound.**  An even truncation level gives an upper sieve for the
number of integers in `Ioc a b` coprime to a squarefree modulus. -/
theorem card_coprime_Ioc_le (m a b r : ℕ) (hm : Squarefree m) (hab : a ≤ b) (hr : Even r) :
    (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ)
      ≤ ((b : ℝ) - a) * (∑ d ∈ truncDivisors m r, (μ d : ℝ) / d)
        + (truncDivisors m r).card := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hstep1 :
      (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ)
        ≤ ∑ n ∈ Ioc a b, ∑ d ∈ truncDivisors (Nat.gcd n m) r, (μ d : ℤ) := by
    have hcard :
        (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ)
          = ∑ n ∈ Ioc a b, (if Nat.Coprime n m then (1 : ℤ) else 0) :=
      Finset.natCast_card_filter (fun n => Nat.Coprime n m) (Finset.Ioc a b)
    rw [hcard]
    refine Finset.sum_le_sum ?_
    intro n _
    have hsq : Squarefree (Nat.gcd n m) := hm.squarefree_of_dvd (Nat.gcd_dvd_right n m)
    exact indicator_le_sum_divisors_moebius_filter_card_le hsq hr
  have hstep2 := sum_truncMoebius_gcd_eq m a b r hm0
  have hZ :
      (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ)
        ≤ ∑ d ∈ truncDivisors m r, (μ d : ℤ) * (#{n ∈ Ioc a b | d ∣ n} : ℤ) := by
    rw [← hstep2]; exact hstep1
  have hR :
      (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ)
        ≤ ∑ d ∈ truncDivisors m r, (μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ) := by
    exact_mod_cast hZ
  have hbound := abs_sum_truncMoebius_sub_mainTerm_le m a b r hm hab
  have := (abs_le.1 hbound).2
  linarith

/-- **Brun's pure sieve, lower bound.**  An odd truncation level gives a lower sieve. -/
theorem le_card_coprime_Ioc (m a b r : ℕ) (hm : Squarefree m) (hab : a ≤ b) (hr : Odd r) :
    ((b : ℝ) - a) * (∑ d ∈ truncDivisors m r, (μ d : ℝ) / d)
        - (truncDivisors m r).card
      ≤ (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hstep1 :
      ∑ n ∈ Ioc a b, ∑ d ∈ truncDivisors (Nat.gcd n m) r, (μ d : ℤ)
        ≤ (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ) := by
    have hcard :
        (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ)
          = ∑ n ∈ Ioc a b, (if Nat.Coprime n m then (1 : ℤ) else 0) :=
      Finset.natCast_card_filter (fun n => Nat.Coprime n m) (Finset.Ioc a b)
    rw [hcard]
    refine Finset.sum_le_sum ?_
    intro n _
    have hsq : Squarefree (Nat.gcd n m) := hm.squarefree_of_dvd (Nat.gcd_dvd_right n m)
    exact sum_divisors_moebius_filter_card_le_le_indicator hsq hr
  have hstep2 := sum_truncMoebius_gcd_eq m a b r hm0
  have hZ :
      ∑ d ∈ truncDivisors m r, (μ d : ℤ) * (#{n ∈ Ioc a b | d ∣ n} : ℤ)
        ≤ (#{n ∈ Ioc a b | Nat.Coprime n m} : ℤ) := by
    rw [← hstep2]; exact hstep1
  have hR :
      ∑ d ∈ truncDivisors m r, (μ d : ℝ) * (#{n ∈ Ioc a b | d ∣ n} : ℝ)
        ≤ (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ) := by
    exact_mod_cast hZ
  have hbound := abs_sum_truncMoebius_sub_mainTerm_le m a b r hm hab
  have := (abs_le.1 hbound).1
  linarith

/-- Being coprime to a product of primes is exactly avoiding each of them. -/
theorem coprime_prod_primes_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    Nat.Coprime n (∏ p ∈ P, p) ↔ ∀ p ∈ P, ¬ p ∣ n := by
  constructor
  · intro h p hp hpn
    have hpm : p ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem _ hp
    have : p ∣ Nat.gcd n (∏ q ∈ P, q) := Nat.dvd_gcd hpn hpm
    rw [h] at this
    exact (hP p hp).one_lt.ne' (Nat.dvd_one.1 this)
  · intro h
    refine Nat.Coprime.prod_right ?_
    intro p hp
    exact ((hP p hp).coprime_iff_not_dvd.2 (h p hp)).symm

end RHTower.Sieve
