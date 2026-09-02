import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor
import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius

/-!
# The Mertens sum as a top-window odd sum, and as the Euler characteristic of the squarefree
knapsack complex

Two exact identities for `M(x) = ∑_{n ≤ x} μ(n)`.

* `M(x) = ∑_{n ∈ (x/2, x], n odd} μ(n)`: the even terms `μ(2m) = −μ(m)` (`m` odd) cancel the odd
  terms below `x/2`.
* `M(x) = ∑_S (−1)^{|S|}` over the finite sets `S` of primes with `∏ S ≤ x`.  These sets are the
  faces of a simplicial complex (the squarefree knapsack complex), so `−M(x)` is its reduced Euler
  characteristic.  The complex is shifted (a face stays a face when a prime is replaced by a
  smaller one), and the first identity is the alternating sum of its Betti numbers, which are
  indexed by the odd squarefree integers of `(x/2, x]`.  Since that window always contains an odd
  prime, the Betti numbers do not vanish: the cancellation in `M(x)` is not a topological
  cancellation but the parity balance of `ω(n)` on the top window.

Also recorded: an affine change of variable `s ↦ a s + b` preserves the displacement of a point
from the centre of its strip measured in strip widths, so no affine image of `ζ` amplifies the
real part of a zero relative to its critical line.
-/

namespace RHTower

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The Möbius function at twice an integer. -/
theorem moebius_two_mul (m : ℕ) : μ (2 * m) = if Odd m then -μ m else 0 := by
  by_cases hm : Odd m
  · rw [if_pos hm]
    have hcop : Nat.Coprime 2 m := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime Nat.prime_two]
    ring
  · rw [if_neg hm]
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hm
    apply moebius_eq_zero_of_not_squarefree
    intro hsq
    have h4 : 2 * 2 ∣ 2 * m := ⟨k, by rw [hk]; ring⟩
    have := hsq 2 h4
    exact absurd this (by decide)

/-- **The Mertens sum is the Möbius sum over the odd integers of `(x/2, x]`.** -/
theorem sum_moebius_eq_sum_odd_window (x : ℕ) :
    ∑ n ∈ Icc 1 x, μ n = ∑ n ∈ (Icc 1 x).filter (fun n => Odd n ∧ x < 2 * n), μ n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 x) (fun n => Odd n)]
  have heven : ((Icc 1 x).filter (fun n => ¬ Odd n)) = (Icc 1 (x / 2)).image (fun m => 2 * m) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, hx⟩, hodd⟩
      obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
      refine ⟨k, ⟨by omega, ?_⟩, by omega⟩
      exact (Nat.le_div_iff_mul_le two_pos).mpr (by omega)
    · rintro ⟨m, ⟨h1, hm⟩, rfl⟩
      have := (Nat.le_div_iff_mul_le two_pos).mp hm
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.not_odd_iff_even]
      exact ⟨m, by ring⟩
  rw [heven, Finset.sum_image (fun a _ b _ h => by omega)]
  simp_rw [moebius_two_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not ((Icc 1 x).filter (fun n => Odd n))
    (fun n => x < 2 * n)]
  have hlow : ((Icc 1 x).filter (fun n => Odd n)).filter (fun n => ¬ x < 2 * n)
      = (Icc 1 (x / 2)).filter (fun m => Odd m) := by
    ext n
    simp only [mem_filter, mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, hodd⟩, h2⟩
      exact ⟨⟨h1, (Nat.le_div_iff_mul_le two_pos).mpr (by omega)⟩, hodd⟩
    · rintro ⟨⟨h1, hm⟩, hodd⟩
      have := (Nat.le_div_iff_mul_le two_pos).mp hm
      exact ⟨⟨⟨h1, by omega⟩, hodd⟩, by omega⟩
  rw [hlow, Finset.filter_filter]
  ring

/-- The finite sets of primes whose product is at most `x`: the faces of the squarefree knapsack
complex. -/
def primeSets (x : ℕ) : Finset (Finset ℕ) :=
  ((range (x + 1)).powerset).filter (fun S => (∀ p ∈ S, p.Prime) ∧ ∏ p ∈ S, p ≤ x)

/-- **Euler characteristic of the squarefree knapsack complex.**  The alternating count of its
faces is the Mertens sum. -/
theorem sum_primeSets_neg_one_pow (x : ℕ) :
    ∑ S ∈ primeSets x, (-1 : ℤ) ^ S.card = ∑ n ∈ Icc 1 x, μ n := by
  classical
  have hfilter : ∑ n ∈ Icc 1 x, μ n = ∑ n ∈ (Icc 1 x).filter (fun n => Squarefree n), μ n := by
    symm
    refine Finset.sum_filter_of_ne fun n _ hne => ?_
    by_contra h
    exact hne (moebius_eq_zero_of_not_squarefree h)
  rw [hfilter]
  symm
  refine Finset.sum_nbij' (fun n => n.primeFactors) (fun S => ∏ p ∈ S, p) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨_, hx⟩, hsq⟩ := hn
    simp only [primeSets, mem_filter, mem_powerset]
    refine ⟨fun p hp => ?_, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
    · exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hx))
    · rw [Nat.prod_primeFactors_of_squarefree hsq]
      exact hx
  · intro S hS
    simp only [primeSets, mem_filter, mem_powerset] at hS
    obtain ⟨_, hprime, hle⟩ := hS
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨Finset.prod_pos fun p hp => (hprime p hp).pos, hle⟩,
      GibbsGas.squarefree_prod_primes hprime⟩
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    exact Nat.prod_primeFactors_of_squarefree hn.2
  · intro S hS
    simp only [primeSets, mem_filter, mem_powerset] at hS
    exact Nat.primeFactors_prod hS.2.1
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    exact Sieve.moebius_eq_neg_one_pow_card_primeFactors hn.2

/-- Every window `(x/2, x]` with `x ≥ 3` contains an odd prime, so the squarefree knapsack
complex always has an odd squarefree integer in its top window. -/
theorem exists_odd_prime_window {x : ℕ} (hx : 3 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ x < 2 * p ∧ p ≤ x := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (x / 2) (by omega)
  have hdiv := Nat.div_add_mod x 2
  have hmod : x % 2 < 2 := Nat.mod_lt x two_pos
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    have hx3 : x = 3 := by omega
    subst hx3
    exact ⟨3, Nat.prime_three, by decide, by norm_num, le_rfl⟩
  · exact ⟨p, hp, hodd, by omega, by omega⟩

/-- An affine change of variable `s ↦ a s + b` preserves the displacement of a point from the
centre `a/2 + b` of its strip, measured in strip widths `a`. -/
theorem relativeDisplacement_affine {a : ℝ} (ha : a ≠ 0) (b : ℝ) (ρ : ℂ) :
    (((a : ℂ) * ρ + b).re - (a / 2 + b)) / a = ρ.re - 1 / 2 := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  field_simp
  ring

end RHTower
