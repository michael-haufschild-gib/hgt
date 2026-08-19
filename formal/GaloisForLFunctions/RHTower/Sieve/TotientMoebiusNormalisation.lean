import GaloisForLFunctions.RHTower.Sieve.CoprimeHarmonicDecomposition

/-!
# The totient as a Möbius divisor sum

Möbius inversion of `∑_{d ∣ n} φ(d) = n` gives `φ(n) = ∑_{a ∣ n} μ(a)(n/a)`, hence the
normalisation identity `∑_{a ∣ n} μ(a)/a = φ(n)/n`.  This is the main-term coefficient of the
coprime harmonic decomposition.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

theorem totient_eq_sum_moebius_mul (n : ℕ) (hn : 0 < n) :
    ((Nat.totient n : ℕ) : ℝ) = ∑ a ∈ n.divisors, ((μ a : ℤ) : ℝ) * ((n / a : ℕ) : ℝ) := by
  have hbase : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, ((Nat.totient i : ℕ) : ℝ) = (m : ℝ) := by
    intro m _
    have h := Nat.sum_totient m
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := fun k => ((Nat.totient k : ℕ) : ℝ)) (g := fun k => (k : ℝ))).mp hbase n hn
  rw [← hinv]
  exact Nat.sum_divisorsAntidiagonal (f := fun a b => ((μ a : ℤ) : ℝ) * (b : ℝ))

/-- **The normalisation identity.**  `∑_{a ∣ n} μ(a)/a = φ(n)/n`. -/
theorem sum_moebius_div_divisors_eq_totient_div {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, ((μ a : ℤ) : ℝ) / (a : ℝ) = (Nat.totient n : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [totient_eq_sum_moebius_mul n hn, Finset.sum_div]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hdvd : a ∣ n := Nat.dvd_of_mem_divisors ha
  have hcast : ((n / a : ℕ) : ℝ) = (n : ℝ) / (a : ℝ) := by
    rw [Nat.cast_div hdvd (ne_of_gt haR)]
  rw [hcast]
  field_simp

end RHTower.Sieve
