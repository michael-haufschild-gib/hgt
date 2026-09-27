import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction

/-!
# Divisor weights in repeated logarithmic dilation

Two unweighted delay sums produce the divisor-count coefficient.
Pairing complementary divisors also gives the exact logarithmic
coefficient, with no estimate or loss of signs.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem sum_log_divisors_eq_half_card_mul_log (n : ℕ) :
    (∑ d ∈ n.divisors, Real.log d) = (n.divisors.card : ℝ) * Real.log n / 2 := by
  have hf : (∑ x ∈ n.divisorsAntidiagonal, Real.log x.1) =
      ∑ d ∈ n.divisors, Real.log d := Nat.sum_divisorsAntidiagonal (fun d _ => Real.log d)
  have hs : (∑ x ∈ n.divisorsAntidiagonal, Real.log x.2) =
      ∑ d ∈ n.divisors, Real.log d := Nat.sum_divisorsAntidiagonal' (fun _ d => Real.log d)
  have hp : (∑ x ∈ n.divisorsAntidiagonal, (Real.log x.1 + Real.log x.2)) =
      (n.divisors.card : ℝ) * Real.log n := by
    calc
      _ = ∑ _x ∈ n.divisorsAntidiagonal, Real.log n := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := Nat.mem_divisorsAntidiagonal.mp hx
        have hnz : x.1 * x.2 ≠ 0 := by rw [hx'.1]; exact hx'.2
        have h1 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (left_ne_zero_of_mul hnz)
        have h2 : (x.2 : ℝ) ≠ 0 := by exact_mod_cast (right_ne_zero_of_mul hnz)
        rw [← Real.log_mul h1 h2, ← Nat.cast_mul, hx'.1]
      _ = ∑ _d ∈ n.divisors, Real.log n := Nat.sum_divisorsAntidiagonal (fun _ _ => Real.log n)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, hf, hs] at hp
  linarith only [hp]

theorem logarithmicDilationSum_twice_eq_divisor_weighted (f : ℝ → ℝ) (T : ℝ) :
    logarithmicDilationSum (logarithmicDilationSum f) T =
      logarithmicWeightedDilation (fun n => (n.divisors.card : ℝ)) f T := by
  change logarithmicWeightedDilation (fun _ => 1)
    (logarithmicWeightedDilation (fun _ => 1) f) T = _
  rw [logarithmicWeightedDilation_comp]
  have hc (n : ℕ) : (∑ _x ∈ n.divisorsAntidiagonal, (1 : ℝ) * 1) = n.divisors.card := by
    simp only [one_mul]
    rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℝ))]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [hc]

theorem logarithmicDilationSum_log_weighted (f : ℝ → ℝ) (T : ℝ) :
    logarithmicDilationSum (logarithmicWeightedDilation (fun n => Real.log n) f) T =
      logarithmicWeightedDilation (fun n => (n.divisors.card : ℝ) * Real.log n / 2) f T := by
  change logarithmicWeightedDilation (fun _ => 1)
    (logarithmicWeightedDilation (fun n => Real.log n) f) T = _
  rw [logarithmicWeightedDilation_comp]
  have hc (n : ℕ) : (∑ x ∈ n.divisorsAntidiagonal, (1 : ℝ) * Real.log x.2) =
      (n.divisors.card : ℝ) * Real.log n / 2 := by
    simp only [one_mul]
    rw [Nat.sum_divisorsAntidiagonal' (fun _ d => Real.log d), sum_log_divisors_eq_half_card_mul_log]
  simp only [hc]

end RHTower
