import GaloisForLFunctions.SelbergClass.Primon.KestenMcKay

/-!
# The positive kernel behind negative Kesten–McKay phase moments

Negating the positive-frequency even cosine moments gives a geometric
sequence. Its Hankel quadratic form is exactly one weighted square, so every
finite section is positive semidefinite and every two-by-two minor vanishes.
This identifies the rank-one geometry of the averaged prime-power terms in
Hartnoll–Yang, arXiv:2502.02661v2, (111)–(112).
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Negative of the even phase moment at the next positive frequency. -/
def negativeEvenMoment (p : Nat.Primes) (n : ℕ) : ℝ :=
  -(∫ t in Ioo (0 : ℝ) 1,
    kestenMcKayDensity p t * Real.cos (2 * Real.pi * (n + 1) * t))

/-- The negative even moments form a geometric sequence. -/
theorem negativeEvenMoment_eq (p : Nat.Primes) (n : ℕ) :
    negativeEvenMoment p n = ((p : ℝ) - 1) / (2 * (p : ℝ)) * ((p : ℝ)⁻¹) ^ n := by
  rw [negativeEvenMoment, integral_kestenMcKayDensity_cos_succ, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev, neg_mul, neg_neg, inv_pow]
  ring

/-- Every finite Hankel energy is exactly one square of a weighted evaluation. -/
theorem phaseMoment_hankel_energy (p : Nat.Primes) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * negativeEvenMoment p (i + j)) =
      ((p : ℝ) - 1) / (2 * (p : ℝ)) *
        (∑ i ∈ s, a i * ((p : ℝ)⁻¹) ^ i) ^ 2 := by
  simp_rw [negativeEvenMoment_eq, pow_add]
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The averaged phase sequence defines a positive semidefinite Hankel kernel. -/
theorem phaseMoment_hankel_nonneg (p : Nat.Primes) (s : Finset ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * negativeEvenMoment p (i + j) := by
  rw [phaseMoment_hankel_energy]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (sq_nonneg _)

/-- The entire nullspace consists of observables whose polynomial vanishes at `1/p`. -/
theorem phaseMoment_hankel_zero_iff (p : Nat.Primes) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * negativeEvenMoment p (i + j)) = 0 ↔
      (∑ i ∈ s, a i * ((p : ℝ)⁻¹) ^ i) = 0 := by
  rw [phaseMoment_hankel_energy]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hC : 0 < ((p : ℝ) - 1) / (2 * (p : ℝ)) :=
    div_pos (by linarith) (by positivity)
  simp only [mul_eq_zero, ne_of_gt hC, false_or, sq_eq_zero_iff]

/-- All two-by-two Hankel minors vanish: the positive kernel has rank at most one. -/
theorem phaseMoment_hankel_minor (p : Nat.Primes) (i j k l : ℕ) :
    negativeEvenMoment p (i + k) * negativeEvenMoment p (j + l) -
      negativeEvenMoment p (i + l) * negativeEvenMoment p (j + k) = 0 := by
  simp only [negativeEvenMoment_eq, pow_add]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
