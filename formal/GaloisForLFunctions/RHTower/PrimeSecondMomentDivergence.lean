import GaloisForLFunctions.RHTower.SteinhausAbscissaSecondMoment
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The prime second moment diverges, and products of two primes factor uniquely

Two inputs for the prime sub-series of the random Dirichlet series.

The arithmetic one is that a product of two primes determines its factors as a multiset: if
`p r = q t` with all four prime then `(p,r)` and `(q,t)` agree up to order.  This is what makes the
fourth moment of `∑_p a_p X_p` collapse to `2(∑ a_p²)² − ∑ a_p⁴`, and it is exactly the step that
fails over general integers, where `X` is not independent across indices.

The analytic one is that `∑_p p^{−2σ}` diverges for every `σ ≤ 1/2`, by comparison with `∑_p 1/p`.

Together with the fourth-moment escape engine these give the almost-sure divergence of the prime
random Dirichlet series to the left of the half line.
-/

noncomputable section

open Filter Set

namespace GaloisForLFunctions.RHTower

/-! ## Products of two primes -/

/-- **A product of two primes determines its factors up to order.** -/
theorem prime_mul_eq_prime_mul {p q r t : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h : p * r = q * t) : (p = q ∧ r = t) ∨ (p = t ∧ r = q) := by
  have hqd : q ∣ p * r := ⟨t, h⟩
  rcases (Nat.Prime.dvd_mul hq).1 hqd with hd | hd
  · have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hd
    subst hpq
    have hrt : r = t := Nat.eq_of_mul_eq_mul_left hq.pos h
    exact Or.inl ⟨rfl, hrt⟩
  · have hrq : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).1 hd
    subst hrq
    have h2 : q * p = q * t := by rw [← h]; ring
    exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hq.pos h2, rfl⟩

/-! ## Divergence of the prime second moment -/

/-- The prime-supported coefficient sequence of the random Dirichlet series. -/
def primeCoeff (σ : ℝ) : ℕ → ℝ :=
  Set.indicator {p : ℕ | p.Prime} fun n => (n : ℝ) ^ (-(2 * σ))

theorem primeCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeCoeff σ n := by
  rw [primeCoeff]
  by_cases h : n ∈ {p : ℕ | p.Prime}
  · rw [Set.indicator_of_mem h]
    positivity
  · rw [Set.indicator_of_notMem h]

/-- **The prime second moment is not summable up to the half line.** -/
theorem not_summable_primeCoeff {σ : ℝ} (hσ : σ ≤ 1 / 2) : ¬ Summable (primeCoeff σ) := by
  intro hsum
  refine not_summable_one_div_on_primes ?_
  refine hsum.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · by_cases h : n ∈ {p : ℕ | p.Prime}
    · rw [Set.indicator_of_mem h]
      positivity
    · rw [Set.indicator_of_notMem h]
  · by_cases h : n ∈ {p : ℕ | p.Prime}
    · rw [Set.indicator_of_mem h, primeCoeff, Set.indicator_of_mem h]
      exact one_div_le_rpow_neg_two_mul hσ (Nat.one_le_iff_ne_zero.2 (Nat.Prime.ne_zero h))
    · rw [Set.indicator_of_notMem h]
      exact primeCoeff_nonneg σ n

/-- **The partial sums of the prime second moment escape to infinity.** -/
theorem tendsto_sum_primeCoeff_atTop {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, primeCoeff σ n) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (primeCoeff_nonneg σ)).1
    (not_summable_primeCoeff hσ)

end GaloisForLFunctions.RHTower

end
