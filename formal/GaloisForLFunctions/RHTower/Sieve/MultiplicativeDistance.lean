import GaloisForLFunctions.RHTower.Sieve.RamareDecomposition

/-!
# The distance of a multiplicative function from a character

Halász's theorem measures a multiplicative function by how far it stands from the characters
`n ↦ n^{it}`:

`D(f, t; P)² = ∑_{p ∈ P} (1 - Re(f(p) p^{-it}))/p`.

Each summand is nonnegative whenever `|f(p)| ≤ 1`, since the real part of a number of modulus at most
one is at most one, so the distance is a genuine nonnegative quantity and is monotone in the set of
primes.

This is the object Halász's bound is stated in terms of; the bound itself is a separate theorem and
is not proved here.
-/

namespace RHTower.Sieve

open Finset

/-- The squared distance of a multiplicative function from the character `n^{it}`. -/
noncomputable def mulDistSq (f : ℕ → ℂ) (t : ℝ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (1 - (f p
    * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)).re) / (p : ℝ)

/-- A number of modulus at most one has real part at most one. -/
theorem one_sub_re_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ 1 - z.re := by
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

/-- Each summand of the distance is nonnegative. -/
theorem mulDist_term_nonneg {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) {p : ℕ} (hp : 0 < p) :
    0 ≤ (1 - (f p
      * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)).re) / (p : ℝ) := by
  have hnorm : ‖f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hf p
  have hnum := one_sub_re_nonneg hnorm
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  positivity

/-- **The distance is nonnegative.** -/
theorem mulDistSq_nonneg {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) : 0 ≤ mulDistSq f t P := by
  refine Finset.sum_nonneg fun p hp => ?_
  exact mulDist_term_nonneg hf t (hP p hp)

/-- **The distance grows with the set of primes.** -/
theorem mulDistSq_mono {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) {P Q : Finset ℕ}
    (hPQ : P ⊆ Q) (hQ : ∀ p ∈ Q, 0 < p) : mulDistSq f t P ≤ mulDistSq f t Q := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hPQ fun p hpQ _ => ?_
  exact mulDist_term_nonneg hf t (hQ p hpQ)

end RHTower.Sieve
