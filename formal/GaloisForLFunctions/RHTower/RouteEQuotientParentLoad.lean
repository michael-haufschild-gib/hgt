import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds

/-!
# Weighted quotient-parent load for Route E's signed edge family

For `w(q)=1/((q+1)(q+2))`, an odd quotient `u ≥ 3` pays its even child
`2u` and any finite family of odd children `pu`, `p ≥ 3`, using at most
`115/126` of its own weight. The odd-child budget uses the existing
reciprocal-square bound, not prime-counting. This is the scalar capacity
needed to test a least-prime-factor sign transport on actual Möbius quotients.
It does not yet prove that every positive quotient has an admissible parent.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

def quotientEdgeWeight (q : ℕ) : ℝ :=
  1 / (((q : ℝ) + 1) * ((q : ℝ) + 2))

theorem quotientEdgeWeight_nonneg (q : ℕ) :
    0 ≤ quotientEdgeWeight q := by
  unfold quotientEdgeWeight
  positivity

theorem quotientEdgeWeight_two_le {u : ℕ} (hu : 3 ≤ u) :
    quotientEdgeWeight (2 * u) ≤ (5 / 14 : ℝ) * quotientEdgeWeight u := by
  let x : ℝ := u
  have hx : 3 ≤ x := by dsimp [x]; exact_mod_cast hu
  have hprod : 0 ≤ (x - 3) * (x + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hpoly : 14 * ((x + 1) * (x + 2)) ≤
      5 * ((2 * x + 1) * (2 * x + 2)) := by
    nlinarith [hprod]
  have hA : 0 < (x + 1) * (x + 2) := by positivity
  have hB : 0 < (2 * x + 1) * (2 * x + 2) := by positivity
  unfold quotientEdgeWeight
  push_cast
  change 1 / ((2 * x + 1) * (2 * x + 2)) ≤
    (5 / 14 : ℝ) * (1 / ((x + 1) * (x + 2)))
  rw [show (5 / 14 : ℝ) * (1 / ((x + 1) * (x + 2))) =
      (5 / 14 : ℝ) / ((x + 1) * (x + 2)) by ring]
  apply (div_le_div_iff₀ hB hA).2
  nlinarith [hpoly]

theorem quotientEdgeWeight_mul_le {u p : ℕ} (hu : 3 ≤ u) (hp : 3 ≤ p) :
    quotientEdgeWeight (p * u) ≤
      (20 / 9 : ℝ) * quotientEdgeWeight u / (p : ℝ) ^ 2 := by
  let x : ℝ := u
  let y : ℝ := p
  have hx : 3 ≤ x := by dsimp [x]; exact_mod_cast hu
  have hy : 3 ≤ y := by dsimp [y]; exact_mod_cast hp
  have hprod : 0 ≤ (x - 3) * (11 * x + 6) :=
    mul_nonneg (by linarith) (by linarith)
  have hApoly : 9 * ((x + 1) * (x + 2)) ≤ 20 * x ^ 2 := by
    nlinarith [hprod]
  have hAp : 9 * y ^ 2 * ((x + 1) * (x + 2)) ≤ 20 * y ^ 2 * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hApoly (sq_nonneg y)]
  have hBpoly : (y * x) ^ 2 ≤ (y * x + 1) * (y * x + 2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ y) (by linarith : 0 ≤ x)]
  have hpoly : 9 * y ^ 2 * ((x + 1) * (x + 2)) ≤
      20 * ((y * x + 1) * (y * x + 2)) := by
    nlinarith [hAp, hBpoly]
  have hA : 0 < (x + 1) * (x + 2) := by positivity
  have hB : 0 < (y * x + 1) * (y * x + 2) := by positivity
  have hy2 : 0 < y ^ 2 := by positivity
  unfold quotientEdgeWeight
  push_cast
  change 1 / ((y * x + 1) * (y * x + 2)) ≤
    (20 / 9 : ℝ) * (1 / ((x + 1) * (x + 2))) / y ^ 2
  field_simp
  nlinarith [hpoly]

/-- One odd negative parent pays its even child and every eligible odd-prime child. -/
theorem quotientEdgeWeight_parent_load_le
    {u : ℕ} (hu : 3 ≤ u) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) :
    quotientEdgeWeight (2 * u) +
        ∑ p ∈ s, quotientEdgeWeight (p * u) ≤
      (115 / 126 : ℝ) * quotientEdgeWeight u := by
  have hoddMass := Sieve.sum_inv_sq_odd_le hs
  have hsum : (∑ p ∈ s, quotientEdgeWeight (p * u)) ≤
      (5 / 9 : ℝ) * quotientEdgeWeight u := by
    calc
      _ ≤ ∑ p ∈ s, (20 / 9 : ℝ) * quotientEdgeWeight u / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact quotientEdgeWeight_mul_le hu (hs p hp).1
      _ = ((20 / 9 : ℝ) * quotientEdgeWeight u) *
          (∑ p ∈ s, 1 / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ ((20 / 9 : ℝ) * quotientEdgeWeight u) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hoddMass
          (mul_nonneg (by norm_num) (quotientEdgeWeight_nonneg u))
      _ = (5 / 9 : ℝ) * quotientEdgeWeight u := by ring
  have htwo := quotientEdgeWeight_two_le hu
  nlinarith

theorem quotientEdgeWeight_parent_load_le_self
    {u : ℕ} (hu : 3 ≤ u) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 3 ≤ p ∧ ¬ 2 ∣ p) :
    quotientEdgeWeight (2 * u) +
        ∑ p ∈ s, quotientEdgeWeight (p * u) ≤
      quotientEdgeWeight u := by
  have hload := quotientEdgeWeight_parent_load_le hu s hs
  have hnonneg := quotientEdgeWeight_nonneg u
  nlinarith

end
end RHTower
