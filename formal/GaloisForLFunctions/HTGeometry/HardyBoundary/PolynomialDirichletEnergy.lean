import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Weighted coefficient energy and polynomial multipliers

The full Dirichlet energy of a real polynomial weights coefficient `k` by
`k + 1`. Multiplication by `X` costs at most a factor two in energy; scalar
multiplication is exact. These finite-support identities make multiplication
by each fixed polynomial bounded, without an ambient function-space hypothesis.
-/

open Polynomial Finset
open scoped BigOperators

namespace HTGeometry.DirichletBoundaryCyclicity
noncomputable section

/-- The full Dirichlet energy, including the Hardy coefficient contribution. -/
def coefficientEnergy (p : Polynomial ℝ) : ℝ :=
  ∑' k : ℕ, (k + 1 : ℝ) * (p.coeff k)^2

private theorem summable_weighted_coeff (p : Polynomial ℝ) (w : ℕ → ℝ) :
    Summable (fun k => w k * (p.coeff k)^2) := by
  apply summable_of_ne_finset_zero (s := p.support)
  intro k hk
  have hz : p.coeff k = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hk
  simp only [hz, zero_pow two_ne_zero, mul_zero]

theorem coefficientEnergy_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientEnergy p :=
  tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)

@[simp] theorem coefficientEnergy_zero : coefficientEnergy 0 = 0 := by
  simp [coefficientEnergy]

theorem coefficientEnergy_eq_sum (p : Polynomial ℝ) :
    coefficientEnergy p = ∑ k ∈ range (p.natDegree + 1), (k + 1 : ℝ) * (p.coeff k)^2 := by
  apply tsum_eq_sum
  intro k hk
  have hd : p.natDegree < k := by
    simp only [mem_range, not_lt] at hk
    omega
  rw [coeff_eq_zero_of_natDegree_lt hd, zero_pow two_ne_zero, mul_zero]

/-- The quadratic triangle inequality for the full coefficient energy. -/
theorem coefficientEnergy_add_le (p q : Polynomial ℝ) :
    coefficientEnergy (p + q) ≤ 2 * (coefficientEnergy p + coefficientEnergy q) := by
  have hp := summable_weighted_coeff p (fun k => (k + 1 : ℝ))
  have hq := summable_weighted_coeff q (fun k => (k + 1 : ℝ))
  calc
    _ ≤ ∑' k : ℕ, 2 * ((k + 1 : ℝ) * (p.coeff k)^2 +
        (k + 1 : ℝ) * (q.coeff k)^2) := by
      apply Summable.tsum_le_tsum _ (summable_weighted_coeff (p + q) _) ((hp.add hq).mul_left 2)
      intro k
      rw [coeff_add]
      have h : (p.coeff k + q.coeff k)^2 ≤ 2 * ((p.coeff k)^2 + (q.coeff k)^2) := by
        nlinarith only [sq_nonneg (p.coeff k - q.coeff k)]
      have hw : (0 : ℝ) ≤ k + 1 := by positivity
      convert mul_le_mul_of_nonneg_left h hw using 1
      ring
    _ = _ := by rw [tsum_mul_left, hp.tsum_add hq]; rfl

/-- Scalar polynomial multiplication rescales the energy exactly. -/
theorem coefficientEnergy_C_mul (a : ℝ) (p : Polynomial ℝ) :
    coefficientEnergy (C a * p) = a^2 * coefficientEnergy p := by
  calc
    _ = ∑' k : ℕ, a^2 * ((k + 1 : ℝ) * (p.coeff k)^2) := by
      apply tsum_congr
      intro k
      rw [coeff_C_mul]
      ring
    _ = _ := tsum_mul_left

/-- The shift adds precisely one to each occupied coefficient's weight. -/
theorem coefficientEnergy_X_mul (p : Polynomial ℝ) :
    coefficientEnergy (X * p) = ∑' k : ℕ, (k + 2 : ℝ) * (p.coeff k)^2 := by
  have h := (summable_weighted_coeff (X * p) (fun k => (k + 1 : ℝ))).sum_add_tsum_nat_add 1
  simpa only [sum_range_one, coeff_X_mul_zero, zero_pow two_ne_zero, mul_zero,
    zero_add, coeff_X_mul, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two,
    coefficientEnergy] using h.symm

/-- The unilateral shift is bounded in the full Dirichlet energy. -/
theorem coefficientEnergy_X_mul_le (p : Polynomial ℝ) :
    coefficientEnergy (X * p) ≤ 2 * coefficientEnergy p := by
  rw [coefficientEnergy_X_mul, coefficientEnergy, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_weighted_coeff p _)
    ((summable_weighted_coeff p _).mul_left 2)
  intro k
  have hw : (k + 2 : ℝ) ≤ 2 * (k + 1) := by linarith only [Nat.cast_nonneg (α := ℝ) k]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hw (sq_nonneg (p.coeff k))

/-- Every fixed power of the shift has a finite multiplier bound. -/
theorem coefficientEnergy_X_pow_mul_le (n : ℕ) (p : Polynomial ℝ) :
    coefficientEnergy (X^n * p) ≤ (2 : ℝ)^n * coefficientEnergy p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc]
      calc
        _ ≤ 2 * coefficientEnergy (X^n * p) := coefficientEnergy_X_mul_le _
        _ ≤ 2 * ((2 : ℝ)^n * coefficientEnergy p) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ']; ring

/-- Every fixed polynomial is a bounded multiplier for Dirichlet coefficient energy. -/
theorem exists_coefficientEnergy_multiplier_bound (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Polynomial ℝ, coefficientEnergy (p * q) ≤ C * coefficientEnergy q := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨C, hC, hp⟩ := hp
      obtain ⟨D, hD, hq⟩ := hq
      refine ⟨2 * (C + D), by positivity, ?_⟩
      intro r
      rw [add_mul]
      calc
        _ ≤ 2 * (coefficientEnergy (p * r) + coefficientEnergy (q * r)) :=
          coefficientEnergy_add_le _ _
        _ ≤ 2 * (C * coefficientEnergy r + D * coefficientEnergy r) :=
          mul_le_mul_of_nonneg_left (add_le_add (hp r) (hq r)) (by norm_num)
        _ = _ := by ring
  | monomial n a =>
      refine ⟨a^2 * (2 : ℝ)^n, by positivity, ?_⟩
      intro q
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, coefficientEnergy_C_mul]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (coefficientEnergy_X_pow_mul_le n q) (sq_nonneg a)

#print axioms coefficientEnergy_X_pow_mul_le
#print axioms exists_coefficientEnergy_multiplier_bound

end
end HTGeometry.DirichletBoundaryCyclicity
