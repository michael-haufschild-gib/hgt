import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

namespace SQBCompactRow
open scoped BigOperators
open Finset
noncomputable section
set_option maxHeartbeats 200000

def degreeElevationCoefficient (n j a : ℕ) : ℝ :=
  if j ≤ a then ((n-j).choose (a-j) : ℝ) else 0

def unscaledBernstein (n a : ℕ) (t : ℝ) : ℝ :=
  t^a*(1-t)^(n-a)

theorem monomial_bernstein_reconstruction (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    (∑ a ∈ range (n+1), degreeElevationCoefficient n j a *
      unscaledBernstein n a t) = t^j := by
  have hsplit : n+1 = j+(n-j+1) := by omega
  rw [hsplit, sum_range_add]
  have hzero : (∑ a ∈ range j, degreeElevationCoefficient n j a *
      unscaledBernstein n a t) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hja : ¬ j ≤ a := by have := mem_range.mp ha; omega
    simp [degreeElevationCoefficient, hja]
  rw [hzero, zero_add]
  calc
    _ = t^j * ∑ a ∈ range (n-j+1),
        t^a*(1-t)^((n-j)-a)*((n-j).choose a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      have hja : j ≤ j+a := by omega
      have he : n-(j+a) = (n-j)-a := by omega
      simp only [degreeElevationCoefficient, hja, if_true, Nat.add_sub_cancel_left,
        unscaledBernstein, pow_add, he]
      ring
    _ = t^j * (t+(1-t))^(n-j) := by rw [add_pow]
    _ = t^j := by simp

theorem tensor_monomial_bernstein_reconstruction
    (n m j k : ℕ) (hj : j ≤ n) (hk : k ≤ m) (c t v : ℝ) :
    (∑ a ∈ range (n+1), ∑ b ∈ range (m+1),
      (c * degreeElevationCoefficient n j a * degreeElevationCoefficient m k b) *
        unscaledBernstein n a t * unscaledBernstein m b v) = c*t^j*v^k := by
  calc
    _ = c * (∑ a ∈ range (n+1), degreeElevationCoefficient n j a *
          unscaledBernstein n a t) *
        (∑ b ∈ range (m+1), degreeElevationCoefficient m k b *
          unscaledBernstein m b v) := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      ring
    _ = _ := by rw [monomial_bernstein_reconstruction n j hj,
      monomial_bernstein_reconstruction m k hk]

end
end SQBCompactRow
