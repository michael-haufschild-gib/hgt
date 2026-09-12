module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Ring

@[expose] public section
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


def bernsteinTransform (f : ℕ → ℕ → ℝ) (t v : ℝ) : ℝ :=
  ∑ a ∈ range 9, ∑ b ∈ range 13,
    f a b * unscaledBernstein 8 a t * unscaledBernstein 12 b v

theorem bernsteinTransform_add (f g : ℕ → ℕ → ℝ) (t v : ℝ) :
    bernsteinTransform (fun a b => f a b + g a b) t v =
      bernsteinTransform f t v + bernsteinTransform g t v := by
  simp only [bernsteinTransform, add_mul, sum_add_distrib]

theorem bernsteinTransform_const_mul (c : ℝ) (f : ℕ → ℕ → ℝ) (t v : ℝ) :
    bernsteinTransform (fun a b => c * f a b) t v =
      c * bernsteinTransform f t v := by
  simp only [bernsteinTransform, mul_assoc, mul_sum]

def tensorIntegerCoefficient (c : ℤ) (j k a b : ℕ) : ℤ :=
  if j ≤ a ∧ k ≤ b then
    c * ((8-j).choose (a-j) : ℤ) * ((12-k).choose (b-k) : ℤ)
  else 0

theorem tensorIntegerCoefficient_cast (c : ℤ) (j k a b : ℕ) :
    (tensorIntegerCoefficient c j k a b : ℝ) =
      (c : ℝ) * degreeElevationCoefficient 8 j a *
        degreeElevationCoefficient 12 k b := by
  by_cases ha : j ≤ a <;> by_cases hb : k ≤ b <;>
    simp [tensorIntegerCoefficient, degreeElevationCoefficient, ha, hb]

theorem bernsteinTransform_integer_add (f g : ℕ → ℕ → ℤ) (t v : ℝ) :
    bernsteinTransform (fun a b => ((f a b + g a b : ℤ) : ℝ)) t v =
      bernsteinTransform (fun a b => (f a b : ℝ)) t v +
        bernsteinTransform (fun a b => (g a b : ℝ)) t v := by
  simp only [Int.cast_add, bernsteinTransform_add]

theorem tensorIntegerCoefficient_reconstruction
    (c : ℤ) (j k : ℕ) (hj : j ≤ 8) (hk : k ≤ 12) (t v : ℝ) :
    bernsteinTransform (fun a b => (tensorIntegerCoefficient c j k a b : ℝ)) t v =
      (c : ℝ)*t^j*v^k := by
  unfold bernsteinTransform
  simp_rw [tensorIntegerCoefficient_cast]
  exact tensor_monomial_bernstein_reconstruction 8 12 j k hj hk (c : ℝ) t v

end
end SQBCompactRow
