import GaloisForLFunctions.HTGeometry.ArithmeticControlledLeibniz
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Literal integer carries require source transport

The source `c_n(x) = floor(n*x) - n*floor(x)` has zero-or-one additive defects
and linear size bounds. Its exact multiplicative law is transported:
`c_(mn)(x) = c_m(n*x) + m*c_n(x)`.

The quadratic lift and the full circle-valued exponential family obey corresponding
nonlinear transported laws. All statements concern the explicitly defined integer source.

Forgetting transport is possible exactly at integer offsets, where every carry vanishes.
This rules out this particular attempted nonzero source instance of the ordinary arithmetic
Leibniz obstruction. It does not rule out transport-aware constructions, identify any offset
with a Xi parameter, or establish an RH consequence.
-/

namespace GaloisForLFunctions.HTGeometry.IntegerCarryTransport

noncomputable def carry (n : ℕ) (x : ℝ) : ℤ := ⌊(n : ℝ) * x⌋ - (n : ℤ) * ⌊x⌋

theorem carry_zero (x : ℝ) : carry 0 x = 0 := by simp [carry]

theorem carry_integer (n : ℕ) (z : ℤ) : carry n (z : ℝ) = 0 := by
  have heq : (n : ℝ) * (z : ℝ) = ((n : ℤ) * z : ℤ) := by push_cast; rfl
  unfold carry
  rw [heq, Int.floor_intCast, Int.floor_intCast, sub_self]

/-- Multiplication transports the phase argument; it is not the ordinary Leibniz law. -/
theorem carry_mul (m n : ℕ) (x : ℝ) :
    carry (m * n) x = carry m ((n : ℝ) * x) + (m : ℤ) * carry n x := by
  simp only [carry, Nat.cast_mul, mul_assoc]
  ring

/-- Every elementary additive discrepancy is literally a zero-or-one integer. -/
theorem carry_add_defect (m n : ℕ) (x : ℝ) :
    carry (m + n) x - carry m x - carry n x = 0 ∨
    carry (m + n) x - carry m x - carry n x = 1 := by
  have hlow := Int.le_floor_add ((m : ℝ) * x) ((n : ℝ) * x)
  have hupp := Int.le_floor_add_floor ((m : ℝ) * x) ((n : ℝ) * x)
  have heq : carry (m + n) x - carry m x - carry n x =
      ⌊(m : ℝ) * x + (n : ℝ) * x⌋ - ⌊(m : ℝ) * x⌋ - ⌊(n : ℝ) * x⌋ := by
    simp only [carry, Nat.cast_add, add_mul]
    ring
  rw [heq]
  omega

/-- The literal carry is nonnegative and bounded by its input multiplicity. -/
theorem carry_bounds (n : ℕ) (x : ℝ) : 0 ≤ carry n x ∧ carry n x ≤ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlow : (n : ℤ) * ⌊x⌋ ≤ ⌊(n : ℝ) * x⌋ := by
    apply Int.le_floor.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left (Int.floor_le x) hn
  have hupp : (carry n x : ℝ) ≤ n := by
    have hx : x ≤ (⌊x⌋ : ℝ) + 1 := (Int.lt_floor_add_one x).le
    have h := mul_le_mul_of_nonneg_left hx hn
    have hnx := Int.floor_le ((n : ℝ) * x)
    dsimp [carry]
    push_cast
    nlinarith
  constructor
  · exact sub_nonneg.mpr hlow
  · exact_mod_cast hupp

theorem norm_carry_le (n : ℕ) (x : ℝ) : ‖(carry n x : ℝ)‖ ≤ n := by
  obtain ⟨hlow, hupp⟩ := carry_bounds n x
  have hlowR : (0 : ℝ) ≤ carry n x := by exact_mod_cast hlow
  rw [Real.norm_eq_abs, abs_of_nonneg hlowR]
  exact_mod_cast hupp

/-- A phase with no carry at any integer scale is already an integer. -/
theorem all_carries_zero_iff_integer (x : ℝ) :
    (∀ n, carry n x = 0) ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro h
    refine ⟨⌊x⌋, ?_⟩
    have hnonneg : 0 ≤ x - (⌊x⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le x)
    have hz : x - (⌊x⌋ : ℝ) = 0 := by
      by_contra hne
      have hp : 0 < x - (⌊x⌋ : ℝ) := lt_of_le_of_ne hnonneg (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (x - (⌊x⌋ : ℝ)))
      have hnlarge : 1 < (n : ℝ) * (x - (⌊x⌋ : ℝ)) := (div_lt_iff₀ hp).mp hn
      have heq : ⌊(n : ℝ) * x⌋ = (n : ℤ) * ⌊x⌋ := sub_eq_zero.mp (h n)
      have hsmall := Int.lt_floor_add_one ((n : ℝ) * x)
      rw [heq] at hsmall
      push_cast at hsmall
      nlinarith
    exact sub_eq_zero.mp hz
  · rintro ⟨z, rfl⟩ n
    exact carry_integer n z

/-- Complete classification of when forgetting source transport happens to be legal. -/
theorem untwisted_leibniz_iff_integer (x : ℝ) :
    (∀ m n, carry (m * n) x = (m : ℤ) * carry n x + (n : ℤ) * carry m x) ↔
      ∃ z : ℤ, x = z := by
  constructor
  · intro h
    have hf : IsArithmeticLeibniz (fun n => (carry n x : ℝ)) := by
      intro m n
      have hh := congrArg (fun z : ℤ => (z : ℝ)) (h m n)
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, smul_eq_mul] using hh
    have hz := hf.eq_zero_of_linear_bound (A := 1) (fun n => by simpa using norm_carry_le n x)
    apply (all_carries_zero_iff_integer x).mp
    intro n
    have hh : (carry n x : ℝ) = 0 := congrFun hz n
    exact_mod_cast hh
  · rintro ⟨z, rfl⟩ m n
    simp [carry_integer]

/-- The quadratic lift retains both the transported argument and the square weight. -/
noncomputable def second (n : ℕ) (x : ℝ) : ℝ := (carry n x : ℝ) ^ (2 : ℕ) / 2

theorem second_mul (m n : ℕ) (x : ℝ) :
    second (m * n) x = second m ((n : ℝ) * x) + (m : ℝ) ^ (2 : ℕ) * second n x +
      (m : ℝ) * (carry m ((n : ℝ) * x) : ℝ) * (carry n x : ℝ) := by
  simp only [second, carry_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

/-- The fixed integer source generates a circle-valued nonlinear family without selecting
a logarithm branch or a phase correction. -/
noncomputable def phase (n : ℕ) (x t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (carry n x : ℂ))

theorem phase_mul (m n : ℕ) (x t : ℝ) :
    phase (m * n) x t = phase m ((n : ℝ) * x) t * phase n x t ^ m := by
  simp only [phase, carry_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem norm_phase (n : ℕ) (x t : ℝ) : ‖phase n x t‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

end GaloisForLFunctions.HTGeometry.IntegerCarryTransport

