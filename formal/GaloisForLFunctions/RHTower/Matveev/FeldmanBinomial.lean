import GaloisForLFunctions.RHTower.Matveev.LinearFormBasic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Fel'dman's integer-valued binomial basis

The auxiliary matrix of an effective linear-form construction has entries built from powers of the
direction coefficients.  Powers are the wrong basis: `|δ|^k` grows with the height of the linear
form to the full multiplicity, and the terminal integrality step cannot tolerate coefficients of
that size.

Fel'dman's polynomials

`Δ(z; k) = (z+1)(z+2)⋯(z+k) / k!`

are the repair.  They take integer values at every integer — a product of `k` consecutive integers
is divisible by `k!`, for negative arguments as well, by sign reversal or by containing zero — and
their size is `(|z| + k)^k / k!` rather than `|z|^k`, a saving of `k!`.

At an integer argument the value is a binomial coefficient, so it is bounded by `2^{z + k}` rather
than by a power of `z`: on a range of arguments of length `S` the basis costs `S + k` in the
logarithm where the power basis costs `k log S`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

/-- The product of the `k` consecutive integers just above `z`. -/
def consecutiveProd (k : ℕ) (z : ℤ) : ℤ := ∏ j ∈ range k, (z + (j : ℤ) + 1)

@[simp] theorem consecutiveProd_zero (z : ℤ) : consecutiveProd 0 z = 1 := by
  simp [consecutiveProd]

theorem consecutiveProd_succ (k : ℕ) (z : ℤ) :
    consecutiveProd (k + 1) z = consecutiveProd k z * (z + (k : ℤ) + 1) := by
  rw [consecutiveProd, consecutiveProd, Finset.prod_range_succ]

/-- On nonnegative arguments the product is an ascending factorial. -/
theorem consecutiveProd_natCast (k n : ℕ) :
    consecutiveProd k (n : ℤ) = (((n + 1).ascFactorial k : ℕ) : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [consecutiveProd_succ, ih, Nat.ascFactorial_succ]
      push_cast
      ring

/-- A descending product of integers is a descending factorial. -/
theorem prod_range_sub_eq_descFactorial (m : ℕ) : ∀ k : ℕ, k ≤ m →
    ∏ j ∈ range k, ((m : ℤ) - (j : ℤ)) = ((m.descFactorial k : ℕ) : ℤ)
  | 0, _ => by simp
  | k + 1, hk => by
      rw [Finset.prod_range_succ, prod_range_sub_eq_descFactorial m k (by omega),
        Nat.descFactorial_succ]
      have hcast : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by
        have : k ≤ m := by omega
        omega
      push_cast [hcast]
      ring

/-- A product of `k` consecutive integers is divisible by `k!`. -/
theorem factorial_dvd_consecutiveProd (k : ℕ) (z : ℤ) :
    ((k.factorial : ℕ) : ℤ) ∣ consecutiveProd k z := by
  rcases le_or_gt 0 z with hz | hz
  · -- nonnegative: an ascending factorial
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [consecutiveProd_natCast]
    exact_mod_cast Nat.factorial_dvd_ascFactorial (n + 1) k
  · -- negative: either the product contains zero, or it is a signed descending factorial
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, z = -((m : ℤ) + 1) := by
      refine ⟨(-z - 1).toNat, ?_⟩
      have h1 : 0 ≤ -z - 1 := by omega
      rw [Int.toNat_of_nonneg h1]
      ring
    by_cases hmk : m + 1 ≤ k
    · -- the factor at `j = m` vanishes
      have hmem : m ∈ range k := mem_range.mpr (by omega)
      have hzero : consecutiveProd k (-((m : ℤ) + 1)) = 0 := by
        rw [consecutiveProd, Finset.prod_eq_zero hmem]
        ring
      rw [hzero]
      exact dvd_zero _
    · -- all factors are negative
      have hk : k ≤ m := by omega
      have hsplit : consecutiveProd k (-((m : ℤ) + 1))
          = (-1 : ℤ) ^ k * ((m.descFactorial k : ℕ) : ℤ) := by
        rw [consecutiveProd]
        rw [show ∏ j ∈ range k, (-((m : ℤ) + 1) + (j : ℤ) + 1)
            = ∏ j ∈ range k, (-1 : ℤ) * (((m : ℤ) - (j : ℤ))) from
          Finset.prod_congr rfl fun j _ => by ring]
        rw [Finset.prod_mul_distrib, Finset.prod_const, card_range,
          prod_range_sub_eq_descFactorial m k hk]
      rw [hsplit]
      refine Dvd.dvd.mul_left ?_ _
      exact_mod_cast Nat.factorial_dvd_descFactorial m k

/-- **Fel'dman's binomial value** `Δ(z; k) = (z+1)⋯(z+k)/k!`, an integer at every integer. -/
def feldmanBinom (k : ℕ) (z : ℤ) : ℤ := consecutiveProd k z / ((k.factorial : ℕ) : ℤ)

theorem feldmanBinom_mul_factorial (k : ℕ) (z : ℤ) :
    feldmanBinom k z * ((k.factorial : ℕ) : ℤ) = consecutiveProd k z := by
  rw [feldmanBinom, Int.ediv_mul_cancel (factorial_dvd_consecutiveProd k z)]

@[simp] theorem feldmanBinom_zero (z : ℤ) : feldmanBinom 0 z = 1 := by
  simp [feldmanBinom]

/-! ## The height gain -/

/-- The consecutive product is bounded by the `k`-th power of the shifted height. -/
theorem abs_consecutiveProd_le (k : ℕ) (z : ℤ) :
    |consecutiveProd k z| ≤ (|z| + (k : ℤ)) ^ k := by
  rw [consecutiveProd, Finset.abs_prod]
  calc ∏ j ∈ range k, |z + (j : ℤ) + 1| ≤ ∏ _j ∈ range k, (|z| + (k : ℤ)) := by
        refine Finset.prod_le_prod (fun j _ => abs_nonneg _) fun j hj => ?_
        have hjk : (j : ℤ) + 1 ≤ (k : ℤ) := by
          have := mem_range.mp hj
          omega
        calc |z + (j : ℤ) + 1| ≤ |z| + |(j : ℤ) + 1| := by
              rw [add_assoc]
              exact abs_add_le _ _
          _ ≤ |z| + (k : ℤ) := by
              have : |(j : ℤ) + 1| = (j : ℤ) + 1 := abs_of_nonneg (by positivity)
              rw [this]
              omega
    _ = (|z| + (k : ℤ)) ^ k := by rw [Finset.prod_const, card_range]

/-- **The height gain.**  The Fel'dman value is smaller than the plain power by the full
factorial. -/
theorem abs_feldmanBinom_mul_factorial_le (k : ℕ) (z : ℤ) :
    |feldmanBinom k z| * ((k.factorial : ℕ) : ℤ) ≤ (|z| + (k : ℤ)) ^ k := by
  have hfac : (0 : ℤ) < ((k.factorial : ℕ) : ℤ) := by
    exact_mod_cast k.factorial_pos
  have hmul : |feldmanBinom k z| * ((k.factorial : ℕ) : ℤ)
      = |feldmanBinom k z * ((k.factorial : ℕ) : ℤ)| := by
    rw [abs_mul, abs_of_pos hfac]
  rw [hmul, feldmanBinom_mul_factorial]
  exact abs_consecutiveProd_le k z

/-! ## The binomial form at integer samples -/

/-- Every binomial coefficient is bounded by the full row sum. -/
theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  rcases le_or_gt k n with hk | hk
  · calc n.choose k ≤ ∑ i ∈ Finset.range (n + 1), n.choose i :=
          Finset.single_le_sum (f := fun i => n.choose i) (fun i _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt hk]
    positivity

/-- **At a nonnegative integer the Fel'dman value is a binomial coefficient.** -/
theorem feldmanBinom_natCast (k n : ℕ) :
    feldmanBinom k (n : ℤ) = (((n + k).choose k : ℕ) : ℤ) := by
  have hfac : ((k.factorial : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  rw [feldmanBinom, consecutiveProd_natCast, Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hfac)]

/-- **The sample-range height gain.**  On a range of nonnegative integer arguments the Fel'dman
value grows only exponentially in the argument, where a power of the argument would grow like
`n^k`. -/
theorem feldmanBinom_natCast_le (k n : ℕ) :
    feldmanBinom k (n : ℤ) ≤ 2 ^ (n + k) := by
  rw [feldmanBinom_natCast]
  exact_mod_cast choose_le_two_pow (n + k) k

end GaloisForLFunctions.RHTower.Matveev
