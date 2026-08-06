import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The bigraded Hilbert identity of a bidegree-`(1,1)` complete intersection

The Hilbert series of the bigraded coordinate ring of `P^m × P^n` modulo a regular sequence of
`m + n` forms of bidegree `(1,1)` is

```text
(1 - s t)^(m+n) / ((1 - s)^(m+1) (1 - t)^(n+1)),
```

so its coefficient in bidegree `(d, e)` is the alternating sum

```text
∑_(k ≤ m+n) (-1)^k binom(m+n, k) binom(d-k+m, m) binom(e-k+n, n).
```

The identity proved here is that this sum is the constant `binom(m+n, m)` for every bidegree beyond
the numerator — the Hilbert polynomial of such an intersection is constant, and the constant is the
bihomogeneous Bézout number.

The mechanism is finite differences: after reversing the summation index the sum is the
`(m+n)`-th forward difference of the polynomial `x ↦ binom(x+m, m) · binom(x+c+n, n)`, which has
degree exactly `m + n` and leading coefficient `1 / (m! n!)`, so the difference is the constant
`(m+n)! / (m! n!)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped Nat

/-! ## Rising products and binomial coefficients -/

/-- **A rising product is a factorial times a binomial coefficient.** -/
theorem prod_range_add_one_eq_factorial_mul_choose (m j : ℕ) :
    ∏ i ∈ Finset.range m, (j + i + 1) = m ! * (j + m).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    have hkey : (j + m + 1) * (j + m).choose m = (j + m + 1).choose (m + 1) * (m + 1) :=
      Nat.add_one_mul_choose_eq _ _
    calc m ! * (j + m).choose m * (j + m + 1)
        = m ! * ((j + m + 1) * (j + m).choose m) := by ring
      _ = m ! * ((j + m + 1).choose (m + 1) * (m + 1)) := by rw [hkey]
      _ = (m + 1) * m ! * (j + (m + 1)).choose (m + 1) := by
          rw [show j + (m + 1) = j + m + 1 from rfl]; ring

/-! ## The binomial coefficient as a polynomial -/

/-- The polynomial `x ↦ binom(x + m, m)`. -/
noncomputable def choosePoly (m : ℕ) : ℚ[X] :=
  C ((m ! : ℚ)⁻¹) * ∏ i ∈ Finset.range m, (X + C ((i : ℚ) + 1))

theorem monic_prod_X_add_C (m : ℕ) :
    (∏ i ∈ Finset.range m, (X + C ((i : ℚ) + 1))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem natDegree_prod_X_add_C (m : ℕ) :
    (∏ i ∈ Finset.range m, (X + C ((i : ℚ) + 1))).natDegree = m := by
  rw [natDegree_prod _ _ fun _ _ => (monic_X_add_C _).ne_zero]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem natDegree_choosePoly (m : ℕ) : (choosePoly m).natDegree = m := by
  rw [choosePoly, natDegree_C_mul (by simpa using Nat.factorial_ne_zero m),
    natDegree_prod_X_add_C]

theorem leadingCoeff_choosePoly (m : ℕ) : (choosePoly m).leadingCoeff = ((m ! : ℚ)⁻¹) := by
  rw [choosePoly, leadingCoeff_mul, leadingCoeff_C, (monic_prod_X_add_C m).leadingCoeff, mul_one]

/-- **The polynomial computes the binomial coefficient at every natural argument.** -/
theorem eval_choosePoly (m j : ℕ) :
    (choosePoly m).eval (j : ℚ) = (((j + m).choose m : ℕ) : ℚ) := by
  have hfac : ((m ! : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hprod : (∏ i ∈ Finset.range m, ((j : ℚ) + ((i : ℚ) + 1)))
      = ((∏ i ∈ Finset.range m, (j + i + 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [choosePoly, eval_mul, eval_C, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  rw [hprod, prod_range_add_one_eq_factorial_mul_choose]
  push_cast
  rw [inv_mul_cancel_left₀ hfac]

/-! ## The shifted product -/

/-- The polynomial `x ↦ binom(x + m, m) · binom(x + c + n, n)`. -/
noncomputable def bezoutPoly (m n c : ℕ) : ℚ[X] :=
  choosePoly m * (choosePoly n).comp (X + C (c : ℚ))

theorem choosePoly_ne_zero (m : ℕ) : choosePoly m ≠ 0 := by
  intro h
  have hl := leadingCoeff_choosePoly m
  rw [h, leadingCoeff_zero] at hl
  exact (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))) hl.symm

theorem natDegree_X_add_C_ne_zero (c : ℕ) : ((X : ℚ[X]) + C (c : ℚ)).natDegree ≠ 0 := by
  rw [natDegree_X_add_C]
  exact one_ne_zero

theorem leadingCoeff_choosePoly_comp (n c : ℕ) :
    ((choosePoly n).comp (X + C (c : ℚ))).leadingCoeff = ((n ! : ℚ)⁻¹) := by
  rw [leadingCoeff_comp (natDegree_X_add_C_ne_zero c), leadingCoeff_choosePoly,
    (monic_X_add_C (c : ℚ)).leadingCoeff, one_pow, mul_one]

theorem choosePoly_comp_ne_zero (n c : ℕ) : (choosePoly n).comp (X + C (c : ℚ)) ≠ 0 := by
  intro h
  have hl := leadingCoeff_choosePoly_comp n c
  rw [h, leadingCoeff_zero] at hl
  exact (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))) hl.symm

theorem natDegree_bezoutPoly (m n c : ℕ) : (bezoutPoly m n c).natDegree = m + n := by
  rw [bezoutPoly, natDegree_mul (choosePoly_ne_zero m) (choosePoly_comp_ne_zero n c),
    natDegree_comp, natDegree_choosePoly, natDegree_choosePoly, natDegree_X_add_C, mul_one]

theorem leadingCoeff_bezoutPoly (m n c : ℕ) :
    (bezoutPoly m n c).leadingCoeff = ((m ! : ℚ)⁻¹) * ((n ! : ℚ)⁻¹) := by
  rw [bezoutPoly, leadingCoeff_mul, leadingCoeff_choosePoly, leadingCoeff_choosePoly_comp]

theorem eval_bezoutPoly (m n c j : ℕ) :
    (bezoutPoly m n c).eval (j : ℚ)
      = (((j + m).choose m : ℕ) : ℚ) * (((j + c + n).choose n : ℕ) : ℚ) := by
  rw [bezoutPoly, eval_mul, eval_comp]
  simp only [eval_add, eval_X, eval_C]
  rw [eval_choosePoly, show ((j : ℚ) + (c : ℚ)) = ((j + c : ℕ) : ℚ) by push_cast; ring,
    eval_choosePoly]

/-! ## The Hilbert identity -/

/-- **The leading behaviour of the shifted product is the bihomogeneous Bézout number.** -/
theorem fwdDiff_iter_bezoutPoly (m n c : ℕ) (x : ℚ) :
    (fwdDiff (1 : ℚ))^[m + n] (fun y => eval y (bezoutPoly m n c)) x
      = (((m + n).choose m : ℕ) : ℚ) := by
  have hfd := Polynomial.fwdDiff_iter_degree_eq_factorial (bezoutPoly m n c)
  rw [natDegree_bezoutPoly] at hfd
  have hval := congrFun hfd x
  rw [hval, leadingCoeff_bezoutPoly]
  have hfacs : ((m + n).choose m : ℕ) * m ! * n ! = (m + n)! := by
    rw [Nat.choose_symm_add]
    exact Nat.add_choose_mul_factorial_mul_factorial m n
  have hm : ((m ! : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hn : ((n ! : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hcast : (((m + n).choose m : ℕ) : ℚ) * (m ! : ℚ) * (n ! : ℚ) = ((m + n)! : ℚ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) hfacs
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
  rw [← hcast]
  field_simp

/-- **The bigraded Hilbert identity.**  The alternating sum weighting the monomial counts of
`P^m × P^n` by the Koszul numerator of `m + n` divisors of bidegree `(1,1)` is the constant
`binom(m+n, m)` — the bihomogeneous Bézout number — in every bidegree past the numerator. -/
theorem alternating_sum_choose_mul_choose (m n c j : ℕ) :
    ∑ k ∈ Finset.range (m + n + 1),
        ((-1 : ℤ) ^ (m + n - k) * ((m + n).choose k : ℤ)) •
          ((((j + k + m).choose m : ℕ) : ℚ) * (((j + k + c + n).choose n : ℕ) : ℚ))
      = (((m + n).choose m : ℕ) : ℚ) := by
  have hsum := fwdDiff_iter_eq_sum_shift (1 : ℚ) (fun y => eval y (bezoutPoly m n c)) (m + n)
    ((j : ℕ) : ℚ)
  rw [fwdDiff_iter_bezoutPoly] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [show ((j : ℚ) + k • (1 : ℚ)) = ((j + k : ℕ) : ℚ) by push_cast; ring, eval_bezoutPoly]

/-- The same identity over the integers. -/
theorem alternating_sum_choose_mul_choose_int (m n c j : ℕ) :
    ∑ k ∈ Finset.range (m + n + 1),
        (-1 : ℤ) ^ (m + n - k) * ((m + n).choose k : ℤ) *
          (((j + k + m).choose m : ℕ) : ℤ) * (((j + k + c + n).choose n : ℕ) : ℤ)
      = (((m + n).choose m : ℕ) : ℤ) := by
  have hq := alternating_sum_choose_mul_choose m n c j
  have hcast : ((∑ k ∈ Finset.range (m + n + 1),
      (-1 : ℤ) ^ (m + n - k) * ((m + n).choose k : ℤ) *
        (((j + k + m).choose m : ℕ) : ℤ) * (((j + k + c + n).choose n : ℕ) : ℤ) : ℤ) : ℚ)
      = (((m + n).choose m : ℕ) : ℚ) := by
    rw [← hq]
    push_cast [zsmul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  exact_mod_cast hcast

end GaloisForLFunctions.HTGeometry
