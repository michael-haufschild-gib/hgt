/-
The elementary non-resonance of square roots of non-squares.

The frontier frequencies are square roots of rationals, and their commensurability classes are indexed
by squarefree kernels `d`.  A class contributes fully to the frontier sum only when `n√d` is close to
an integer.  The elementary obstruction to that is:

    **for a non-square positive integer `m`, the distance from `√m` to the nearest integer is at least
    `1/(2√m + 1)`.**

The proof is the factorisation `(√m - k)(√m + k) = m - k²`: the right side is a nonzero integer, so it
has absolute value at least `1`, while the second factor is at most `2√m + 1` in the only case where
the first can be small.

Applied with `m = n²d`, this gives `‖n√d‖ ≫ 1/(n√d)`, so no single class can resonate with a given `n`
beyond that quantitative limit.  The open problem is the *simultaneous* version — how many classes can
resonate with one `n` at once — for which no comparable elementary bound exists.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace HTGeometry

open Real

/-- **A non-square integer's square root is at distance at least `1/(2√m + 1)` from every integer.** -/
theorem dist_sqrt_int_lower {m : ℕ} (hm : 0 < m) (hns : ∀ j : ℤ, j * j ≠ (m : ℤ)) (k : ℤ) :
    1 / (2 * Real.sqrt m + 1) ≤ |Real.sqrt m - (k : ℝ)| := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hsq : Real.sqrt m ^ 2 = (m : ℝ) := Real.sq_sqrt hm0
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hm1
  have hden : (0 : ℝ) < 2 * Real.sqrt m + 1 := by linarith
  have hsmall : 1 / (2 * Real.sqrt m + 1) ≤ 1 := by
    rw [div_le_one hden]; linarith
  rcases lt_or_ge k 0 with hk | hk
  · -- negative `k`: the distance exceeds `1`
    have hkr : (k : ℝ) < 0 := by exact_mod_cast hk
    have : (1 : ℝ) ≤ Real.sqrt m - (k : ℝ) := by linarith
    calc 1 / (2 * Real.sqrt m + 1) ≤ 1 := hsmall
      _ ≤ Real.sqrt m - (k : ℝ) := this
      _ ≤ |Real.sqrt m - (k : ℝ)| := le_abs_self _
  · -- nonnegative `k`
    have hkr : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rcases lt_or_ge (Real.sqrt m + 1) (k : ℝ) with hbig | hle
    · -- `k` far above `√m`
      have : (1 : ℝ) ≤ (k : ℝ) - Real.sqrt m := by linarith
      calc 1 / (2 * Real.sqrt m + 1) ≤ 1 := hsmall
        _ ≤ (k : ℝ) - Real.sqrt m := this
        _ ≤ |Real.sqrt m - (k : ℝ)| := by
            rw [abs_sub_comm]; exact le_abs_self _
    · -- the main case: factorise
      have hne : (m : ℤ) - k * k ≠ 0 := by
        intro hz
        exact hns k (by linarith [hz])
      have hone : (1 : ℝ) ≤ |(m : ℝ) - (k : ℝ) * (k : ℝ)| := by
        have : (1 : ℤ) ≤ |(m : ℤ) - k * k| := Int.one_le_abs hne
        calc (1 : ℝ) ≤ ((|(m : ℤ) - k * k| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(m : ℝ) - (k : ℝ) * (k : ℝ)| := by push_cast; ring_nf
      have hfac : |Real.sqrt m - (k : ℝ)| * (Real.sqrt m + (k : ℝ))
          = |(m : ℝ) - (k : ℝ) * (k : ℝ)| := by
        have hpos : (0 : ℝ) ≤ Real.sqrt m + (k : ℝ) := by positivity
        rw [← abs_of_nonneg hpos, ← abs_mul]
        congr 1
        nlinarith [hsq]
      have hbound : Real.sqrt m + (k : ℝ) ≤ 2 * Real.sqrt m + 1 := by linarith
      have hposfac : (0 : ℝ) < Real.sqrt m + (k : ℝ) := by linarith
      rw [div_le_iff₀ hden]
      calc (1 : ℝ) ≤ |(m : ℝ) - (k : ℝ) * (k : ℝ)| := hone
        _ = |Real.sqrt m - (k : ℝ)| * (Real.sqrt m + (k : ℝ)) := hfac.symm
        _ ≤ |Real.sqrt m - (k : ℝ)| * (2 * Real.sqrt m + 1) :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

/-- **Hence the square root of a non-square is irrational-looking at every scale**: it never comes
within `1/(2√m + 1)` of an integer. -/
theorem sqrt_nonsquare_not_near_integer {m : ℕ} (hm : 0 < m)
    (hns : ∀ j : ℤ, j * j ≠ (m : ℤ)) (k : ℤ) :
    Real.sqrt m ≠ (k : ℝ) := by
  intro heq
  have h := dist_sqrt_int_lower hm hns k
  have hzero : |Real.sqrt m - (k : ℝ)| = 0 := by rw [heq, sub_self, abs_zero]
  rw [hzero] at h
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hm1
  have : (0 : ℝ) < 1 / (2 * Real.sqrt m + 1) := by positivity
  linarith

/-- The bound is sharp in order: for `m = k² + 1` the distance is `≍ 1/(2√m)`. -/
theorem dist_bound_order (k : ℕ) (hk : 0 < k) :
    Real.sqrt ((k : ℝ) ^ 2 + 1) - (k : ℝ) ≤ 1 / (2 * (k : ℝ)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnn : (0 : ℝ) ≤ (k : ℝ) ^ 2 + 1 := by positivity
  have hle : Real.sqrt ((k : ℝ) ^ 2 + 1) ≤ (k : ℝ) + 1 / (2 * (k : ℝ)) := by
    rw [show (k : ℝ) + 1 / (2 * (k : ℝ)) = Real.sqrt (((k : ℝ) + 1 / (2 * (k : ℝ))) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have : ((k : ℝ) + 1 / (2 * (k : ℝ))) ^ 2
        = (k : ℝ) ^ 2 + 1 + 1 / (4 * (k : ℝ) ^ 2) := by
      field_simp
      ring
    rw [this]
    have : (0 : ℝ) < 1 / (4 * (k : ℝ) ^ 2) := by positivity
    linarith
  linarith

end HTGeometry
