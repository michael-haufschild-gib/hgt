import GaloisForLFunctions.RHTower.HadamardRegularizationLaw

/-!
# The factorial multiplier fails positivity at every off-diagonal pair

A positive kernel obeys `B(m,n)² ≤ B(m,m)·B(n,n)`.  The reciprocal-factorial multiplier
`B(m,n) = 1/(m+n)!` obeys the **reverse** inequality, strictly whenever `m ≠ n`, because the
factorial is strictly log-convex:

`((m+n)!)² < (2m)!·(2n)!`  for `m ≠ n`.

So every two-by-two minor of the multiplier on distinct indices is negative: the obstruction found
at the corner is not a corner artefact but is present at every scale and every pair.  No positive
kernel agrees with the reciprocal factorials even on two distinct indices, so no positivity-
preserving regularization reproduces factorial damping anywhere.
-/

open Nat

namespace RHTower

/-- Moving factorial mass outward increases the product: `(a+d)!² ≤ a!·(a+2d)!`. -/
theorem factorial_sq_le_aux : ∀ (d a : ℕ), (a + d)! * (a + d)! ≤ a ! * (a + 2 * d)!
  | 0, a => by simp
  | (d + 1), a => by
      have ih := factorial_sq_le_aux d (a + 1)
      have hl : a + (d + 1) = (a + 1) + d := by omega
      have hr : (a + 1) + 2 * d = a + 2 * d + 1 := by omega
      have hstep : (a + 1)! * ((a + 1) + 2 * d)! ≤ a ! * (a + 2 * (d + 1))! := by
        rw [hr]
        have h1 : (a + 1)! = (a + 1) * a ! := Nat.factorial_succ a
        have h2 : a + 2 * (d + 1) = (a + 2 * d + 1) + 1 := by omega
        rw [h1, h2, Nat.factorial_succ]
        have hle : a + 1 ≤ a + 2 * d + 1 + 1 := by omega
        calc (a + 1) * a ! * (a + 2 * d + 1)!
            = (a + 1) * (a ! * (a + 2 * d + 1)!) := by ring
          _ ≤ (a + 2 * d + 1 + 1) * (a ! * (a + 2 * d + 1)!) :=
              Nat.mul_le_mul_right _ hle
          _ = a ! * ((a + 2 * d + 1 + 1) * (a + 2 * d + 1)!) := by ring
      rw [hl]
      exact le_trans ih hstep

/-- The strict form, for a nonzero displacement. -/
theorem factorial_sq_lt_aux (d a : ℕ) :
    (a + (d + 1))! * (a + (d + 1))! < a ! * (a + 2 * (d + 1))! := by
  have ih := factorial_sq_le_aux d (a + 1)
  have hl : a + (d + 1) = (a + 1) + d := by omega
  have hr : (a + 1) + 2 * d = a + 2 * d + 1 := by omega
  have hstep : (a + 1)! * ((a + 1) + 2 * d)! < a ! * (a + 2 * (d + 1))! := by
    rw [hr]
    have h1 : (a + 1)! = (a + 1) * a ! := Nat.factorial_succ a
    have h2 : a + 2 * (d + 1) = (a + 2 * d + 1) + 1 := by omega
    rw [h1, h2, Nat.factorial_succ]
    have hlt : a + 1 < a + 2 * d + 1 + 1 := by omega
    have hpos : 0 < a ! * (a + 2 * d + 1)! :=
      Nat.mul_pos (Nat.factorial_pos a) (Nat.factorial_pos _)
    calc (a + 1) * a ! * (a + 2 * d + 1)!
        = (a + 1) * (a ! * (a + 2 * d + 1)!) := by ring
      _ < (a + 2 * d + 1 + 1) * (a ! * (a + 2 * d + 1)!) :=
          (Nat.mul_lt_mul_right hpos).mpr hlt
      _ = a ! * ((a + 2 * d + 1 + 1) * (a + 2 * d + 1)!) := by ring
  rw [hl]
  exact lt_of_le_of_lt ih hstep

/-- **Log-convexity of the factorial**, in the form the Cauchy--Schwarz test needs. -/
theorem factorial_add_sq_le (m n : ℕ) : (m + n)! * (m + n)! ≤ (2 * m)! * (2 * n)! := by
  rcases le_total m n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hx := factorial_sq_le_aux d (2 * m)
    have h1 : m + (m + d) = 2 * m + d := by omega
    have h2 : 2 * (m + d) = 2 * m + 2 * d := by omega
    rw [h1, h2]
    exact hx
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hx := factorial_sq_le_aux d (2 * n)
    have h1 : n + d + n = 2 * n + d := by omega
    have h2 : 2 * (n + d) = 2 * n + 2 * d := by omega
    rw [h1, h2, mul_comm ((2 * n + 2 * d)!) ((2 * n)!)]
    exact hx

/-- **Strict log-convexity off the diagonal.** -/
theorem factorial_add_sq_lt {m n : ℕ} (h : m ≠ n) :
    (m + n)! * (m + n)! < (2 * m)! * (2 * n)! := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hx := factorial_sq_lt_aux d (2 * m)
    have h1 : m + (m + d + 1) = 2 * m + (d + 1) := by omega
    have h2 : 2 * (m + d + 1) = 2 * m + 2 * (d + 1) := by omega
    rw [h1, h2]
    exact hx
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hx := factorial_sq_lt_aux d (2 * n)
    have h1 : n + d + 1 + n = 2 * n + (d + 1) := by omega
    have h2 : 2 * (n + d + 1) = 2 * n + 2 * (d + 1) := by omega
    rw [h1, h2, mul_comm ((2 * n + 2 * (d + 1))!) ((2 * n)!)]
    exact hx

/-- The two-by-two block of the reciprocal-factorial multiplier at a pair of indices. -/
noncomputable def reciprocalFactorialBlock (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / ((2 * m)! : ℝ), 1 / ((m + n)! : ℝ); 1 / ((m + n)! : ℝ), 1 / ((2 * n)! : ℝ)]

theorem reciprocalFactorialBlock_det_neg {m n : ℕ} (h : m ≠ n) :
    (reciprocalFactorialBlock m n).det < 0 := by
  have hlt := factorial_add_sq_lt h
  have hcast : (((m + n)! : ℕ) : ℝ) * (((m + n)! : ℕ) : ℝ)
      < (((2 * m)! : ℕ) : ℝ) * (((2 * n)! : ℕ) : ℝ) := by exact_mod_cast hlt
  have hmn : (0 : ℝ) < (((m + n)! : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + n)
  have h2m : (0 : ℝ) < (((2 * m)! : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * m)
  have h2n : (0 : ℝ) < (((2 * n)! : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * n)
  rw [reciprocalFactorialBlock, Matrix.det_fin_two_of, sub_neg, one_div_mul_one_div,
    one_div_mul_one_div]
  exact div_lt_div_of_pos_left one_pos (by positivity) hcast

/-- **The multiplier fails positivity at every off-diagonal pair.**  Not a corner artefact: for
every `m ≠ n`, whatever the scale, the two-by-two block is not positive semidefinite. -/
theorem reciprocalFactorialBlock_not_posSemidef {m n : ℕ} (h : m ≠ n) :
    ¬ (reciprocalFactorialBlock m n).PosSemidef := by
  intro hpsd
  exact absurd (reciprocalFactorialBlock_det_neg h) (not_lt_of_ge hpsd.det_nonneg)

/-- **No positive kernel reproduces factorial damping, even at two indices.** -/
theorem no_posSemidef_kernel_matches_reciprocalFactorial {m n : ℕ} (h : m ≠ n)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.PosSemidef)
    (h00 : B 0 0 = 1 / ((2 * m)! : ℝ)) (h01 : B 0 1 = 1 / ((m + n)! : ℝ))
    (h10 : B 1 0 = 1 / ((m + n)! : ℝ)) (h11 : B 1 1 = 1 / ((2 * n)! : ℝ)) : False := by
  refine reciprocalFactorialBlock_not_posSemidef h ?_
  have hEq : reciprocalFactorialBlock m n = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reciprocalFactorialBlock, h00, h01, h10, h11]
  rw [hEq]
  exact hB

end RHTower
