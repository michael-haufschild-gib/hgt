import Mathlib

/-!
# Gamma at a natural-number shift (Pochhammer recurrence)

The `n`-step iterate of the Gamma functional equation, absent from mathlib (which has only the
single step `Gamma_add_one`):

`Γ(z + n) = (∏_{j<n} (z + j)) · Γ(z)`,

valid whenever none of the shifted arguments `z + j` (`j < n`) vanishes.  This is the recurrence that
moves a Gamma factor to a chosen representative of its `ℤ`-shift orbit — the reduction underlying the
signed-archimedean Gamma-product normal form — and is reusable Gamma infrastructure.
-/

open scoped BigOperators

namespace HTGeometry

/-- **Complex Gamma at a natural shift.**  `Γ(z + n) = (∏_{j<n} (z + j)) · Γ(z)` when no shifted
argument vanishes. -/
theorem Gamma_add_nat (z : ℂ) (n : ℕ) (h : ∀ j : ℕ, j < n → z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (n : ℂ)) = (∏ j ∈ Finset.range n, (z + (j : ℂ))) * Complex.Gamma z := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : z + (k : ℂ) ≠ 0 := h k (Nat.lt_succ_self k)
    have hz1 : z + ((k + 1 : ℕ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
    rw [hz1, Complex.Gamma_add_one _ hk, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      Finset.prod_range_succ]
    ring

/-- **Real Gamma at a natural shift.**  `Γ(x + n) = (∏_{j<n} (x + j)) · Γ(x)` when no shifted
argument vanishes. -/
theorem Real.Gamma_add_nat (x : ℝ) (n : ℕ) (h : ∀ j : ℕ, j < n → x + (j : ℝ) ≠ 0) :
    Real.Gamma (x + (n : ℝ)) = (∏ j ∈ Finset.range n, (x + (j : ℝ))) * Real.Gamma x := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : x + (k : ℝ) ≠ 0 := h k (Nat.lt_succ_self k)
    have hx1 : x + ((k + 1 : ℕ) : ℝ) = (x + (k : ℝ)) + 1 := by push_cast; ring
    rw [hx1, Real.Gamma_add_one hk, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      Finset.prod_range_succ]
    ring

/-- For arguments with strictly positive real part, all shifts are nonzero, so the Pochhammer
recurrence holds unconditionally. -/
theorem Gamma_add_nat_of_re_pos (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    Complex.Gamma (z + (n : ℂ)) = (∏ j ∈ Finset.range n, (z + (j : ℂ))) * Complex.Gamma z := by
  refine Gamma_add_nat z n (fun j _ hj => ?_)
  have : (z + (j : ℂ)).re = z.re + j := by simp
  rw [hj] at this
  simp only [Complex.zero_re] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

end HTGeometry
