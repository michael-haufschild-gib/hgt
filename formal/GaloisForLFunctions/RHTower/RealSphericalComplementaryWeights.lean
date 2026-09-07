import GaloisForLFunctions.RHTower.RealSphericalHarishChandra
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Complementary-series weights on spherical `K`-types

For real `|s| < 1`, the invariant Hermitian form on the spherical principal-series
Harish-Chandra module is diagonal in the `K`-type basis.  This file constructs its positive
weights as finite products and proves the two-sided recurrence required by `e† = -f`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Ratio between consecutive nonnegative complementary-series `K`-type weights. -/
def complementaryWeightRatio (s : ℝ) (n : ℕ) : ℝ :=
  (((2 * n + 1 : ℕ) : ℝ) + s) / (((2 * n + 1 : ℕ) : ℝ) - s)

/-- Positive-index product defining complementary-series `K`-type weights. -/
def complementaryNatWeight (s : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, complementaryWeightRatio s k

/-- Even extension of the complementary-series weights to all integer `K`-type indices. -/
def complementaryKTypeWeight (s : ℝ) (m : ℤ) : ℝ :=
  complementaryNatWeight s m.natAbs

@[simp]
theorem complementaryKTypeWeight_ofNat (s : ℝ) (n : ℕ) :
    complementaryKTypeWeight s (Int.ofNat n) =
      complementaryNatWeight s n := rfl

@[simp]
theorem complementaryKTypeWeight_negSucc (s : ℝ) (n : ℕ) :
    complementaryKTypeWeight s (Int.negSucc n) =
      complementaryNatWeight s (n + 1) := rfl

@[simp]
theorem complementaryNatWeight_zero (s : ℝ) :
    complementaryNatWeight s 0 = 1 := by
  simp [complementaryNatWeight]

theorem complementaryNatWeight_succ (s : ℝ) (n : ℕ) :
    complementaryNatWeight s (n + 1) =
      complementaryNatWeight s n * complementaryWeightRatio s n := by
  simp [complementaryNatWeight, Finset.prod_range_succ]

theorem complementaryWeightRatio_pos (s : ℝ) (hs : |s| < 1) (n : ℕ) :
    0 < complementaryWeightRatio s n := by
  have hs' := abs_lt.mp hs
  have hn : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * n))
  unfold complementaryWeightRatio
  exact div_pos (by linarith) (by linarith)

theorem complementaryKTypeWeight_pos (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    0 < complementaryKTypeWeight s m := by
  cases m with
  | ofNat n =>
      rw [complementaryKTypeWeight_ofNat]
      exact Finset.prod_pos fun k _ ↦ complementaryWeightRatio_pos s hs k
  | negSucc n =>
      rw [complementaryKTypeWeight_negSucc]
      exact Finset.prod_pos fun k _ ↦ complementaryWeightRatio_pos s hs k

theorem complementaryWeightRatio_cancel (s : ℝ) (hs : |s| < 1) (n : ℕ) :
    (((2 * n + 1 : ℕ) : ℝ) - s) * complementaryWeightRatio s n =
      ((2 * n + 1 : ℕ) : ℝ) + s := by
  have hs' := abs_lt.mp hs
  have hn : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (2 * n))
  have hden : (((2 * n + 1 : ℕ) : ℝ) - s) ≠ 0 := by linarith
  rw [complementaryWeightRatio]
  field_simp

theorem complementaryNatWeight_recurrence (s : ℝ) (hs : |s| < 1) (n : ℕ) :
    (((2 * n + 1 : ℕ) : ℝ) - s) * complementaryNatWeight s (n + 1) =
      (((2 * n + 1 : ℕ) : ℝ) + s) * complementaryNatWeight s n := by
  rw [complementaryNatWeight_succ]
  calc
    (((2 * n + 1 : ℕ) : ℝ) - s) *
        (complementaryNatWeight s n * complementaryWeightRatio s n) =
      complementaryNatWeight s n *
        ((((2 * n + 1 : ℕ) : ℝ) - s) * complementaryWeightRatio s n) := by ring
    _ = complementaryNatWeight s n * (((2 * n + 1 : ℕ) : ℝ) + s) := by
      rw [complementaryWeightRatio_cancel s hs n]
    _ = (((2 * n + 1 : ℕ) : ℝ) + s) * complementaryNatWeight s n := by ring

/-- Two-sided recurrence making the raising and lowering operators adjoint with opposite sign. -/
theorem complementaryKTypeWeight_succ_recurrence (s : ℝ) (hs : |s| < 1) (m : ℤ) :
    ((((2 : ℤ) * m + 1 : ℤ) : ℝ) - s) * complementaryKTypeWeight s (m + 1) =
      ((((2 : ℤ) * m + 1 : ℤ) : ℝ) + s) * complementaryKTypeWeight s m := by
  cases m with
  | ofNat n =>
      have hstep := complementaryNatWeight_recurrence s hs n
      change
        (((2 * n + 1 : ℕ) : ℝ) - s) * complementaryNatWeight s (n + 1) =
          (((2 * n + 1 : ℕ) : ℝ) + s) * complementaryNatWeight s n
      exact hstep
  | negSucc n =>
      cases n with
      | zero =>
          have hstep := complementaryNatWeight_recurrence s hs 0
          simp [Int.negSucc_eq, complementaryKTypeWeight] at ⊢
          simp only [complementaryNatWeight_zero] at hstep
          norm_num at hstep
          calc
            -1 - s = -(1 + s) := by ring
            _ = -((1 - s) * complementaryNatWeight s 1) := by rw [hstep]
            _ = (-1 + s) * complementaryNatWeight s 1 := by ring
      | succ n =>
          have hstep := complementaryNatWeight_recurrence s hs (n + 1)
          rw [show (Int.negSucc (n + 1) + 1) = Int.negSucc n by omega]
          rw [complementaryKTypeWeight_negSucc, complementaryKTypeWeight_negSucc]
          rw [Int.negSucc_eq]
          push_cast
          have hcoeff :
              (2 * -(((n : ℝ) + 1) + 1) + 1) =
                -(((2 * (n + 1) + 1 : ℕ) : ℝ)) := by
            push_cast
            ring
          rw [hcoeff, show n + 1 + 1 = n + 2 by omega]
          calc
            (-(((2 * (n + 1) + 1 : ℕ) : ℝ)) - s) *
                complementaryNatWeight s (n + 1) =
              -(((((2 * (n + 1) + 1 : ℕ) : ℝ)) + s) *
                complementaryNatWeight s (n + 1)) := by ring
            _ = -(((((2 * (n + 1) + 1 : ℕ) : ℝ)) - s) *
                complementaryNatWeight s (n + 2)) := by rw [hstep]
            _ = (-(((2 * (n + 1) + 1 : ℕ) : ℝ)) + s) *
                complementaryNatWeight s (n + 2) := by ring

end

end GaloisForLFunctions.RHTower
