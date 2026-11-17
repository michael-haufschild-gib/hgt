import GaloisForLFunctions.HilbertMetric.QuantumInformation.JordanPositivityBoundary
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact rank of the forward Jordan symbol

The arithmetic-mean symbol factors through two dimensions. Constant
positive rates give rank one; a rate mismatch gives a nonsingular
two-coordinate minor and hence rank two.
-/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.CauchyJordan

/-- Forward Jordan symbols factor through two scalar channels. -/
theorem jordanSymbol_factor_two {n : ℕ} (r : Fin n → ℝ) :
    jordanSymbol r =
      Matrix.of (fun i (a : Fin 2) => if a = 0 then (rate r i : ℂ) / 2 else 1 / 2) *
        Matrix.of (fun (a : Fin 2) j => if a = 0 then (1 : ℂ) else (rate r j : ℂ)) := by
  ext i j
  rw [jordanSymbol_apply, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num
  ring

/-- The rank of the Jordan symbol is at most two in every dimension. -/
theorem jordanSymbol_rank_le_two {n : ℕ} (r : Fin n → ℝ) :
    (jordanSymbol r).rank ≤ 2 := by
  rw [jordanSymbol_factor_two]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Constant rates have rank one, and every genuine rate mismatch has rank two. -/
theorem jordanSymbol_rank (n : ℕ) (r : Fin (n + 1) → ℝ) :
    (jordanSymbol r).rank = if ∀ i j, r i = r j then 1 else 2 := by
  classical
  by_cases hc : ∀ i j, r i = r j
  · rw [if_pos hc]
    have hf : jordanSymbol r =
        Matrix.of (fun (_ : Fin (n + 1)) (_ : Fin 1) => (rate r 0 : ℂ)) *
          Matrix.of (fun (_ : Fin 1) (_ : Fin (n + 1)) => (1 : ℂ)) := by
      ext i j
      rw [jordanSymbol_apply, Matrix.mul_apply, Fin.sum_univ_one]
      simp only [Matrix.of_apply, rate, hc i 0, hc j 0, mul_one]
      ring
    have hle : (jordanSymbol r).rank ≤ 1 := by
      rw [hf]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
    have hd : ((jordanSymbol r).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)).det ≠ 0 := by
      rw [Matrix.det_fin_one]
      simp only [Matrix.submatrix_apply, jordanSymbol_apply]
      rw [show ((rate r 0 : ℂ) + (rate r 0 : ℂ)) / 2 = (rate r 0 : ℂ) by ring]
      exact Complex.ofReal_ne_zero.mpr (rate_pos r 0).ne'
    have hu : IsUnit ((jordanSymbol r).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have hr := Matrix.rank_of_isUnit _ hu
    have hlo := Matrix.rank_submatrix_le (jordanSymbol r)
      (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
    rw [hr, Fintype.card_fin] at hlo
    exact le_antisymm hle hlo
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨i, j, hij⟩ := hc
    have hd : ((jordanSymbol r).submatrix ![i, j] ![i, j]).det ≠ 0 := by
      intro h
      have hneg := (jordanSymbol_pair_det_neg_iff r i j).mpr hij
      rw [h, Complex.zero_re] at hneg
      exact (lt_irrefl 0) hneg
    have hu : IsUnit ((jordanSymbol r).submatrix ![i, j] ![i, j]) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have hr := Matrix.rank_of_isUnit _ hu
    have hle := Matrix.rank_submatrix_le (jordanSymbol r) ![i, j] ![i, j]
    rw [hr, Fintype.card_fin] at hle
    exact le_antisymm (jordanSymbol_rank_le_two r) hle

#print axioms jordanSymbol_factor_two
#print axioms jordanSymbol_rank_le_two
#print axioms jordanSymbol_rank
end GaloisForLFunctions.HilbertMetric.CauchyJordan
