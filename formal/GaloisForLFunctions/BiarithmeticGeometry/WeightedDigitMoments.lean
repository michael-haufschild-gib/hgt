import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact moments of signed digit rows

All base-five words are enumerated, with arbitrary fixed real coefficients. Their second
moment separates the diagonal variance from the square of the mean; a nonzero leading
digit gives the corresponding annular identity.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- A signed linear readout of a finite base-five word. -/
def fiveDigitReadout {M : ℕ} (x : Fin M → ℝ) (d : Fin M → Fin 5) : ℝ :=
  ∑ i, (d i : ℝ) * x i

private def fiveDigitSplit (M : ℕ) :
    (Fin (M + 1) → Fin 5) ≃ Fin 5 × (Fin M → Fin 5) where
  toFun d := (d 0, fun i => d i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by cases p; rfl

private theorem sum_fiveDigitSplit (M : ℕ) (f : (Fin (M + 1) → Fin 5) → ℝ) :
    (∑ d, f d) = ∑ a : Fin 5, ∑ d : Fin M → Fin 5, f (Fin.cases a d) := by
  rw [← (fiveDigitSplit M).symm.sum_comp f, Fintype.sum_prod_type]
  rfl

theorem fiveDigitReadout_cons {M : ℕ} (x : Fin (M + 1) → ℝ)
    (a : Fin 5) (d : Fin M → Fin 5) :
    fiveDigitReadout x (Fin.cases a d) =
      (a : ℝ) * x 0 + fiveDigitReadout (fun i => x i.succ) d := by
  rw [fiveDigitReadout, Fin.sum_univ_succ]
  rfl

/-- The first signed moment over every base-five word. -/
theorem sum_fiveDigitReadout (M : ℕ) (x : Fin M → ℝ) :
    (∑ d : Fin M → Fin 5, fiveDigitReadout x d) = (5 : ℝ) ^ M * (2 * ∑ i, x i) := by
  induction M with
  | zero => simp [fiveDigitReadout]
  | succ M ih =>
    rw [sum_fiveDigitSplit]
    simp only [fiveDigitReadout_cons, sum_add_distrib, sum_const, card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ih]
    norm_num [Fin.sum_univ_succ, pow_succ]
    ring

/-- The exact second moment keeps both signed cross terms and diagonal variance. -/
theorem sum_sq_fiveDigitReadout (M : ℕ) (x : Fin M → ℝ) :
    (∑ d : Fin M → Fin 5, fiveDigitReadout x d ^ 2) =
      (5 : ℝ) ^ M * (2 * ∑ i, x i ^ 2 + 4 * (∑ i, x i) ^ 2) := by
  induction M with
  | zero => simp [fiveDigitReadout]
  | succ M ih =>
    rw [sum_fiveDigitSplit]
    simp only [fiveDigitReadout_cons]
    have hexpand (a : Fin 5) (d : Fin M → Fin 5) :
        ((a : ℝ) * x 0 + fiveDigitReadout (fun i => x i.succ) d) ^ 2 =
          (a : ℝ) ^ 2 * x 0 ^ 2 +
          2 * (a : ℝ) * x 0 * fiveDigitReadout (fun i => x i.succ) d +
          fiveDigitReadout (fun i => x i.succ) d ^ 2 := by ring
    simp_rw [hexpand]
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_sum]
    rw [sum_fiveDigitReadout, ih]
    norm_num [Fin.sum_univ_succ, pow_succ]
    ring

/-- The exact block moment when the leading base-five digit is nonzero. -/
theorem sum_sq_fiveDigitBlock (M : ℕ) (x : Fin M → ℝ) (leading : ℝ) :
    (∑ a : Fin 4, ∑ d : Fin M → Fin 5,
      (((a : ℝ) + 1) * leading + fiveDigitReadout x d) ^ 2) =
      4 * (5 : ℝ) ^ M *
        ((5 / 4 : ℝ) * leading ^ 2 + 2 * ∑ i, x i ^ 2 +
          ((5 / 2 : ℝ) * leading + 2 * ∑ i, x i) ^ 2) := by
  have hexpand (a : Fin 4) (d : Fin M → Fin 5) :
      (((a : ℝ) + 1) * leading + fiveDigitReadout x d) ^ 2 =
        ((a : ℝ) + 1) ^ 2 * leading ^ 2 +
        2 * ((a : ℝ) + 1) * leading * fiveDigitReadout x d + fiveDigitReadout x d ^ 2 := by
    ring
  simp_rw [hexpand]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_sum]
  rw [sum_fiveDigitReadout, sum_sq_fiveDigitReadout]
  norm_num [Fin.sum_univ_succ]
  ring

/-- No choice of lower-digit coefficients can remove the leading-digit variance. -/
theorem fiveDigitBlock_leading_lower (M : ℕ) (x : Fin M → ℝ) (leading : ℝ) :
    (5 : ℝ) ^ (M + 1) * leading ^ 2 ≤
      ∑ a : Fin 4, ∑ d : Fin M → Fin 5,
        (((a : ℝ) + 1) * leading + fiveDigitReadout x d) ^ 2 := by
  rw [sum_sq_fiveDigitBlock, pow_succ]
  have hx : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ => sq_nonneg (x i)
  have hm : 0 ≤ ((5 / 2 : ℝ) * leading + 2 * ∑ i, x i) ^ 2 := sq_nonneg _
  have hp : 0 ≤ (5 : ℝ) ^ M := pow_nonneg (by norm_num) M
  nlinarith only [mul_nonneg hp hx, mul_nonneg hp hm]

end GaloisForLFunctions.BiarithmeticGeometry
