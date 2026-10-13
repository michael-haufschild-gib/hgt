import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Vanishing on the real diagonal is exactly divisibility by the difference of the variables. -/

open MvPolynomial
local notation "P₂" => MvPolynomial (Fin 2) ℝ
local notation "Δ" => (X (0 : Fin 2) - X (1 : Fin 2) : P₂)
local notation "ρ" => MvPolynomial.rename (R := ℝ) (fun _ : Fin 2 => (1 : Fin 2))

namespace GaloisForLFunctions.HTGeometry

theorem binaryPolynomial_sub_rename_diagonal_dvd (p : P₂) : Δ ∣ p - ρ p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      have hdiff : p + q - ρ (p + q) = (p - ρ p) + (q - ρ q) := by
        rw [map_add]
        ring
      rw [hdiff]
      exact dvd_add hp hq
  | mul_X p i hp =>
      have hi : Δ ∣ (X i : P₂) - X (1 : Fin 2) := by
        fin_cases i <;> simp
      rw [map_mul, rename_X]
      have hdiff : p * X i - ρ p * X (1 : Fin 2) =
          (p - ρ p) * X i + ρ p * (X i - X (1 : Fin 2)) := by ring
      rw [hdiff]
      exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hi _)

theorem binaryPolynomial_diagonal_zero_iff_dvd (p : P₂) :
    (∀ x : ℝ, eval (fun _ => x) p = 0) ↔ Δ ∣ p := by
  constructor
  · intro h
    have hrename : ρ p = 0 := by
      apply MvPolynomial.funext
      intro z
      simpa only [eval_rename, Function.comp_def, map_zero] using h (z 1)
    simpa only [hrename, sub_zero] using binaryPolynomial_sub_rename_diagonal_dvd p
  · rintro ⟨q, rfl⟩ x
    simp only [map_mul, map_sub, eval_X, sub_self, zero_mul]

theorem binaryPolynomial_diagonal_constant_iff_dvd (p : P₂) :
    (∀ x : ℝ, eval (fun _ => x) p = eval (fun _ => 0) p) ↔
      Δ ∣ p - C (eval (fun _ => 0) p) := by
  rw [← binaryPolynomial_diagonal_zero_iff_dvd]
  simp only [map_sub, eval_C, sub_eq_zero]

end GaloisForLFunctions.HTGeometry
