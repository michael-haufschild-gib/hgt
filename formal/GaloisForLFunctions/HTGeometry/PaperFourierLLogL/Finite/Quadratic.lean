import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Complex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Cauchy–Schwarz and Minkowski for finite probability laws

Quadratic inequalities for expectations `P.Ex` under a finite probability law `P` on a finite type:
a weighted Cauchy–Schwarz inequality, Jensen's inequality `(E f)² ≤ E f²`, the triangle inequality
for the `L²(P)` norm, and the bound `‖E f‖² ≤ E ‖f‖²` for complex-valued `f`.

## Main results

- `sq_Ex_le`: if `f² ≤ g h` pointwise with `g, h ≥ 0`, then `(E f)² ≤ E g · E h`.
- `sq_Ex_mul`: Cauchy–Schwarz `(E[f g])² ≤ E f² · E g²`.
- `sq_Ex`: `(E f)² ≤ E f²`.
- `quadratic_minkowski`: `√E (f + g)² ≤ √E f² + √E g²`.
- `sq_Cx_norm`: `‖E f‖² ≤ E ‖f‖²` for complex `f`.

## Hypotheses

All results are unconditional.
-/

open Set Function Filter
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

namespace FourierLLogL.Law
open Real
variable {α : Type} [Fintype α]

/-- Weighted Cauchy–Schwarz: if `f x ^ 2 ≤ g x · h x` with `g, h ≥ 0`, then
`(E f)² ≤ E g · E h`. -/
lemma sq_Ex_le (P : Law α) (f g h : α → ℝ) (hg : ∀ x, 0 ≤ g x) (hh : ∀ x, 0 ≤ h x)
    (H : ∀ x, f x^2 ≤ g x*h x) : P.Ex f^2 ≤ P.Ex g * P.Ex h := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (f:=fun x => P x * g x) (g:=fun x => P x * h x)
    (fun x _ => mul_nonneg (P.nonneg x) (hg x))
    (fun x _ => mul_nonneg (P.nonneg x) (hh x)) ?_
  intro x _
  have hi := mul_le_mul_of_nonneg_left (H x) (sq_nonneg (P x))
  calc
    (P x * f x)^2 = P x^2 * f x^2 := mul_pow _ _ _
    _ ≤ _ := hi
    _ = P x * g x * (P x * h x) := by ring

/-- Cauchy–Schwarz for a finite law: `(E[f g])² ≤ E f² · E g²`. -/
lemma sq_Ex_mul (P : Law α) (f g : α → ℝ) :
    (P.Ex (fun x => f x * g x))^2 ≤ P.Ex (fun x => f x^2) * P.Ex (fun x => g x^2) :=
  sq_Ex_le _ _ _ _ (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (fun _ => (mul_pow _ _ _).le)

/-- Jensen for the square: `(E f)² ≤ E f²`. -/
lemma sq_Ex (P : Law α) (f : α → ℝ) :
    (P.Ex f)^2 ≤ P.Ex (fun x => f x^2) := by
  simpa only [mul_one,one_pow,Ex_const] using sq_Ex_mul P f (fun _ => 1)

/-- Minkowski's inequality in `L²(P)`: `√E (f + g)² ≤ √E f² + √E g²`. -/
lemma quadratic_minkowski (P : Law α) (f g : α → ℝ) :
    √(P.Ex fun x => (f x+g x)^2) ≤ √(P.Ex fun x => (f x)^2) + √(P.Ex fun x => (g x)^2) := by
  let A := P.Ex fun x => (f x)^2; let B := P.Ex fun x => (g x)^2
  let E := P.Ex fun x => (f x+g x)^2
  have hA := sq_sqrt (show 0 ≤ A from P.Ex_nonneg fun x => sq_nonneg _)
  have hB := sq_sqrt (show 0 ≤ B from P.Ex_nonneg fun x => sq_nonneg _)
  have hE := sq_sqrt (show 0 ≤ E from P.Ex_nonneg fun x => sq_nonneg _)
  let L := P.Ex fun x => f x * g x
  have hL : E = A+B+2*L := by
    unfold E A B L
    simp_rw [← Ex_lmul,← Ex_add]; congr 1; funext i; ring
  have hU : L^2 ≤ (√A*√B)^2 := by rw [mul_pow,hA,hB]; exact sq_Ex_mul _ _ _
  have hL' : L ≤ √A*√B := by nlinarith [show 0 ≤ √A*√B by positivity]
  change √E ≤ √A+√B
  nlinarith [sqrt_nonneg A,sqrt_nonneg B]

/-- For complex-valued `f`, the squared norm of the complex expectation is at most `E ‖f‖²`. -/
lemma sq_Cx_norm (P : Law α) (f : α → ℂ) :
    ‖P.Cx f‖^2 ≤ P.Ex (fun x => ‖f x‖^2) :=
  (pow_le_pow_left₀ (norm_nonneg _) (P.Cx_norm _) _).trans (sq_Ex _ _)
end FourierLLogL.Law

end GaloisForLFunctions.HTGeometry
