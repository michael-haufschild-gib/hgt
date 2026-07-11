import Mathlib.Analysis.Complex.CauchyIntegral
import GaloisForLFunctions.RHTower.CompactCarrierFECompleteness

/-!
# One-dimensional analytic partial sums as scalar polynomials

This small bridge turns the partial sums of a one-dimensional formal
multilinear series into ordinary complex polynomials, including translation
of the expansion centre.
-/

noncomputable section

namespace RHTower

open Polynomial Finset

/-- Scalar polynomial encoding the first `N` homogeneous terms of a
one-dimensional formal multilinear series. -/
def fmlsPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ range N, C (p n (fun _ => 1)) * X ^ n

theorem fmlsPolynomial_eval
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (z : ℂ) :
    (fmlsPolynomial p N).eval z = p.partialSum N z := by
  unfold fmlsPolynomial FormalMultilinearSeries.partialSum
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have h := (p n).map_smul_univ (fun _ : Fin n => z) (fun _ => (1 : ℂ))
  have hp : p n (fun _ => z) = z ^ n * p n (fun _ => 1) := by
    simpa using h
  rw [hp]
  ring

/-- Translate the preceding polynomial from zero to a centre `c`. -/
def shiftedFmlsPolynomial
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (c : ℂ) : Polynomial ℂ :=
  (fmlsPolynomial p N).comp (X - C c)

theorem shiftedFmlsPolynomial_eval
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (N : ℕ) (c z : ℂ) :
    (shiftedFmlsPolynomial p N c).eval z = p.partialSum N (z - c) := by
  rw [shiftedFmlsPolynomial, Polynomial.eval_comp]
  simp only [eval_sub, eval_X, eval_C]
  exact fmlsPolynomial_eval p N (z - c)

end RHTower
