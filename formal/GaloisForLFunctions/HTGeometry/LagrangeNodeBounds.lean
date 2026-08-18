import Mathlib

/-!
# Polynomials small at separated nodes

A polynomial of degree below the number of interpolation nodes is the Lagrange combination of its
values there, so smallness at the nodes forces smallness everywhere, with a constant governed only
by the node separation.  Two consequences are recorded:

* the value bound on an arbitrary point;
* the coefficient bound, obtained by reading the same identity coefficientwise.

These are the quantitative replacements for the compactness argument behind the invertibility of a
moment matrix built from measures on disjoint intervals.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- **Lagrange evaluation identity.** -/
theorem eval_eq_sum_lagrange {J : ℕ} (t : Fin J → ℂ) (ht : Function.Injective t)
    (P : Polynomial ℂ) (hdeg : P.degree < (J : ℕ)) (z : ℂ) :
    P.eval z
      = ∑ i : Fin J, P.eval (t i) *
          ∏ k ∈ Finset.univ.erase i, (t i - t k)⁻¹ * (z - t k) := by
  have hcard : (Finset.univ : Finset (Fin J)).card = J := by simp
  have hinj : Set.InjOn t (Finset.univ : Finset (Fin J)) := fun a _ b _ h => ht h
  have hdeg' : P.degree < ((Finset.univ : Finset (Fin J)).card : ℕ) := by
    rw [hcard]; exact hdeg
  have hP := Lagrange.eq_interpolate (v := t) hinj hdeg'
  have hval : P.eval z
      = (Lagrange.interpolate (Finset.univ : Finset (Fin J)) t
          (fun i => P.eval (t i))).eval z := by
    rw [hP]
  rw [hval, Lagrange.interpolate_apply]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis]
  congr 1
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

/-- **Values are small when the polynomial is small at the nodes.** -/
theorem norm_eval_le_of_nodes {J : ℕ} (t : Fin J → ℂ) (ht : Function.Injective t)
    (P : Polynomial ℂ) (hdeg : P.degree < (J : ℕ)) {ε : ℝ}
    (hsmall : ∀ i, ‖P.eval (t i)‖ ≤ ε) (z : ℂ) :
    ‖P.eval z‖ ≤ ε * ∑ i : Fin J, ∏ k ∈ Finset.univ.erase i, ‖(t i - t k)⁻¹ * (z - t k)‖ := by
  rw [eval_eq_sum_lagrange t ht P hdeg z]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_right (hsmall i) ?_
  positivity

/-- **Coefficients are small when the polynomial is small at the nodes.** -/
theorem norm_coeff_le_of_nodes {J : ℕ} (t : Fin J → ℂ) (ht : Function.Injective t)
    (P : Polynomial ℂ) (hdeg : P.degree < (J : ℕ)) {ε : ℝ}
    (hsmall : ∀ i, ‖P.eval (t i)‖ ≤ ε) (j : ℕ) :
    ‖P.coeff j‖ ≤ ε * ∑ i : Fin J,
      ‖(∏ k ∈ Finset.univ.erase i, Lagrange.basisDivisor (t i) (t k)).coeff j‖ := by
  have hcard : (Finset.univ : Finset (Fin J)).card = J := by simp
  have hinj : Set.InjOn t (Finset.univ : Finset (Fin J)) := fun a _ b _ h => ht h
  have hdeg' : P.degree < ((Finset.univ : Finset (Fin J)).card : ℕ) := by
    rw [hcard]; exact hdeg
  have hP := Lagrange.eq_interpolate (v := t) hinj hdeg'
  have hcoeff : P.coeff j
      = ∑ i : Fin J, P.eval (t i) *
          (∏ k ∈ Finset.univ.erase i, Lagrange.basisDivisor (t i) (t k)).coeff j := by
    conv_lhs => rw [← hP]
    rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Lagrange.basis, Polynomial.coeff_C_mul]
  rw [hcoeff]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hsmall i) (norm_nonneg _)

end GaloisForLFunctions.HTGeometry

end
