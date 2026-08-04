import GaloisForLFunctions.HTGeometry.StokesFilteredReesCoarea
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial multi-Rees family of Stokes coarea

This module upgrades the real-weight deformation to an actual polynomial multi-Rees family.
Every threshold channel is placed in its own multidegree and multiplied by the square of its Rees
variable.  Unit specialization recovers the Stokes Cartan form; arbitrary real specialization is
the nonnegative weighted form with weights equal to squares.  The physical-rank term is constant
over the entire Rees base.
-/

open scoped BigOperators
open MvPolynomial

namespace GaloisForLFunctions.IrregularStokes.OrbitCoareaDatum

noncomputable section

variable {n m e : ℕ}

/-- Polynomial associated-graded coarea over the multi-Rees base. -/
def polynomialReesBlockEnergy (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    MvPolynomial (Fin e) ℝ :=
  ∑ edge, X edge ^ 2 * C (d.cuts.length edge * d.cutCharge x edge ^ 2)

/-- Polynomial multi-Rees Cartan form.  Only positive threshold channels carry Rees degree; the
terminal energy and unique physical-rank channel are degree zero. -/
def polynomialReesCartanQuadratic (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    MvPolynomial (Fin e) ℝ :=
  C (d.terminalEnergy x) + d.polynomialReesBlockEnergy x -
    C ((d.cuts.root - 1) * d.physicalRank x ^ 2)

/-- Evaluation of the polynomial Rees block form is exactly the real weighted deformation with
nonnegative weights `parameter edge ^ 2`. -/
theorem eval_polynomialReesBlockEnergy (d : OrbitCoareaDatum n m e)
    (parameter : Fin e → ℝ) (x : Fin n → ℝ) :
    eval parameter (d.polynomialReesBlockEnergy x) =
      d.reesBlockEnergy (fun edge => parameter edge ^ 2) x := by
  simp [polynomialReesBlockEnergy, reesBlockEnergy]
  apply Finset.sum_congr rfl
  intro edge _
  ring

/-- Evaluation of the polynomial Cartan form is exactly the corresponding real multi-Rees
specialization. -/
theorem eval_polynomialReesCartanQuadratic (d : OrbitCoareaDatum n m e)
    (parameter : Fin e → ℝ) (x : Fin n → ℝ) :
    eval parameter (d.polynomialReesCartanQuadratic x) =
      d.reesCartanQuadratic (fun edge => parameter edge ^ 2) x := by
  simp [polynomialReesCartanQuadratic, d.eval_polynomialReesBlockEnergy,
    reesCartanQuadratic]

/-- Unit specialization of the actual polynomial Rees family is the original Cartan form. -/
theorem eval_one_polynomialReesCartanQuadratic (d : OrbitCoareaDatum n m e)
    (x : Fin n → ℝ) :
    eval (fun _ => 1) (d.polynomialReesCartanQuadratic x) = d.cartanQuadratic x := by
  rw [d.eval_polynomialReesCartanQuadratic]
  simpa using d.reesCartanQuadratic_one x

/-- Every real point of the polynomial multi-Rees base is positive away from zero on the
physical-rank kernel. -/
theorem eval_polynomialReesCartanQuadratic_pos_of_physicalRank_eq_zero
    (d : OrbitCoareaDatum n m e) (parameter : Fin e → ℝ) {x : Fin n → ℝ}
    (hrank : d.physicalRank x = 0) (hx : x ≠ 0) :
    0 < eval parameter (d.polynomialReesCartanQuadratic x) := by
  rw [d.eval_polynomialReesCartanQuadratic]
  exact d.reesCartanQuadratic_pos_of_physicalRank_eq_zero
    (fun edge => sq_nonneg (parameter edge)) hrank hx

/-- Setting selected Rees variables to zero deletes exactly their graded channels. -/
theorem eval_polynomialReesBlockEnergy_zero_deleted
    (d : OrbitCoareaDatum n m e) (parameter : Fin e → ℝ)
    (retained : Fin e → Prop) [DecidablePred retained] (x : Fin n → ℝ) :
    eval (fun edge => if retained edge then parameter edge else 0)
        (d.polynomialReesBlockEnergy x) =
      ∑ edge ∈ Finset.univ.filter retained,
        parameter edge ^ 2 * d.cuts.length edge * d.cutCharge x edge ^ 2 := by
  rw [d.eval_polynomialReesBlockEnergy]
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0)]
  exact d.reesBlockEnergy_specialize (fun edge => parameter edge ^ 2) retained x

end

end GaloisForLFunctions.IrregularStokes.OrbitCoareaDatum
