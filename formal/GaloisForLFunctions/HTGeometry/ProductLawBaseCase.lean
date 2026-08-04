import GaloisForLFunctions.HTGeometry.ProductLawDegenerate

/-!
# The base case: a two-map cascade

At height one the bordered determinant is a single entry, the gradient of the head product against the
first coordinate derivation, and that entry is the product of the zeroth factor with the derivative of
the first.  So a two-map linear-terminal product law is observable exactly when its first factor is
nonconstant — which for a cascade of first-order linear entire maps is automatic, the factor carrying
the linear term of the equation.

Chained with the reductions, this gives the output-jet determinant of the second coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The gradient of the two-factor head product. -/
theorem fpderiv_prodHead_two :
    fpderiv 1 (prodHead Q 2) = fact (Q 0) 0 * fact (Q 1).derivative 1 := by
  have h2 : prodHead Q 2 = fact (Q 0) 0 * fact (Q 1) 1 := by
    rw [prodHead_succ, prodHead_succ, prodHead_zero, one_mul]
  rw [h2, Derivation.leibniz, fpderiv_fact_of_ne (by omega : (0 : ℕ) ≠ 1),
    derivation_fact, fpderiv_fx_self]
  simp

/-- **The base case of the bordered determinant.** -/
theorem bordered_det_ne_zero_zero {Q : ℕ → Polynomial ℂ} (hQ0 : Q 0 ≠ 0)
    (hQ1 : (Q 1).derivative ≠ 0) :
    (uniformBordered (headGradient Q 0) (headBellGradient Q v 0)).det ≠ 0 := by
  rw [Matrix.det_fin_one]
  have hval : uniformBordered (headGradient Q 0) (headBellGradient Q v 0) 0 0
      = fpderiv 1 (prodHead Q 2) := by
    simp [uniformBordered, headGradient]
  rw [hval, fpderiv_prodHead_two]
  exact mul_ne_zero (fact_ne_zero hQ0 0) (fact_ne_zero hQ1 1)

/-- **The output-jet determinant of a two-map cascade.** -/
theorem prodOutput_det_ne_zero_two {Q : ℕ → Polynomial ℂ} {α β : ℂ} (hα : α ≠ 0)
    (hv : v 2 = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hQ : ∀ j, Q j ≠ 0) (hQ1 : (Q 1).derivative ≠ 0) :
    (Matrix.of fun i j : Fin 2 =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv 2
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
          (fun j' : Fin 1 => fpderiv ((j' : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx 2)))
          j).det ≠ 0 := by
  refine prodOutput_det_ne_zero_of_headJetJacobian Q v hα hv ?_
  exact headJetJacobian_det_ne_zero_of_bordered v hQ 0
    (bordered_det_ne_zero_zero v (hQ 0) hQ1)

end GaloisForLFunctions.HTGeometry
