import GaloisForLFunctions.HTGeometry.DisjointBlockPolynomialIndependence
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every nonconstant complex multivariate polynomial has a zero. -/
theorem exists_mvPolynomial_eval_eq_zero_of_not_constant
    {σ : Type*} {P : MvPolynomial σ ℂ} (hP : ¬ IsConstantMvPolynomial P) :
    ∃ x : σ → ℂ, MvPolynomial.eval x P = 0 := by
  obtain ⟨x, y, hdeg⟩ := exists_mvPolynomial_line_natDegree_ne_zero hP
  let Q := mvPolynomialLine P x y
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hdeg
    simp [Q, hzero]
  have hdegree : Q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hQ0]
    exact_mod_cast hdeg
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root Q hdegree
  exact ⟨fun i => x i + t * (y i - x i), by
    simpa [Q, Polynomial.IsRoot] using (eval_mvPolynomialLine P x y t).symm.trans ht⟩

end
end GaloisForLFunctions.HTGeometry
