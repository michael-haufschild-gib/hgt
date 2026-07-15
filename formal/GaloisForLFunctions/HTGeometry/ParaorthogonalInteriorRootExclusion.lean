import GaloisForLFunctions.HTGeometry.ParaorthogonalBlaschkeRoot

/-!
# Interior-root exclusion for paraorthogonal terminals

A polynomial carrying a strict open-disk root cannot be a paraorthogonal terminal built from a
strictly stable polynomial and a unimodular endpoint.  This is the contradiction-ready form of
the finite paraorthogonal root-location theorem.
-/

open Complex Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A certified strict open-disk root excludes equality with every stable paraorthogonal
terminal. -/
theorem polynomial_ne_finiteParaorthogonalPolynomial_of_isRoot_norm_lt_one
    {P p : Polynomial ℂ} {u terminal : ℂ}
    (huRoot : P.IsRoot u) (hu : ‖u‖ < 1)
    (hp : p ≠ 0) (hroots : ∀ a ∈ p.roots, ‖a‖ < 1)
    (hterminal : ‖terminal‖ = 1) :
    P ≠ finiteParaorthogonalPolynomial p terminal := by
  intro heq
  rw [heq] at huRoot
  have hunit := finiteParaorthogonalPolynomial_isRoot_norm_eq_one
    hp hroots hterminal huRoot
  linarith

end


end GaloisForLFunctions.HTGeometry
