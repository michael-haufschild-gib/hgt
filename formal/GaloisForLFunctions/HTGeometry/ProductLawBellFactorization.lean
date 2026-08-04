import GaloisForLFunctions.HTGeometry.ProductLawHeadReduction
import GaloisForLFunctions.HTGeometry.AffineTopBellJacobian
import GaloisForLFunctions.HTGeometry.BellCoordinateJacobian

/-!
# The Bell rows factor through the universal unit matrix

Every gradient of a Bell value is a fixed universal combination of the gradients of the jets of the
multiplier — the coefficients are the entries of the Bell coordinate Jacobian, evaluated at those
jets, and do not depend on which derivation is applied.

That is what turns the bordered Bell determinant into the bordered jet determinant: the combination
is unitriangular, so it changes no determinant, and it works for a rectangular block of rows because
the identity is entrywise in the derivation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

variable (Q v : ℕ → Polynomial ℂ)

/-- The product law's Bell iterates are the general affine jet coefficients. -/
theorem prodBell_eq_genJetA (A : CascadeField) (i : ℕ) :
    prodBell Q v A i = genJetA (prodDerivation Q v) A i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [prodBell_succ, genJetA_succ, ih]
      ring

/-- **The gradient of a Bell value is a universal combination of the gradients of the jets.** -/
theorem fpderiv_prodBell_succ (U : CascadeField) (n : ℕ) (r : Fin (n + 1)) (j : ℕ) :
    fpderiv j (prodBell Q v U ((r : ℕ) + 1))
      = ∑ k : Fin (n + 1),
          MvPolynomial.aeval
            (fun l : Fin (n + 1) =>
              ((prodDerivation Q v : CascadeField → CascadeField)^[(l : ℕ)]) U)
            (bellCoordinateJacobian n k r)
          * fpderiv j (((prodDerivation Q v : CascadeField → CascadeField)^[(k : ℕ)]) U) := by
  rw [prodBell_eq_genJetA, genJetA_eq_derivationBellValue (n := n) (i := r), derivationBellValue,
    derivation_aeval_eq_sum_pderiv]
  rfl

end GaloisForLFunctions.HTGeometry
