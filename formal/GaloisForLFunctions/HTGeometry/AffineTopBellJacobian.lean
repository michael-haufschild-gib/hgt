import GaloisForLFunctions.HTGeometry.AffineTopGeneral
import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# The homogeneous jet coefficients are the Bell values

The coefficients produced by the affine top reduction obey `A_0 = 1`, `A_(i+1) = δA_i + A_i·A`, which
is the Bell recursion for the multiplier `A`.  They therefore agree with the corpus's universal Bell
values, evaluated at the jets of `A` — no auxiliary element with `δx = A·x` is needed, because the
recursion characterises both sides.

Consequently the Jacobian of the coefficients equals the Jacobian of the jets of the multiplier
itself: the passage from a driven variable to its driver costs nothing.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- **The affine jet coefficients are the universal Bell polynomials at the jets of the
multiplier.** -/
theorem genJetA_eq_aeval_bellCore (δ : Derivation ℂ R R) (A : R) (m : ℕ) :
    genJetA δ A m
      = aeval (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A) (bellCore m) := by
  induction m with
  | zero => simp [genJetA, bellCore_zero]
  | succ m ih =>
      rw [genJetA_succ, ih, aeval_bellCore_succ_derivationIterate δ A m,
        derivation_aeval_eq_sum_pderiv δ (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A)
          (bellCore m)]
      have hjet : ∀ j : Fin m, δ (((δ : R → R)^[(j : ℕ)]) A)
          = ((δ : R → R)^[(j : ℕ) + 1]) A := by
        intro j
        exact (derivation_iterate_succ δ (j : ℕ) A).symm
      simp only [hjet]
      ring

/-- The affine jet coefficients are the corpus's Bell values. -/
theorem genJetA_eq_derivationBellValue (δ : Derivation ℂ R R) (A : R) (n : ℕ) (i : Fin (n + 1)) :
    genJetA δ A ((i : ℕ) + 1) = derivationBellValue δ A n i := by
  rw [genJetA_eq_aeval_bellCore]
  simp [derivationBellValue, bellAt, MvPolynomial.aeval_rename, Function.comp_def]

/-- **The Jacobian of the jet coefficients is the Jacobian of the jets of the multiplier.**  The Bell
recursion is unitriangular in the jets, so the two determinants agree. -/
theorem det_genJetA_eq_det_jets (δ : Derivation ℂ R R) (n : ℕ)
    (partials : Fin (n + 2) → Derivation ℂ R R) (A : R) :
    (Matrix.of fun i j : Fin (n + 1) =>
        partials j.castSucc (genJetA δ A ((i : ℕ) + 1))).det
      = (Matrix.of fun i j : Fin (n + 1) =>
        partials j.castSucc (((δ : R → R)^[(i : ℕ)]) A)).det := by
  have hL : (Matrix.of fun i j : Fin (n + 1) =>
      partials j.castSucc (genJetA δ A ((i : ℕ) + 1)))
      = derivationBellValueJacobian δ n partials A := by
    funext i j
    rw [Matrix.of_apply, derivationBellValueJacobian, genJetA_eq_derivationBellValue]
  have hR : (Matrix.of fun i j : Fin (n + 1) =>
      partials j.castSucc (((δ : R → R)^[(i : ℕ)]) A))
      = derivationLowerJetJacobian δ n partials A := rfl
  rw [hL, hR, derivationBellValueJacobian_det]

end GaloisForLFunctions.HTGeometry
