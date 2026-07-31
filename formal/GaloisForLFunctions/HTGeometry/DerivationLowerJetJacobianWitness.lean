import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian

/-!
# The lower-jet Jacobian is nondegenerate somewhere

The terminal-linear orbit law is conditional on the lower-jet coordinate Jacobian having nonzero
determinant, and that nondegeneracy was consumed with no producer at all — so the law quantified
over a class never shown to be nonempty.

It is attained by the universal model: on the polynomial ring in countably many coordinates, the
shift derivation sends `X k` to `X (k+1)`, so its iterates applied to `X 0` are exactly the
coordinates, and the partial derivatives read them off.  The Jacobian is then the identity matrix,
at every order.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shift derivation on the polynomial ring in countably many coordinates. -/
def natShiftDerivation : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  mkDerivation ℂ (fun i => X (i + 1))

@[simp] theorem natShiftDerivation_X (i : ℕ) :
    natShiftDerivation (X i) = X (i + 1) := by
  rw [natShiftDerivation, mkDerivation_X]

/-- The iterates of the shift derivation applied to the first coordinate are the coordinates. -/
theorem natShiftDerivation_iterate_X_zero (k : ℕ) :
    ((natShiftDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[k]) (X 0) = X k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, natShiftDerivation_X]

/-- **The universal lower-jet Jacobian is the identity.**  With the shift derivation, the first
coordinate as base point and the coordinate partial derivatives, the lower-jet Jacobian is the
identity matrix at every order. -/
theorem derivationLowerJetJacobian_natShift (n : ℕ) :
    derivationLowerJetJacobian natShiftDerivation n
      (fun j : Fin (n + 2) => pderiv (j : ℕ)) (X 0) = 1 := by
  funext i j
  rw [derivationLowerJetJacobian, natShiftDerivation_iterate_X_zero, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : ((i : ℕ)) ≠ ((j.castSucc : Fin (n + 2)) : ℕ) := by
      simp only [Fin.val_castSucc]
      exact fun h => hij (Fin.ext h)
    rw [pderiv_X_of_ne hne, if_neg hij]

/-- Hence the nondegeneracy hypothesis of the terminal-linear orbit law is attained at every
order. -/
theorem det_derivationLowerJetJacobian_natShift_ne_zero (n : ℕ) :
    (derivationLowerJetJacobian natShiftDerivation n
      (fun j : Fin (n + 2) => pderiv (j : ℕ)) (X 0)).det ≠ 0 := by
  rw [derivationLowerJetJacobian_natShift, Matrix.det_one]
  exact one_ne_zero

/-- The existence form of the hypothesis. -/
theorem exists_det_derivationLowerJetJacobian_ne_zero (n : ℕ) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℂ R)
      (δ : Derivation ℂ R R) (partials : Fin (n + 2) → Derivation ℂ R R) (A : R),
      (derivationLowerJetJacobian δ n partials A).det ≠ 0 :=
  ⟨MvPolynomial ℕ ℂ, inferInstance, inferInstance, natShiftDerivation,
    fun j : Fin (n + 2) => pderiv (j : ℕ), X 0,
    det_derivationLowerJetJacobian_natShift_ne_zero n⟩

end

end GaloisForLFunctions.HTGeometry
