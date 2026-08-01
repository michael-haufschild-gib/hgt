import GaloisForLFunctions.HTGeometry.ProjectiveHorizonReciprocalJacobian

/-!
# The numerators of the reciprocal jets, and their exponential specialisation

Each jet of the reciprocal of the base coordinate is a polynomial divided by a power of that
coordinate, and the numerators satisfy a two-term recursion obtained from the quotient rule.

Substituting the same variable for every jet coordinate models the exponential, whose jets are all
equal.  Under that substitution the jet shift becomes the Euler operator, so the numerators become
the alternating powers.  This is the specialisation that certifies the reconstruction determinant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {C : Type*} [Field C]

/-- The numerator of the `j`-th jet of the reciprocal of the base coordinate. -/
def recipNumer (C : Type*) [Field C] : ℕ → FreeScalarJetPolynomial C
  | 0 => 1
  | (j + 1) =>
      MvPolynomial.X 0 * freeJetShiftPolynomialDerivation C (recipNumer C j) -
        (j + 1) • (MvPolynomial.X 1 * recipNumer C j)

@[simp]
theorem recipNumer_zero : recipNumer C 0 = 1 := rfl

theorem recipNumer_succ (j : ℕ) :
    recipNumer C (j + 1) =
      MvPolynomial.X 0 * freeJetShiftPolynomialDerivation C (recipNumer C j) -
        (j + 1) • (MvPolynomial.X 1 * recipNumer C j) := rfl

/-- **The reciprocal jets are the numerators over powers of the base coordinate.** -/
theorem algebraMap_recipNumer (j : ℕ) :
    algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) (recipNumer C j) =
      recipJet C j * (freeCoordinate C ℕ 0) ^ (j + 1) := by
  have hw : freeCoordinate C ℕ 0 ≠ 0 := freeScalarJetCoordinate_ne_zero 0
  induction j with
  | zero =>
      rw [recipNumer_zero, map_one, recipJet, Function.iterate_zero_apply, recipBase, pow_one,
        inv_mul_cancel₀ hw]
  | succ j ih =>
      have hd := congrArg (freeJetShift C) ih
      rw [freeJetShift_algebraMap, Derivation.leibniz, Derivation.leibniz_pow,
        freeJetShift_freeCoordinate] at hd
      have hstep : recipJet C (j + 1) = freeJetShift C (recipJet C j) := by
        rw [recipJet, recipJet, Function.iterate_succ_apply']
      rw [recipNumer_succ, map_sub, map_mul, map_nsmul, map_mul, hstep]
      show freeCoordinate C ℕ 0 *
          algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
            (freeJetShiftPolynomialDerivation C (recipNumer C j)) -
          (j + 1) • (freeCoordinate C ℕ 1 *
            algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) (recipNumer C j)) = _
      rw [hd, ih]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      ring

/-! ## The exponential specialisation -/

/-- Substitution of a single variable for every jet coordinate: the jet model of the exponential,
all of whose jets agree. -/
def expJetEval (C : Type*) [Field C] : FreeScalarJetPolynomial C →ₐ[C] Polynomial C :=
  MvPolynomial.aeval fun _ => (Polynomial.X : Polynomial C)

@[simp]
theorem expJetEval_X (j : ℕ) :
    expJetEval C (MvPolynomial.X j) = (Polynomial.X : Polynomial C) :=
  MvPolynomial.aeval_X _ _

/-- **Under the exponential specialisation the jet shift becomes the Euler operator.** -/
theorem expJetEval_shift (P : FreeScalarJetPolynomial C) :
    expJetEval C (freeJetShiftPolynomialDerivation C P) =
      Polynomial.X * Polynomial.derivative (expJetEval C P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hCa : (MvPolynomial.C a : FreeScalarJetPolynomial C) =
          algebraMap C (FreeScalarJetPolynomial C) a := rfl
      have hev : expJetEval C (MvPolynomial.C a) = Polynomial.C a := by
        rw [hCa, AlgHom.commutes]
        rfl
      rw [hCa, Derivation.map_algebraMap, map_zero, ← hCa, hev, Polynomial.derivative_C, mul_zero]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add, Polynomial.derivative_add, mul_add]
  | mul_X p k hp =>
      have hL : freeJetShiftPolynomialDerivation C (p * MvPolynomial.X k) =
          p * MvPolynomial.X (k + 1) +
            MvPolynomial.X k * freeJetShiftPolynomialDerivation C p := by
        rw [Derivation.leibniz, freeJetShiftPolynomialDerivation_X, smul_eq_mul, smul_eq_mul]
      rw [hL]
      simp only [map_add, map_mul, expJetEval_X]
      rw [hp, Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      ring

/-- **The numerators specialise to the alternating powers.** -/
theorem expJetEval_recipNumer (j : ℕ) :
    expJetEval C (recipNumer C j) = (-1 : Polynomial C) ^ j * Polynomial.X ^ j := by
  have hderiv : ∀ i : ℕ, Polynomial.derivative
      ((-1 : Polynomial C) ^ i * Polynomial.X ^ i) =
      (-1 : Polynomial C) ^ i * ((i : Polynomial C) * Polynomial.X ^ (i - 1)) := by
    intro i
    have hc : Polynomial.derivative ((-1 : Polynomial C) ^ i) = 0 := by
      rw [show ((-1 : Polynomial C)) = Polynomial.C (-1 : C) from by simp, ← Polynomial.C_pow,
        Polynomial.derivative_C]
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow, hc, zero_mul, zero_add]
    simp
  induction j with
  | zero => rw [recipNumer_zero, map_one, pow_zero, pow_zero, one_mul]
  | succ j ih =>
      rw [recipNumer_succ, map_sub, map_mul, map_nsmul, map_mul, expJetEval_shift, ih,
        expJetEval_X, expJetEval_X, hderiv]
      cases j with
      | zero => simp
      | succ i =>
          simp only [Nat.add_sub_cancel, nsmul_eq_mul]
          push_cast
          ring
end

end GaloisForLFunctions.HTGeometry
