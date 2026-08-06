import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Lifting a jet equation to the last variable

An algebraic differential equation of order `n` is naturally a univariate
polynomial in the top jet with coefficients polynomial in the lower jets.  The
same datum is a polynomial in `n + 1` variables in which the top jet is the last
variable.

The lift sends the polynomial variable to the last coordinate and renames the
coefficient variables along `Fin.castSucc`.  Evaluation is compatible with the
two-step evaluation of the univariate presentation, and the partial derivative
in the last coordinate is the lift of the univariate derivative: the separant
of the equation is the last partial derivative of its lift.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### The last coordinate is absent from renamed coefficients -/

theorem pderiv_last_rename_castSucc {n : ℕ} (a : MvPolynomial (Fin n) R) :
    MvPolynomial.pderiv (Fin.last n) (MvPolynomial.rename Fin.castSucc a) = 0 := by
  induction a using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.rename_C, MvPolynomial.pderiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp,
        MvPolynomial.pderiv_X_of_ne (Fin.castSucc_lt_last i).ne, smul_zero, smul_zero,
        add_zero]

/-! ### Powers of a single variable -/

theorem pderiv_X_pow_succ_self {σ : Type*} (i : σ) (k : ℕ) :
    MvPolynomial.pderiv i ((MvPolynomial.X i : MvPolynomial σ R) ^ (k + 1))
      = ((k + 1 : ℕ) : MvPolynomial σ R) * MvPolynomial.X i ^ k := by
  induction k with
  | zero =>
      rw [pow_one, MvPolynomial.pderiv_X_self, pow_zero, Nat.cast_one, mul_one]
  | succ m ih =>
      rw [pow_succ, Derivation.leibniz, MvPolynomial.pderiv_X_self, ih]
      simp only [smul_eq_mul, mul_one]
      push_cast
      ring

/-! ### The lift -/

/-- The polynomial in `n + 1` variables presenting a univariate polynomial in
the top jet: the polynomial variable becomes the last coordinate. -/
def lastVariableJetLift {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial (Fin (n + 1)) R :=
  Polynomial.eval₂ (MvPolynomial.rename Fin.castSucc).toRingHom
    (MvPolynomial.X (Fin.last n)) P

theorem jetLift_zero {n : ℕ} :
    lastVariableJetLift (0 : Polynomial (MvPolynomial (Fin n) R)) = 0 :=
  Polynomial.eval₂_zero _ _

theorem jetLift_add {n : ℕ} (p q : Polynomial (MvPolynomial (Fin n) R)) :
    lastVariableJetLift (p + q) = lastVariableJetLift p + lastVariableJetLift q :=
  Polynomial.eval₂_add _ _

theorem jetLift_monomial {n : ℕ} (k : ℕ) (a : MvPolynomial (Fin n) R) :
    lastVariableJetLift (Polynomial.monomial k a)
      = MvPolynomial.rename Fin.castSucc a * MvPolynomial.X (Fin.last n) ^ k :=
  Polynomial.eval₂_monomial _ _

/-- **Evaluation of the lift is the two-step evaluation of the univariate
presentation.** -/
theorem eval_jetLift {n : ℕ} (a : Fin (n + 1) → R)
    (P : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.eval a (lastVariableJetLift P)
      = Polynomial.eval₂ (MvPolynomial.eval fun i : Fin n => a i.castSucc)
        (a (Fin.last n)) P := by
  have hhom : ((MvPolynomial.eval a).comp
        (MvPolynomial.rename Fin.castSucc : MvPolynomial (Fin n) R →ₐ[R] _).toRingHom)
      = (MvPolynomial.eval fun i : Fin n => a i.castSucc) := by
    refine RingHom.ext fun p => ?_
    show MvPolynomial.eval a (MvPolynomial.rename Fin.castSucc p) = _
    rw [MvPolynomial.eval_rename]
    rfl
  rw [lastVariableJetLift, Polynomial.hom_eval₂, hhom, MvPolynomial.eval_X]

/-- **The separant is the last partial derivative of the lift.** -/
theorem pderiv_last_jetLift {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.pderiv (Fin.last n) (lastVariableJetLift P)
      = lastVariableJetLift (Polynomial.derivative P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [jetLift_add, map_add, hp, hq, Polynomial.derivative_add, jetLift_add]
  | monomial k a =>
      cases k with
      | zero =>
          rw [jetLift_monomial, pow_zero, mul_one, pderiv_last_rename_castSucc,
            Polynomial.derivative_monomial, Nat.cast_zero, mul_zero,
            Polynomial.monomial_zero_right, jetLift_zero]
      | succ m =>
          rw [jetLift_monomial, Derivation.leibniz, pderiv_last_rename_castSucc,
            smul_zero, add_zero, pderiv_X_pow_succ_self,
            Polynomial.derivative_monomial, jetLift_monomial, map_mul,
            map_natCast, Nat.add_sub_cancel]
          simp only [smul_eq_mul]
          ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-! ### The inverse presentation -/

/-- A polynomial in `n + 1` variables read as a univariate polynomial in the
last variable. -/
def jetUnlift {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) R) :
    Polynomial (MvPolynomial (Fin n) R) :=
  MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
    (fun i : Fin (n + 1) =>
      if h : (i : ℕ) < n then Polynomial.C (MvPolynomial.X ⟨(i : ℕ), h⟩)
      else Polynomial.X) Q

/-- **The lift undoes the inverse presentation.** -/
theorem lastVariableJetLift_jetUnlift {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) R) :
    lastVariableJetLift (jetUnlift Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      rw [jetUnlift, MvPolynomial.eval₂_C, RingHom.comp_apply,
        lastVariableJetLift, Polynomial.eval₂_C]
      show MvPolynomial.rename Fin.castSucc (MvPolynomial.C a) = _
      rw [MvPolynomial.rename_C]
  | add p q hp hq =>
      rw [jetUnlift, MvPolynomial.eval₂_add, ← jetUnlift, ← jetUnlift,
        jetLift_add, hp, hq]
  | mul_X p i hp =>
      rw [jetUnlift, MvPolynomial.eval₂_mul, ← jetUnlift, MvPolynomial.eval₂_X,
        lastVariableJetLift, Polynomial.eval₂_mul, ← lastVariableJetLift,
        ← lastVariableJetLift, hp]
      congr 1
      by_cases h : (i : ℕ) < n
      · rw [dif_pos h, lastVariableJetLift, Polynomial.eval₂_C]
        show MvPolynomial.rename Fin.castSucc (MvPolynomial.X _) = _
        rw [MvPolynomial.rename_X]
        congr 1
      · have hlast : i = Fin.last n := by
          refine Fin.ext ?_
          rw [Fin.val_last]
          have hle : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
          omega
        rw [dif_neg h, lastVariableJetLift, Polynomial.eval₂_X, hlast]

theorem jetUnlift_ne_zero {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) R} (hQ : Q ≠ 0) :
    jetUnlift Q ≠ 0 := fun h =>
  hQ (by rw [← lastVariableJetLift_jetUnlift Q, h, jetLift_zero])

end

end GaloisForLFunctions.HTGeometry
