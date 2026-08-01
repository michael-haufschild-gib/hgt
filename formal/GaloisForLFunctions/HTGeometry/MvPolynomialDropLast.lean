import GaloisForLFunctions.HTGeometry.MvPolynomialPDerivDegree
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Dropping an unused variable

A polynomial that does not involve its last variable is the image of a polynomial in one variable
fewer, with the same evaluation on the truncated point.  Since a polynomial over an infinite domain
is determined by its evaluations, the truncated polynomial is nonzero whenever the original is.

This is the order-descent step of an algebraic differential relation that has ceased to involve its
top jet.
-/

open MvPolynomial

namespace GaloisForLFunctions

variable {n : ℕ}

/-- Forgetting the last coordinate. -/
def dropLastIdx (n : ℕ) [NeZero n] : Fin (n + 1) → Fin n :=
  fun k => if h : (k : ℕ) < n then ⟨k, h⟩ else 0

theorem castSucc_dropLastIdx [NeZero n] {k : Fin (n + 1)} (hk : k ≠ Fin.last n) :
    Fin.castSucc (dropLastIdx n k) = k := by
  have hlt : (k : ℕ) < n := by
    have := Fin.val_lt_last hk
    exact this
  simp only [dropLastIdx, dif_pos hlt]
  exact Fin.ext rfl

/-- A polynomial that does not involve the last variable, read in one variable fewer. -/
noncomputable def dropLastPoly [NeZero n] (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial (Fin n) ℂ := MvPolynomial.rename (dropLastIdx n) p

theorem eval_dropLastPoly [NeZero n] {p : MvPolynomial (Fin (n + 1)) ℂ}
    (h : MvPolynomial.degreeOf (Fin.last n) p = 0) (y : Fin (n + 1) → ℂ) :
    MvPolynomial.eval (fun j : Fin n => y (Fin.castSucc j)) (dropLastPoly p)
      = MvPolynomial.eval y p := by
  rw [dropLastPoly, MvPolynomial.eval_rename]
  refine (eval_eq_of_degreeOf_eq_zero h ?_).symm
  intro j hj
  show y j = (fun j : Fin n => y (Fin.castSucc j)) (dropLastIdx n j)
  simp only
  rw [castSucc_dropLastIdx hj]

theorem dropLastPoly_ne_zero [NeZero n] {p : MvPolynomial (Fin (n + 1)) ℂ}
    (h : MvPolynomial.degreeOf (Fin.last n) p = 0) (hp : p ≠ 0) : dropLastPoly p ≠ 0 := by
  intro hzero
  refine hp (MvPolynomial.funext fun y => ?_)
  have := eval_dropLastPoly h y
  rw [hzero] at this
  simpa using this.symm

end GaloisForLFunctions
