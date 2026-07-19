import GaloisForLFunctions.HTGeometry.NegSupportedDimension
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Shifting one polynomial variable by a constant

Adding a constant to a function changes its value but none of its derivatives, so a differential
polynomial annihilating the shifted function becomes one annihilating the original after shifting
the value variable.

Such a shift is an algebra automorphism of the polynomial ring — its inverse shifts by the negative
constant — so it preserves being nonzero, which is what the transfer of differential algebraicity
requires.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Shifting one polynomial variable by a constant. -/
def shiftSubst {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.bind₁ fun s =>
    if s = i then MvPolynomial.X s + MvPolynomial.C c else MvPolynomial.X s

@[simp]
theorem shiftSubst_X_self {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ) :
    shiftSubst i c (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C c := by
  simp [shiftSubst]

@[simp]
theorem shiftSubst_X_ne {σ : Type*} [DecidableEq σ] {i s : σ} (h : s ≠ i) (c : ℂ) :
    shiftSubst i c (MvPolynomial.X s) = MvPolynomial.X s := by
  simp [shiftSubst, h]

/-- Shifting by the negative constant undoes the shift. -/
theorem shiftSubst_shiftSubst {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ)
    (Q : MvPolynomial σ ℂ) :
    shiftSubst i (-c) (shiftSubst i c Q) = Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [shiftSubst]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      by_cases h : s = i
      · subst h
        rw [shiftSubst_X_self, map_add, shiftSubst_X_self]
        simp [shiftSubst]
      · rw [shiftSubst_X_ne h, shiftSubst_X_ne h]

/-- **Shifting preserves nonvanishing.** -/
theorem shiftSubst_ne_zero {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ)
    {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) : shiftSubst i c Q ≠ 0 := by
  intro hzero
  apply hQ
  rw [← shiftSubst_shiftSubst i c Q, hzero, map_zero]

/-- Evaluating a shifted polynomial is evaluating the original at the shifted point. -/
theorem eval_shiftSubst {σ : Type*} [DecidableEq σ] (i : σ) (c : ℂ)
    (Q : MvPolynomial σ ℂ) (v : σ → ℂ) :
    MvPolynomial.eval v (shiftSubst i c Q)
      = MvPolynomial.eval (Function.update v i (v i + c)) Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [shiftSubst]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      by_cases h : s = i
      · subst h
        simp [shiftSubst]
      · simp [shiftSubst, h]

end

end GaloisForLFunctions.HTGeometry
