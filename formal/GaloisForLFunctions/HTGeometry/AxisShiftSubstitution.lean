import GaloisForLFunctions.HTGeometry.RegularizedTransformBridge

/-!
# Shifting every variable by a polynomial in one distinguished variable

Adding a polynomial to a function shifts each jet slot by the corresponding derivative of that
polynomial, all of which are polynomials in the spectral variable.  The substitution realizing this
leaves the distinguished variable fixed and shifts every other by a polynomial in it.

Such a substitution is an algebra automorphism — its inverse shifts by the negatives — so it
preserves being nonzero, which is what transferring a differential relation requires.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Shift every variable other than the distinguished one by a polynomial in the distinguished
variable. -/
def axisShiftSubst {σ : Type*} [DecidableEq σ] (i : σ) (h : σ → Polynomial ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.bind₁ fun s =>
    if s = i then MvPolynomial.X i
    else MvPolynomial.X s + Polynomial.aeval (MvPolynomial.X i) (h s)

@[simp]
theorem axisShiftSubst_X_self {σ : Type*} [DecidableEq σ] (i : σ) (h : σ → Polynomial ℂ) :
    axisShiftSubst i h (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [axisShiftSubst]

@[simp]
theorem axisShiftSubst_X_ne {σ : Type*} [DecidableEq σ] {i s : σ} (hs : s ≠ i)
    (h : σ → Polynomial ℂ) :
    axisShiftSubst i h (MvPolynomial.X s)
      = MvPolynomial.X s + Polynomial.aeval (MvPolynomial.X i) (h s) := by
  simp [axisShiftSubst, hs]

/-- Shifting by the negated family undoes the shift. -/
theorem axisShiftSubst_axisShiftSubst {σ : Type*} [DecidableEq σ] (i : σ)
    (h : σ → Polynomial ℂ) (Q : MvPolynomial σ ℂ) :
    axisShiftSubst i (fun s => -(h s)) (axisShiftSubst i h Q) = Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [axisShiftSubst]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p s hp =>
      rw [map_mul, map_mul, hp]
      by_cases hs : s = i
      · subst hs
        rw [axisShiftSubst_X_self, axisShiftSubst_X_self]
      · rw [axisShiftSubst_X_ne hs, map_add, axisShiftSubst_X_ne hs]
        have haev : axisShiftSubst i (fun s => -(h s))
            (Polynomial.aeval (MvPolynomial.X i) (h s))
            = Polynomial.aeval (MvPolynomial.X i) (h s) := by
          induction (h s) using Polynomial.induction_on with
          | C a => simp [axisShiftSubst]
          | add p q hp hq => simp [map_add, hp, hq]
          | monomial k a ih =>
              simp only [Polynomial.aeval_X, Polynomial.aeval_C,
                map_mul, map_pow, axisShiftSubst_X_self]
              simp [axisShiftSubst]
        rw [haev]
        simp [Polynomial.aeval_neg]

/-- **The axis shift preserves nonvanishing.** -/
theorem axisShiftSubst_ne_zero {σ : Type*} [DecidableEq σ] (i : σ) (h : σ → Polynomial ℂ)
    {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) : axisShiftSubst i h Q ≠ 0 := by
  intro hzero
  apply hQ
  rw [← axisShiftSubst_axisShiftSubst i h Q, hzero, map_zero]

end

end GaloisForLFunctions.HTGeometry
