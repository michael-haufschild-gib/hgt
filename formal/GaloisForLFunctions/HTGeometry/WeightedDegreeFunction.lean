import GaloisForLFunctions.HTGeometry.DegreeDeterminantNonCancellation

/-!
# The weighted degree as a degree function

Substituting the monomial curve `X_j ↦ X_j · t^(w_j)` turns a polynomial in `n` coordinates into a
polynomial in one variable `t` whose coefficients still remember the coordinates.  Nothing cancels —
distinct exponent vectors keep distinct coordinate monomials — so the substitution is injective and
the `t`-degree of the image is the weighted degree of the original.

Degrees of a domain-valued substitution are additive on products and subadditive on sums, so the
weighted degree is a degree function in the sense of `IsDegree` and the determinant criteria apply
to matrices of polynomials.  Rational entries are handled by clearing one denominator per row: the
determinant changes by a nonzero factor and the row constants of a staircase absorb the shift.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ : Type*}

/-- Substitution of the monomial curve `X_j ↦ X_j · t^(w_j)`. -/
def curveHom (w : σ → ℕ) :
    MvPolynomial σ ℂ →+* Polynomial (MvPolynomial σ ℂ) :=
  eval₂Hom (Polynomial.C.comp (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ))
    (fun j => Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ (w j))

@[simp] theorem curveHom_C (w : σ → ℕ) (r : ℂ) :
    curveHom w (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  simp [curveHom]

@[simp] theorem curveHom_X (w : σ → ℕ) (j : σ) :
    curveHom w (MvPolynomial.X j) = Polynomial.C (MvPolynomial.X j) * Polynomial.X ^ (w j) := by
  simp [curveHom]

/-- **The curve substitution is injective**: evaluating `t` at one undoes it. -/
theorem curveHom_injective (w : σ → ℕ) : Function.Injective (curveHom w) := by
  have hcomp : (Polynomial.evalRingHom (1 : MvPolynomial σ ℂ)).comp (curveHom w)
      = RingHom.id (MvPolynomial σ ℂ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp
    · simp
  intro a b hab
  have h := congrArg (Polynomial.evalRingHom (1 : MvPolynomial σ ℂ)) hab
  have ha : ((Polynomial.evalRingHom (1 : MvPolynomial σ ℂ)).comp (curveHom w)) a
      = ((Polynomial.evalRingHom (1 : MvPolynomial σ ℂ)).comp (curveHom w)) b := h
  rw [hcomp] at ha
  simpa using ha

theorem curveHom_eq_zero_iff (w : σ → ℕ) (p : MvPolynomial σ ℂ) :
    curveHom w p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have : curveHom w p = curveHom w 0 := by rw [h, map_zero]
    exact curveHom_injective w this
  · intro h; rw [h, map_zero]

open scoped Classical in
/-- The weighted degree of a polynomial: the `t`-degree of its monomial-curve substitution. -/
def wdeg (w : σ → ℕ) (p : MvPolynomial σ ℂ) : WithBot ℤ :=
  if p = 0 then ⊥ else (((curveHom w p).natDegree : ℤ) : WithBot ℤ)

@[simp] theorem wdeg_zero (w : σ → ℕ) : wdeg w (0 : MvPolynomial σ ℂ) = ⊥ := by
  simp [wdeg]

theorem wdeg_of_ne_zero (w : σ → ℕ) {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    wdeg w p = (((curveHom w p).natDegree : ℤ) : WithBot ℤ) := by
  simp [wdeg, hp]

theorem wdeg_eq_bot_iff (w : σ → ℕ) (p : MvPolynomial σ ℂ) :
    wdeg w p = ⊥ ↔ p = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [wdeg_of_ne_zero w hp]
    simp [hp]

/-- **The weighted degree is a degree function.** -/
theorem isDegree_wdeg (w : σ → ℕ) : IsDegree (wdeg (σ := σ) w) := by
  refine ⟨wdeg_eq_bot_iff w, ?_, ?_⟩
  · intro p q
    by_cases hp : p = 0
    · simp [hp]
    by_cases hq : q = 0
    · simp [hq]
    have hpq : p * q ≠ 0 := mul_ne_zero hp hq
    have hcp : curveHom w p ≠ 0 := fun h => hp ((curveHom_eq_zero_iff w p).mp h)
    have hcq : curveHom w q ≠ 0 := fun h => hq ((curveHom_eq_zero_iff w q).mp h)
    rw [wdeg_of_ne_zero w hpq, wdeg_of_ne_zero w hp, wdeg_of_ne_zero w hq, map_mul,
      Polynomial.natDegree_mul hcp hcq]
    push_cast
    rfl
  · intro p q
    by_cases hpq : p + q = 0
    · simp [hpq]
    by_cases hp : p = 0
    · subst hp; simp
    by_cases hq : q = 0
    · subst hq; simp
    have hcast : ∀ a b : ℕ, a ≤ b →
        (((a : ℤ) : WithBot ℤ)) ≤ (((b : ℤ) : WithBot ℤ)) := by
      intro a b hab
      exact_mod_cast hab
    rw [wdeg_of_ne_zero w hpq, wdeg_of_ne_zero w hp, wdeg_of_ne_zero w hq, map_add]
    refine le_trans (hcast _ _ (Polynomial.natDegree_add_le _ _)) ?_
    rcases le_total (curveHom w p).natDegree (curveHom w q).natDegree with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _

@[simp] theorem wdeg_X (w : σ → ℕ) (j : σ) :
    wdeg w (MvPolynomial.X j : MvPolynomial σ ℂ) = ((w j : ℤ) : WithBot ℤ) := by
  have hX : (MvPolynomial.X j : MvPolynomial σ ℂ) ≠ 0 := MvPolynomial.X_ne_zero j
  rw [wdeg_of_ne_zero w hX, curveHom_X]
  have hC : (Polynomial.C (MvPolynomial.X j : MvPolynomial σ ℂ)) ≠ 0 := by
    simp
  rw [Polynomial.natDegree_mul hC (pow_ne_zero _ Polynomial.X_ne_zero),
    Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
  simp

theorem wdeg_C (w : σ → ℕ) {r : ℂ} (hr : r ≠ 0) :
    wdeg w (MvPolynomial.C r : MvPolynomial σ ℂ) = 0 := by
  have hne : (MvPolynomial.C r : MvPolynomial σ ℂ) ≠ 0 := by
    simpa using hr
  rw [wdeg_of_ne_zero w hne, curveHom_C, Polynomial.natDegree_C]
  rfl

end GaloisForLFunctions.HTGeometry

end
