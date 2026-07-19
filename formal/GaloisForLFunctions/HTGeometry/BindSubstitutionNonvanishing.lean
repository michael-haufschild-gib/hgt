import GaloisForLFunctions.HTGeometry.TriangularSolvability

/-!
# Nonvanishing for a substitution given by its coordinate images

A substitution specified by the image of each variable acts on points by evaluating those images.
So the nonvanishing criterion applies directly: if that induced point map covers the locus where
some fixed nonzero polynomial does not vanish, the substitution kills no nonzero polynomial.

For a triangular family the covered locus is the nonvanishing locus of the diagonal, and the
covering is the solvability of the triangular system.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The point map induced by a coordinatewise substitution. -/
def bindPointMap {σ : Type*} (J : σ → MvPolynomial σ ℂ) (v : σ → ℂ) : σ → ℂ :=
  fun s => MvPolynomial.eval v (J s)

/-- Evaluating a substituted polynomial is evaluating the original at the induced point. -/
theorem eval_bind₁_eq {σ : Type*} (J : σ → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ)
    (v : σ → ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ J Q)
      = MvPolynomial.eval (bindPointMap J v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p s hp => simp [map_mul, hp, bindPointMap]

/-- **A coordinatewise substitution with covering point map preserves nonvanishing.** -/
theorem bind₁_ne_zero_of_pointMap_surjective {σ : Type*}
    (J : σ → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) (hg : g ≠ 0)
    (hsurj : ∀ w : σ → ℂ, MvPolynomial.eval w g ≠ 0 → ∃ v, bindPointMap J v = w)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : MvPolynomial.bind₁ J P ≠ 0 :=
  subst_ne_zero_of_pointMap_surjective (MvPolynomial.bind₁ J) (bindPointMap J)
    (fun Q v => eval_bind₁_eq J Q v) g hg hsurj hP

/-- **The injective form.** -/
theorem bind₁_injective_of_pointMap_surjective {σ : Type*}
    (J : σ → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ) (hg : g ≠ 0)
    (hsurj : ∀ w : σ → ℂ, MvPolynomial.eval w g ≠ 0 → ∃ v, bindPointMap J v = w) :
    Function.Injective (MvPolynomial.bind₁ J : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) :=
  subst_injective_of_pointMap_surjective (MvPolynomial.bind₁ J) (bindPointMap J)
    (fun Q v => eval_bind₁_eq J Q v) g hg hsurj

end

end GaloisForLFunctions.HTGeometry
