import GaloisForLFunctions.HTGeometry.AddPolynomialInvariance

/-!
# The Herglotz gauge reduces to its multiplicative part

The regularized transform is the Cauchy transform of the weighted measure multiplied by `1 + z ^ (2 : ℕ)`
and shifted by `z` times the total mass.  The shift is a polynomial, so the additive invariance
removes it outright.

What is left is the purely multiplicative question: whether multiplying by a nonzero polynomial
changes hypertranscendence.  That is the only remaining step of the gauge.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The polynomial shift of the gauge is removable.**  A transform presented as a polynomial plus
another function is hypertranscendental exactly when that other function is, provided the other
function is smooth. -/
theorem differentiallyAlgebraic_add_polynomial_iff {f : ℂ → ℂ}
    (hf : ∀ j, Differentiable ℂ (iteratedDeriv j f))
    (hfp : ∀ (b : Polynomial ℂ) (j : ℕ),
      Differentiable ℂ (iteratedDeriv j fun w => f w + Polynomial.eval w b))
    (b : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun w => f w + Polynomial.eval w b) ↔
      DifferentiallyAlgebraic f := by
  constructor
  · exact differentiallyAlgebraic_add_polynomial hf b
  · intro h
    refine differentiallyAlgebraic_add_polynomial (f := fun w => f w + Polynomial.eval w b)
      (hfp b) (-b) ?_
    simpa using h

/-- **The gauge reduces to its multiplicative part.**  Presenting the regularized transform as a
polynomial shift of a multiple of the Cauchy transform, the shift drops out and only the
multiplicative factor remains in question. -/
theorem hypertranscendental_gauge_iff_mul {C m : ℂ → ℂ} (b : Polynomial ℂ)
    (hgauge : ∀ z, m z = Polynomial.eval z b + (1 + z ^ (2 : ℕ)) * C z)
    (hf : ∀ j, Differentiable ℂ (iteratedDeriv j fun z => (1 + z ^ (2 : ℕ)) * C z))
    (hfp : ∀ (c : Polynomial ℂ) (j : ℕ),
      Differentiable ℂ (iteratedDeriv j fun w =>
        (1 + w ^ (2 : ℕ)) * C w + Polynomial.eval w c)) :
    Hypertranscendental m ↔ Hypertranscendental (fun z => (1 + z ^ (2 : ℕ)) * C z) := by
  have hfun : m = fun z => (1 + z ^ (2 : ℕ)) * C z + Polynomial.eval z b := by
    funext z
    rw [hgauge z]
    ring
  rw [hfun, Hypertranscendental, Hypertranscendental]
  exact not_congr (differentiallyAlgebraic_add_polynomial_iff hf hfp b)

end

end GaloisForLFunctions.HTGeometry
