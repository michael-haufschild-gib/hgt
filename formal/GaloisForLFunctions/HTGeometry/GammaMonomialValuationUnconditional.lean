import GaloisForLFunctions.HTGeometry.GammaFiniteProjectiveLaw
import GaloisForLFunctions.HTGeometry.GammaVerticalDecay

/-!
# The monomial valuation residue, unconditionally

The projective normalization of a Gamma-field element on a vertical line was proved with the decay of
`Γ` along that line as an explicit hypothesis.  That decay is now a theorem, so the normalization is
unconditional on every vertical line of positive abscissa.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- **Eq. (3), unconditionally.**  On any vertical line with positive abscissa, a Gamma-field
element normalized by its dominant Gamma powers converges to the residue of its `L`-coefficients. -/
theorem gamma_monomial_valuation_residue_of_pos (P Q R S : Polynomial ℂ) (u v : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hP : P = Polynomial.X ^ u * R) (hQ : Q = Polynomial.X ^ v * S)
    (hS0 : S.eval 0 ≠ 0) :
    Tendsto (fun t : ℝ =>
        (P.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ u)
          / (Q.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ v))
      atTop (nhds (R.eval 0 / S.eval 0)) :=
  gamma_monomial_valuation_residue P Q R S u v σ hP hQ hS0
    (Gamma_vertical_tendsto_nhdsWithin_zero hσ)

end GaloisForLFunctions
