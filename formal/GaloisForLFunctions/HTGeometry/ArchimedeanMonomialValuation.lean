import GaloisForLFunctions.HTGeometry.GammaScaleVerticalDecay
import GaloisForLFunctions.HTGeometry.GammaFiniteProjectiveLaw

/-!
# The monomial-valuation residue of the archimedean product

The lowest-power ratio law of the corpus is stated for an arbitrary argument tending to zero in a
punctured neighbourhood, so it applies verbatim to the archimedean product
`G(s) = e^{αs}∏_j Γ(λ_j s + μ_j)` in place of `Γ`.  This is the projective form of the card's
equation `(3)` for the general commensurable product.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The archimedean product on a vertical line. -/
def archimedeanProductLine {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ) (α σ t : ℝ) : ℂ :=
  Complex.exp ((α : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))
    * ∏ j : Fin d, Complex.Gamma ((lam j : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) + μ j)

/-- **Monomial-valuation residue for the archimedean product.**  A `K_G`-element presented as a
quotient of polynomials in `G`, normalized by its dominant `G` powers, converges to the residue of
its coefficients. -/
theorem archimedeanProduct_monomial_valuation_residue (P Q R S : Polynomial ℂ) (u v : ℕ)
    {d : ℕ} (hd : 0 < d) (lam : Fin d → ℝ) (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) {σ : ℝ}
    (hσ : ∀ j, 0 < lam j * σ + (μ j).re) (α : ℝ)
    (hP : P = Polynomial.X ^ u * R) (hQ : Q = Polynomial.X ^ v * S) (hS0 : S.eval 0 ≠ 0) :
    Tendsto (fun t : ℝ =>
        (P.eval (archimedeanProductLine lam μ α σ t)
            / (archimedeanProductLine lam μ α σ t) ^ u)
          / (Q.eval (archimedeanProductLine lam μ α σ t)
            / (archimedeanProductLine lam μ α σ t) ^ v))
      atTop (nhds (R.eval 0 / S.eval 0)) :=
  (polynomial_lowest_power_ratio_tendsto P Q R S u v hP hQ hS0).comp
    (archimedeanProduct_vertical_tendsto_nhdsWithin_zero hd lam μ hlam hσ α)

end

end GaloisForLFunctions.HTGeometry
