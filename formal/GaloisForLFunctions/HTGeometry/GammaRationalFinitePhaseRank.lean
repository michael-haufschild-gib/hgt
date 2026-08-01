import GaloisForLFunctions.HTGeometry.GammaRationalPhaseRank
import GaloisForLFunctions.HTGeometry.PolynomialRelationPhaseRank

/-!
# Finite phase rank over the Gamma field

The collapse turns a Gamma-rational differential relation into a constant-coefficient polynomial
relation, and a nonzero polynomial relation forces finite frequency rank.  Distinct monomials with a
nonzero coefficient make the collapsed relation nonzero, and the coefficient at the valuation-minimal
index is `1`, so the only hypotheses left are the strip almost periodicity of the solution and the
distinctness of the monomials of the relation.
-/

open Filter Topology Metric Set MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ R r ρ : ℝ} {N n : ℕ}

/-- **Finite phase rank over the Gamma field, with no analytic hypothesis left.**  A strip almost
periodic holomorphic solution of a differential relation with Gamma-rational coefficients whose
collapsed relation is a nonzero polynomial has finite rational Bohr frequency rank. -/
theorem rank_finite_of_gamma_rational_nontrivial (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hR : 0 < R) (hσR : R ≤ σ) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (pp qq : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (qq α).eval 0 ≠ 0) (hp0 : ∀ α, (pp α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (pp α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (qq α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hne : (∑ α : Fin N, C (gammaRatioLimit pp qq u v β α) *
      ∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α j)) ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  have hauto := gamma_rational_autonomous_relation hR hσR hΦ hap e Cf pp qq u v β hq0 hp0 hCf
    hrelC hmin
  refine rank_finite_of_polynomial_relation hr hρ hrρ hΦ hap hf hfu hftb n _ hne ?_
  intro z hz
  have h := hauto hz
  rw [← jetPoly_eq_mvEval]
  simpa [jetPoly] using h


/-- **Eq. (9) over the Gamma field.**  A strip almost periodic holomorphic solution of a differential
relation with Gamma-rational coefficients and distinct monomials has finite rational Bohr frequency
rank. -/
theorem rank_finite_of_gamma_rational_relation (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hR : 0 < R) (hσR : R ≤ σ) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (pp qq : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (qq α).eval 0 ≠ 0) (hp0 : ∀ α, (pp α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (pp α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (qq α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (he : Function.Injective e) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  have hβ : gammaRatioLimit pp qq u v β β ≠ 0 := by
    rw [gammaRatioLimit_self pp qq u v β (hp0 β) (hq0 β)]
    exact one_ne_zero
  exact rank_finite_of_gamma_rational_nontrivial hr hρ hrρ hR hσR hΦ hap e Cf pp qq u v β
    hq0 hp0 hCf hrelC hmin hf hfu hftb
    (monomialSum_ne_zero (gammaRatioLimit pp qq u v β) e he β hβ)

end GaloisForLFunctions
