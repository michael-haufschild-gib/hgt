import GaloisForLFunctions.HTGeometry.MvPolynomialJetDerivative
import GaloisForLFunctions.HTGeometry.PointNondegeneracyPhaseRank

/-!
# Finite phase rank for a polynomial differential relation

The phase-rank bound applies verbatim to a relation given by a multivariate polynomial in the jets:
its derivative is the partial-derivative vector, and nondegeneracy in the top jet is the
nonvanishing of the corresponding partial derivative at one point of the line.
-/

open Filter Topology Metric Set MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r ρ : ℝ} {n : ℕ}

/-- **Finite phase rank for a polynomial differential relation.**  A strip almost periodic
holomorphic solution of a polynomial differential relation whose top partial derivative is nonzero at
one point of the line has finite rational Bohr frequency rank. -/
theorem rank_finite_of_mvPolynomial_relation (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) p = 0)
    (hnd0 : ∃ t₀ : ℝ, MvPolynomial.eval
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t₀ : ℂ) * Complex.I))
      ((pderiv (Fin.last n)) p) ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  refine rank_finite_of_nondegenerate_at_point hr hρ hrρ hF hap hf hfu hftb hn
    (continuous_mvEval p) (continuous_mvJetDeriv p)
    (fun y => (hasFDerivAt_mvEval p y).restrictScalars ℝ) hrel ?_
  obtain ⟨t₀, ht₀⟩ := hnd0
  refine ⟨t₀, ?_⟩
  rw [partialCoeff_mvJetDeriv]
  exact ht₀

end GaloisForLFunctions
