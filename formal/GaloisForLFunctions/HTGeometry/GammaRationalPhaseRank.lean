import GaloisForLFunctions.HTGeometry.GammaRationalStripCollapse
import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRank
import GaloisForLFunctions.HTGeometry.NondegenerateSolutionPhaseRank
import GaloisForLFunctions.HTGeometry.PointNondegeneracyPhaseRank
import GaloisForLFunctions.HTGeometry.JetPolynomialDerivative

/-!
# Finite phase rank over the Gamma field

A strip almost periodic holomorphic function satisfying a differential relation with Gamma-rational
coefficients satisfies the constant-coefficient relation `jetPoly (gammaRatioLimit …)` on the whole
strip.  That relation is a polynomial in the jets, so its Fréchet derivative is explicit, and the
phase-rank bound applies with no hypothesis on the coefficients at all.

This is eq. (9) over the Gamma field: the rational Bohr frequency rank of the line restriction is at
most `2 |T| (n+1)`, the only remaining input being a regularity region for the solutions themselves.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ R r ρ : ℝ} {N n : ℕ}

/-- **Eq. (9) over the Gamma field.**  A strip almost periodic holomorphic solution of a
Gamma-rational differential relation, regular at one of finitely many sample times, has rational Bohr
frequency rank at most `2 |T| (n+1)`. -/
theorem rank_le_of_gamma_rational (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hσR : R ≤ σ) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (p q : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (q α).eval 0 ≠ 0) (hp0 : ∀ α, (p α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (p α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (q α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ} {T : Finset ι}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hC : ∀ i, 0 ≤ C i)
    (hbnd : ∀ i, ∀ y ∈ S i, ‖jetPolyDeriv (gammaRatioLimit p q u v β) e y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hatlas : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ),
        jetPoly (gammaRatioLimit p q u v β) e
          (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ i ∈ T, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * (n + 1)) : ℕ) : Cardinal) := by
  have hauto := gamma_rational_autonomous_relation hR hσR hΦ hap e Cf p q u v β hq0 hp0 hCf
    hrelC hmin
  have hrel : ∀ z ∈ verticalStrip σ R, jetPoly (gammaRatioLimit p q u v β) e
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z) = 0 := by
    intro z hz
    have := hauto hz
    simpa [jetPoly] using this
  exact rank_le_of_strip_solution hr hρ hrρ hΦ hap hf hfu hftb hn
    (continuous_jetPoly (gammaRatioLimit p q u v β) e) hrel hSopen hSconv
    (fun i y _ => hasFDerivWithinAt_jetPoly (gammaRatioLimit p q u v β) e (S i) y)
    hC hbnd hdom hatlas


/-- **Finite phase rank over the Gamma field from nondegeneracy alone.**  If the collapsed relation
has nonzero top partial derivative at some jet along the line of every holomorphic solution,
the rational Bohr frequency rank of the line restriction is finite — no atlas, no regularity region,
and no hypothesis on the coefficients. -/
theorem rank_finite_of_gamma_rational (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hσR : R ≤ σ) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (p q : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (q α).eval 0 ≠ 0) (hp0 : ∀ α, (p α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (p α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (q α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n)
    (hnd : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ),
        jetPoly (gammaRatioLimit p q u v β) e
          (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ t : ℝ, partialCoeff (jetPolyDeriv (gammaRatioLimit p q u v β) e
        (fun k : Fin (n + 1) =>
          iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  have hauto := gamma_rational_autonomous_relation hR hσR hΦ hap e Cf p q u v β hq0 hp0 hCf
    hrelC hmin
  have hrel : ∀ z ∈ verticalStrip σ R, jetPoly (gammaRatioLimit p q u v β) e
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z) = 0 := by
    intro z hz
    have := hauto hz
    simpa [jetPoly] using this
  exact rank_finite_of_nondegenerate_solution hr hρ hrρ hΦ hap hf hfu hftb hn
    (continuous_jetPoly (gammaRatioLimit p q u v β) e)
    (continuous_jetPolyDeriv (gammaRatioLimit p q u v β) e)
    (fun y => (hasFDerivAt_jetPoly (gammaRatioLimit p q u v β) e y).restrictScalars ℝ)
    hrel hnd


/-- **Finite phase rank over the Gamma field from one nondegenerate point.**  If the collapsed
relation has nonzero top partial derivative at a single jet of the solution itself, the rational Bohr
frequency rank of the line restriction is finite. -/
theorem rank_finite_of_gamma_rational_at_point (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hR : 0 < R) (hσR : R ≤ σ) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (p q : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (q α).eval 0 ≠ 0) (hp0 : ∀ α, (p α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (p α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (q α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n)
    (hnd0 : ∃ t₀ : ℝ, partialCoeff (jetPolyDeriv (gammaRatioLimit p q u v β) e
      (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) Φ ((σ : ℂ) + (t₀ : ℂ) * Complex.I))) (Fin.last n) ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  have hauto := gamma_rational_autonomous_relation hR hσR hΦ hap e Cf p q u v β hq0 hp0 hCf
    hrelC hmin
  have hrel : ∀ z ∈ verticalStrip σ R, jetPoly (gammaRatioLimit p q u v β) e
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z) = 0 := by
    intro z hz
    have := hauto hz
    simpa [jetPoly] using this
  exact rank_finite_of_nondegenerate_at_point hr hρ hrρ hΦ hap hf hfu hftb hn
    (continuous_jetPoly (gammaRatioLimit p q u v β) e)
    (continuous_jetPolyDeriv (gammaRatioLimit p q u v β) e)
    (fun y => (hasFDerivAt_jetPoly (gammaRatioLimit p q u v β) e y).restrictScalars ℝ)
    hrel hnd0

end GaloisForLFunctions
