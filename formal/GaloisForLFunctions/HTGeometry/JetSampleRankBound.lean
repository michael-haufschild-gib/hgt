import GaloisForLFunctions.HTGeometry.CircleJetSample
import GaloisForLFunctions.HTGeometry.StripLineCarrierEquiv

/-!
# The frequency rank bound from a jet relation

Assembling the route: the contour jet sample is continuous and, where the separant does not vanish,
injective on the carrier of the strip translate curve; that carrier is uniformly equivalent to the
carrier of the line restriction; and a continuous injective jet sample into `ℂ^N` bounds the rational
rank of the frequency group by `2N`.
-/

open Filter Topology Metric Set Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Finite frequency rank from a jet relation with non-vanishing separant.** -/
theorem rank_le_of_separant_jet_relation {σ R r r' : ℝ} (hr0 : 0 < r) (hrr' : r < r')
    (hr'R : r' < R) (hRpos : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    [MeasurableSpace (BohrHull (verticalRestriction F hRpos hF hap))]
    [BorelSpace (BohrHull (verticalRestriction F hRpos hF hap))]
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {n : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) P = 0)
    (t₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ θ : ℝ, circleMap ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ θ ∈ closedStrip σ r)
    (hdisc : Metric.closedBall ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ ⊆ verticalStrip σ r)
    (hsep : ∀ (x : BohrHull Gb) (g : ℂ → ℂ), DifferentiableOn ℂ g (verticalStrip σ r) →
      (∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z) →
      deriv (fun u : ℂ => MvPolynomial.eval
          (Fin.snoc (jetVec (n := n) (lineFun σ g) t₀) u)
          (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P))
        (iteratedDeriv n (lineFun σ g) t₀) ≠ 0) :
    Module.rank ℤ (bohrHullFrequencies (verticalRestriction F hRpos hF hap))
      ≤ ((2 * (n + 1) : ℕ) : Cardinal) := by
  have hr : r < R := lt_trans hrr' hr'R
  have hf : ∀ t : ℝ, (verticalRestriction F hRpos hF hap) t
      = F ((σ : ℂ) + (t : ℂ) * Complex.I) := verticalRestriction_apply F hRpos hF hap
  set e := stripLineHullEquiv (le_of_lt hr0) hrr' hr'R hF hap hf hGb with he
  refine rank_frequencies_le_of_vertical hRpos hF hap
    (J := fun y => fun k : Fin (n + 1) =>
      circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) ρ hball (k : ℕ) (bohrEval Gb (e y))) ?_ ?_
  · refine continuous_pi fun k => ?_
    obtain ⟨C, hC⟩ := lipschitzWith_circleJetSample ((σ : ℂ) + (t₀ : ℂ) * Complex.I) hρ hball (k : ℕ)
    exact hC.continuous.comp
      (UniformSpace.Completion.continuous_extension.comp e.continuous)
  · intro y₁ y₂ hy
    refine e.injective ?_
    exact hull_injective_of_circleJetSample hr0 hr hF hn P hrel hGb t₀ hρ hball hdisc hsep hy

end GaloisForLFunctions
