import GaloisForLFunctions.HTGeometry.JetSampleRankBound
import GaloisForLFunctions.HTGeometry.GammaFieldRationalPhaseRank

/-!
# The explicit jet bound in frequency-module form

The jet-embedding bound says the frequency group of a strip-almost-periodic solution of a polynomial
jet relation with nonvanishing separant has `ℤ`-rank at most `2(n+1)`: the contour jet sample embeds
the carrier in `ℂ^{n+1}`.  Through the module theorem and the rational-rank bridge that becomes a
bound on the number of rationally independent frequencies of the Bohr–Fourier expansion of the line
restriction itself — eq. (7)/(9) in the units the card states it in, with the Borel structure on the
hull chosen inside the proof rather than assumed.
-/

open Filter Set Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The explicit rational phase-rank bound from a jet relation with nonvanishing separant.** -/
theorem rank_bohrFrequencyModule_le_of_separant_jet_relation {σ R r r' : ℝ} (hr0 : 0 < r)
    (hrr' : r < r') (hr'R : r' < R) (hRpos : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
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
    Module.rank ℚ (bohrFrequencyModule fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I))
      ≤ ((2 * (n + 1) : ℕ) : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := verticalRestriction F hRpos hF hap with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hZ : Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (n + 1) : ℕ) : Cardinal) :=
    rank_le_of_separant_jet_relation hr0 hrr' hr'R hRpos hF hap hGb hn P hrel t₀ hρ hball hdisc hsep
  have hfval : ∀ t : ℝ, f t = F ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    verticalRestriction_apply F hRpos hF hap
  have hfun : (fun t : ℝ => (f t : ℂ)) = fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    funext hfval
  have hcont : Continuous fun t : ℝ => (f t : ℂ) := f.continuous
  have hapline : _root_.HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => (f t : ℂ) := by
    rw [hfun]
    exact isBohrAlmostPeriodic_line hRpos hap
  have hfu : UniformContinuous fun t : ℝ => (f t : ℂ) :=
    uniformContinuous_of_isBohrAlmostPeriodic hcont hapline
  have hftb : HasTotallyBoundedOrbit fun t : ℝ => (f t : ℂ) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapline
  have hQ := rank_bohrFrequencyModule_le_of_hull_rank_le hfu hftb hZ
  rw [hfun] at hQ
  exact hQ

end GaloisForLFunctions.HTGeometry
