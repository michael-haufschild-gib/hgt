import GaloisForLFunctions.HTGeometry.GammaFieldFinitePhaseLaw
import GaloisForLFunctions.HTGeometry.GammaJetRatioFamily

/-!
# The finite phase law over the coefficient ratios

The law consumes its coefficient data through three facts only: the normalizing coefficient is
eventually nonzero, the coefficient ratios converge, and the limit at the normalizing index is
nonzero.  Stated that way it is independent of how the coefficients are presented.

Feeding it the Gamma-jet presentation — a datum and a residue for each coefficient — the dominance
is produced by the datum order, so the law applies with no hypothesis chosen by hand.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The law over the coefficient ratios.**  With convergent coefficient ratios, a nonzero limit at
the normalizing index and an eventually nonzero normalizing coefficient, a relation on the strip
collapses to a nontrivial constant-coefficient relation and the frequency rank is finite. -/
theorem finite_phase_law_of_coeff_ratios {n N : ℕ} {σ R rr ρ : ℝ}
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / F β ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) (hdβ : d β ≠ 0)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) :=
  ⟨fun _z hz => strip_relation_of_coeff_limits hR hΦ hap e F d β hcoeff hFβ hrel hz,
    monomialSum_ne_zero d e he β hdβ,
    rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb⟩

/-- **The law from Gamma-jet data.**  Coefficients presented by their Gamma-jet datum and residue
supply the ratios themselves: the datum order produces the normalizing index, the shape ratios give
the limits, and the law applies. -/
theorem finite_phase_law_of_gammaJet_data {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ) (hN : 0 < N)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (u a dP b : Fin N → ℕ) (c : Fin N → ℂ) (hc : ∀ α, c α ≠ 0)
    (hF : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ (u α) (a α) (dP α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  obtain ⟨β, r, hrlim, hrβ⟩ := exists_dominant_with_shape_ratios hσ hN u a dP b
  obtain ⟨hFβ, -, hcoeff⟩ := tendsto_family_ratio_of_normalized
    (F := fun α t => F α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (shape := fun α => gammaJetShape σ (u α) (a α) (dP α) (b α)) (c := c) (r := r)
    β (hc β) (fun α => eventually_gammaJetShape_ne_zero hσ (u α) (a α) (dP α) (b α)) hF hrlim
  have hdβ : c β * r β / c β = 1 := self_ratio_eq_one β (hc β) hrβ
  refine ⟨β, fun α => c α * r α / c β, hdβ, ?_⟩
  exact finite_phase_law_of_coeff_ratios hr hρ hrρ hR hΦ hap e F _ β hcoeff hFβ
    (by rw [hdβ]; exact one_ne_zero) hrel he hf hfu hftb

end GaloisForLFunctions
