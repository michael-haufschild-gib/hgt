import GaloisForLFunctions.HTGeometry.GammaShiftDatum
import GaloisForLFunctions.HTGeometry.GammaFieldAbstractCollapse

/-!
# The finite phase law over a real Gamma-shift field

The collapse of a differential relation needs only two facts about its coefficients: their
normalized ratios converge along the line, and the normalizing coefficient is eventually nonzero.
For coefficients presented by their shifted data both come from the projective boundary of the
shift shapes, so the law applies verbatim to a finite real Gamma-shift field.

This is eq. (19) of the shifted law, from the data of eq. (3).
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Equation (19) of the shifted law.**  A strip almost periodic holomorphic solution of a
differential relation whose coefficients have shifted data has finite rational Bohr frequency
rank. -/
theorem rank_finite_of_gammaShift_data {n N : ℕ} {σ lam R rr ρ : ℝ} (hσ : 0 < σ + lam)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (d α) (ω α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x)) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  obtain ⟨β, r, hrβ, hratio⟩ := exists_dominant_shiftShape_ratio (σ := σ) (lam := lam) hσ hN
    (fun α t => F α ((σ : ℂ) + (t : ℂ) * Complex.I)) d ω b c hc hdat
  have hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    eventually_ne_zero_of_shiftDatum (σ := σ) (lam := lam) (hc β) (hdat β)
  have hdβ : r β ≠ 0 := by
    rw [hrβ]
    exact one_ne_zero
  exact GaloisForLFunctions.rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F r β hratio hFβ
    hrel he hdβ hf hfu hftb

end

end GaloisForLFunctions.HTGeometry
