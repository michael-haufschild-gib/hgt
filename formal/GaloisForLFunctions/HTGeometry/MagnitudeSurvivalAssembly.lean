import GaloisForLFunctions.HTGeometry.MagnitudeDistinctSurvival
import GaloisForLFunctions.HTGeometry.FiberPermanentIdentity

/-!
# Magnitude survival assembly

Combines the complex regrouping, the complex minimal-valuation domination, and the singleton-fiber
weight nonvanishing into a usable survival lemma: if the coefficient `coeff N` of a differential
polynomial applied to `f` has a **single-fiber minimal-valuation atom** `ν₀` (realized by one
`(μ,l)`-pair with nonzero polynomial coefficient) whose valuation gap `G` to every competitor
exceeds the log of the total-weight-to-dominant-weight ratio, then that coefficient is nonzero.
This is the general-HT survival step; the superlacunar magnitude profile supplies the gap.
-/

open Finset PowerSeries

namespace GaloisForLFunctions

/-- **Singleton-min complex survival.**  A single-fiber minimal-valuation atom with nonzero
coefficient and dominating gap forces `coeff N ≠ 0`. -/
theorem diffPoly_coeff_ne_zero_of_singleton_min_complex {D : ℕ} (f : ℂ⟦X⟧) (N : ℕ)
    (S : Finset (Fin D → ℕ)) (c : (Fin D → ℕ) → ℂ) {b : ℕ → ℝ}
    (hb : ∀ n, ‖coeff n f‖ = Real.exp (- b n))
    (ν₀ : ℕ →₀ ℕ) (p₀ : (Fin D → ℕ) × (Fin D →₀ ℕ))
    (hfiber : (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀) = {p₀})
    (hc : c p₀.1 ≠ 0)
    (hν₀ : ν₀ ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).image
      (fun p => key (fun t => p.2 t + p.1 t)))
    {G : ℝ}
    (hgap : ∀ ν ∈ ((S ×ˢ (Finset.univ.finsuppAntidiag N)).image
          (fun p => key (fun t => p.2 t + p.1 t))).erase ν₀,
        ν₀.sum (fun n k => (k : ℝ) * b n) + G ≤ ν.sum (fun n k => (k : ℝ) * b n))
    (hG : (∑ ν ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).image
          (fun p => key (fun t => p.2 t + p.1 t)),
        ‖(∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
              (fun p => key (fun t => p.2 t + p.1 t) = ν),
            c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))‖)
        < ‖(∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
              (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
            c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))‖ * Real.exp G) :
    (coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 :=
  diffPoly_coeff_ne_zero_of_dominant_complex f N S c hb
    (fun ν => ∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
          (fun p => key (fun t => p.2 t + p.1 t) = ν),
        c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))
    (fun _ => rfl) ν₀ hν₀ (weight_singleton_ne_zero_complex N S c ν₀ p₀ hfiber hc) hgap hG

/-- **Single-order-min complex survival.**  A minimal-valuation atom whose fiber lies over a
single derivative-order `μ₀` (with `c μ₀ ≠ 0`) and dominating gap forces `coeff N ≠ 0`. -/
theorem diffPoly_coeff_ne_zero_of_single_mu_min_complex {D : ℕ} (f : ℂ⟦X⟧) (N : ℕ)
    (S : Finset (Fin D → ℕ)) (c : (Fin D → ℕ) → ℂ) {b : ℕ → ℝ}
    (hb : ∀ n, ‖coeff n f‖ = Real.exp (- b n))
    (ν₀ : ℕ →₀ ℕ) (μ₀ : Fin D → ℕ)
    (hsingle : ∀ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀), p.1 = μ₀)
    (hne : ((S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀)).Nonempty)
    (hc : c μ₀ ≠ 0)
    (hν₀ : ν₀ ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).image
      (fun p => key (fun t => p.2 t + p.1 t)))
    {G : ℝ}
    (hgap : ∀ ν ∈ ((S ×ˢ (Finset.univ.finsuppAntidiag N)).image
          (fun p => key (fun t => p.2 t + p.1 t))).erase ν₀,
        ν₀.sum (fun n k => (k : ℝ) * b n) + G ≤ ν.sum (fun n k => (k : ℝ) * b n))
    (hG : (∑ ν ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).image
          (fun p => key (fun t => p.2 t + p.1 t)),
        ‖(∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
              (fun p => key (fun t => p.2 t + p.1 t) = ν),
            c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))‖)
        < ‖(∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
              (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
            c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))‖ * Real.exp G) :
    (coeff N) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 :=
  diffPoly_coeff_ne_zero_of_dominant_complex f N S c hb
    (fun ν => ∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
          (fun p => key (fun t => p.2 t + p.1 t) = ν),
        c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))
    (fun _ => rfl) ν₀ hν₀
    (weight_single_mu_ne_zero_complex N S c ν₀ μ₀ hsingle hne hc) hgap hG

end GaloisForLFunctions
