import GaloisForLFunctions.HTGeometry.GammaFieldDominantIndex
import GaloisForLFunctions.HTGeometry.GammaFieldJetCollapse

/-!
# No cancellation at the dominant datum

Two monomials contribute to the same limit constant only when their `Γ`-exponents and digamma
exponents agree.  So if the monomials of the normalizing coefficient carry pairwise distinct
`(Γ-exponent, digamma exponent)` pairs, only the normalizing monomial itself contributes and the
limit constant is exactly `1`.

That discharges the last numerical hypothesis of the finite-phase law: with distinct exponent pairs —
the normal form obtained by collecting monomials with equal exponents — no assumption on the
coefficients is left beyond their monomial expansion.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **No cancellation when the exponent pairs are distinct.**  If the `(Γ-exponent, digamma
exponent)` pairs of a family are pairwise distinct, then only the normalizing member contributes to
the limit constant, which is therefore `1`. -/
theorem sum_gammaMonomialLimit_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (β : ι) (hp : p β ≠ 0) (hq : q β ≠ 0)
    (hdist : ∀ i, i ≠ β → (j i, D i) ≠ (j β, D β)) :
    (∑ i, gammaMonomialLimit (j i) (p i) (q i) (D i) (j β) (p β) (q β) (D β)) = 1 := by
  classical
  rw [Finset.sum_eq_single β]
  · rw [gammaMonomialLimit, if_pos ⟨rfl, by rw [mul_comm], rfl⟩, mul_comm (p β) (q β)]
    exact div_self (Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hq hp))
  · intro i _ hi
    rw [gammaMonomialLimit, if_neg]
    rintro ⟨hj, -, hD⟩
    exact hdist i hi (by rw [hj, hD])
  · intro h
    exact absurd (Finset.mem_univ β) h

/-- **Eq. (9) with the non-cancellation hypothesis discharged.**  If the monomials of the
normalizing coefficient have pairwise distinct `(Γ-exponent, digamma exponent)` pairs, its limit
constant is `1`, so the finite-phase law applies with no numerical hypothesis at all. -/
theorem rank_finite_of_gammaFieldSum_distinct {n N k m : ℕ} {Φ : ℂ → ℂ} {R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ) (D : Fin N → Fin k → ℕ)
    (hp : ∀ a i, p a i ≠ 0) (hq : ∀ a i, q a i ≠ 0)
    (β : Fin N) (i₀ : Fin k)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (D a i)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀))
    (hdist : ∀ i, i ≠ i₀ → (j β i, D β i) ≠ (j β i₀, D β i₀))
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaFieldElt m (j α i) (p α i) (q α i) (D α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ (((1 / 2 + m : ℝ) : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hc : (∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀)) ≠ 0 := by
    rw [sum_gammaMonomialLimit_eq_one (j β) (p β) (q β) (D β) i₀ (hp β i₀) (hq β i₀) hdist]
    exact one_ne_zero
  exact rank_finite_of_gammaFieldSum_relation hr hρ hrρ hR hΦ hap e F j p q D
    (j β i₀) (p β i₀) (q β i₀) (D β i₀) hq (hq β i₀) (hp β i₀) hdom β hc hF hrel he hf hfu hftb

end GaloisForLFunctions
