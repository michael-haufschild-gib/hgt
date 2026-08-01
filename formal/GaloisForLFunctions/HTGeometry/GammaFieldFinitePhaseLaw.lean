import GaloisForLFunctions.HTGeometry.GammaFieldGeneralLineJets
import GaloisForLFunctions.HTGeometry.ObservableFrequencyRank

/-!
# The finite-phase law over the Gamma field

This file states the law of the card in one place.  A holomorphic function, almost periodic on a
vertical strip of the right half plane, satisfying a differential relation whose coefficients are
elements of `ℂ(s)[Γ, ψ, ψ′, …]` written in monomial expansion:

* satisfies the collapsed *constant-coefficient* relation on the whole strip — it is differentially
  algebraic over `ℂ` (eq. 8);
* has finite rational Bohr frequency rank (eq. 9);
* and so does every observable dominated by it — the divisor clause.

All three come from the same two facts about the coefficients, which the projective boundary of the
Gamma field supplies: their normalized ratios converge along the line, and the normalizing coefficient
is eventually nonzero.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The finite-phase law over the Gamma field.**  A holomorphic, strip almost periodic solution of
a differential relation whose coefficients are elements of `ℂ(s)[Γ, ψ, ψ′, …]` in monomial expansion
is differentially algebraic over the constants — the collapsed relation holds on the whole strip —
and its rational Bohr frequency rank is finite. -/
theorem gammaField_finite_phase_law {n N k r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ)
    (E : Fin N → Fin k → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaJetEltG σ (j α i) (p α i) (q α i) (E α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    (∀ z ∈ verticalStrip σ R, jetPoly
        (fun α : Fin N => (∑ i, gammaJetLimit (j α i) (p α i) (q α i) (E α i) jb pb qb Db)
          / ∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) e
        (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  set d : Fin N → ℂ := fun α =>
    (∑ i, gammaJetLimit (j α i) (p α i) (q α i) (E α i) jb pb qb Db)
      / ∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db with hd
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (d α)) := by
    intro α
    have h := tendsto_ratio_gammaJetEltG_sum hσ j p q E jb pb qb Db hq hqb hpb hdom β hc α
    refine h.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_sum_gammaJetEltG_ne_zero hσ (j β) (p β) (q β) (E β) jb pb qb Db
      (fun i => hq β i) hqb hpb (fun i => hdom β i) hc] with t ht
    rw [hF β t]
    exact ht
  have hdβ : d β ≠ 0 := by
    rw [hd]
    simp only
    rw [div_self hc]
    exact one_ne_zero
  refine ⟨fun z hz => strip_relation_of_coeff_limits hR hΦ hap e F d β hcoeff hFβ hrel hz, ?_⟩
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb

/-- **The divisor clause of the law.**  Every observable dominated by such a solution has finite
rational Bohr frequency rank as well. -/
theorem gammaField_finite_phase_law_observable {n N k r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ)
    (E : Fin N → Fin k → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaJetEltG σ (j α i) (p α i) (q α i) (E α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {g : ℝ →ᵇ ℂ} (hgdom : IsDominatedObservable f g) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies g) ≤ (K : Cardinal) := by
  obtain ⟨K, hK⟩ := (gammaField_finite_phase_law hσ hr hρ hrρ hR hΦ hap e F j p q E jb pb qb Db
    hq hqb hpb hdom β hc hF hrel he hf hfu hftb).2
  exact ⟨K, le_trans (rank_le_of_dominated hgdom) hK⟩

end GaloisForLFunctions
