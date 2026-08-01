import GaloisForLFunctions.HTGeometry.GammaFieldJetBoundary
import GaloisForLFunctions.HTGeometry.GammaFieldAbstractCollapse

/-!
# The finite-phase law for full-tower coefficients

Coefficients that are finite sums of monomials `Γ^j·(p/q)·∏(ψ⁽ⁱ⁾)^{E i}` — that is, arbitrary
elements of `ℂ(s)[Γ, ψ, ψ′, …]` in monomial expansion — have convergent normalized ratios and are
eventually nonvanishing whenever their limit constant is nonzero.

Those are exactly the two facts the abstract collapse consumes, so the finite-phase law applies: a
strip almost periodic holomorphic solution of a differential relation with such coefficients has
finite rational Bohr frequency rank.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The projective limit of a full-tower monomial against a pure one. -/
noncomputable def gammaJetLimit {r : ℕ} (ja : ℕ) (pa qa : Polynomial ℂ) (Ea : Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ) : ℂ :=
  gammaMonomialLimit ja pa qa (Ea 0) jb pb qb Db * ∏ k : Fin r, (0 : ℂ) ^ (Ea k.succ)

theorem tendsto_sum_ratio_gammaFieldJet' {ι : Type*} [Fintype ι] (m : ℕ) {r : ℕ} (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (E : ι → Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (E i 0) jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaFieldJetElt m (j i) (p i) (q i) (E i) t) / gammaFieldElt m jb pb qb Db t) atTop
      (nhds (∑ i, gammaJetLimit (j i) (p i) (q i) (E i) jb pb qb Db)) :=
  tendsto_sum_ratio_gammaFieldJet m j p q E jb pb qb Db hq hqb hpb hdom

/-- A dominated sum of full-tower monomials with nonzero limit constant is eventually nonvanishing. -/
theorem eventually_sum_gammaFieldJetElt_ne_zero {ι : Type*} [Fintype ι] (m : ℕ) {r : ℕ} (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (E : ι → Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (E i 0) jb pb qb Db)
    (hc : (∑ i, gammaJetLimit (j i) (p i) (q i) (E i) jb pb qb Db) ≠ 0) :
    ∀ᶠ t : ℝ in atTop, (∑ i, gammaFieldJetElt m (j i) (p i) (q i) (E i) t) ≠ 0 := by
  have hratio := tendsto_sum_ratio_gammaFieldJet' m j p q E jb pb qb Db hq hqb hpb hdom
  filter_upwards [hratio.eventually_ne hc] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-- **Eq. (5) for coefficients that are finite sums of full-tower monomials.** -/
theorem tendsto_ratio_gammaFieldJetSum {ι κ : Type*} [Fintype ι] [Fintype κ] (m : ℕ) {r : ℕ}
    (j : κ → ι → ℕ) (p q : κ → ι → Polynomial ℂ) (E : κ → ι → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db) (β : κ)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0) (a : κ) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaFieldJetElt m (j a i) (p a i) (q a i) (E a i) t)
        / ∑ i, gammaFieldJetElt m (j β i) (p β i) (q β i) (E β i) t) atTop
      (nhds ((∑ i, gammaJetLimit (j a i) (p a i) (q a i) (E a i) jb pb qb Db)
        / ∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db)) := by
  classical
  have hnum := tendsto_sum_ratio_gammaFieldJet' m (j a) (p a) (q a) (E a) jb pb qb Db
    (fun i => hq a i) hqb hpb (fun i => hdom a i)
  have hden := tendsto_sum_ratio_gammaFieldJet' m (j β) (p β) (q β) (E β) jb pb qb Db
    (fun i => hq β i) hqb hpb (fun i => hdom β i)
  have hdiv := hnum.div hden hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_gammaFieldElt_ne_zero m jb hpb hqb Db] with t ht
  simp only [Pi.div_apply]
  rcases eq_or_ne (∑ i, gammaFieldJetElt m (j β i) (p β i) (q β i) (E β i) t) 0 with hB | hB
  · rw [hB]
    simp
  · field_simp

/-- **Eq. (9) for coefficients that are finite sums of full-tower Gamma-field monomials.** -/
theorem rank_finite_of_gammaFieldJetSum_relation {n N k m r : ℕ} {Φ : ℂ → ℂ} {R rr ρ : ℝ}
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip (1 / 2 + m) R))
    (hap : IsStripAlmostPeriodic Φ (1 / 2 + m) R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ)
    (E : Fin N → Fin k → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaFieldJetElt m (j α i) (p α i) (q α i) (E α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ (((1 / 2 + m : ℝ) : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  set d : Fin N → ℂ := fun α =>
    (∑ i, gammaJetLimit (j α i) (p α i) (q α i) (E α i) jb pb qb Db)
      / ∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db with hd
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)) := by
    intro α
    have h := tendsto_ratio_gammaFieldJetSum m j p q E jb pb qb Db hq hqb hpb hdom β hc α
    refine h.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop,
      F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_sum_gammaFieldJetElt_ne_zero m (j β) (p β) (q β) (E β) jb pb qb Db
      (fun i => hq β i) hqb hpb (fun i => hdom β i) hc] with t ht
    rw [hF β t]
    exact ht
  have hdβ : d β ≠ 0 := by
    rw [hd]
    simp only
    rw [div_self hc]
    exact one_ne_zero
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb

end GaloisForLFunctions
