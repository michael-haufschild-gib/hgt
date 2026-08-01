import GaloisForLFunctions.HTGeometry.GammaFieldGeneralLine
import GaloisForLFunctions.HTGeometry.GammaFieldNoCancellation

/-!
# Finite sums on an arbitrary vertical line

The limit datum of a pair of Gamma-field monomials and the lexicographic order on it do not depend on
the line, so the sum and quotient results carry over verbatim once the monomial ratio is available on
a general line.

Combined with the line-agnostic collapse and the fact that distinct exponent pairs force the limit
constant to be `1`, the finite-phase law holds on every vertical line of the right half plane for
coefficients that are finite sums of Gamma-field monomials in normal form.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The monomial ratio on an arbitrary vertical line. -/
theorem tendsto_monomial_ratioG {σ : ℝ} (hσ : 0 < σ) {ja : ℕ} {pa qa : Polynomial ℂ} {Da : ℕ}
    {jb : ℕ} {pb qb : Polynomial ℂ} {Db : ℕ}
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa Da jb pb qb Db) :
    Tendsto (fun t : ℝ => gammaEltG σ ja pa qa Da t / gammaEltG σ jb pb qb Db t) atTop
      (nhds (gammaMonomialLimit ja pa qa Da jb pb qb Db)) :=
  tendsto_ratio_gammaEltG_lex hσ pa qa pb qb hqa hqb hpb hdom

/-- **Eq. (3) for a finite sum on an arbitrary vertical line.** -/
theorem tendsto_sum_ratio_gammaEltG {ι : Type*} [Fintype ι] {σ : ℝ} (hσ : 0 < σ) (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (D i) jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaEltG σ (j i) (p i) (q i) (D i) t) / gammaEltG σ jb pb qb Db t) atTop
      (nhds (∑ i, gammaMonomialLimit (j i) (p i) (q i) (D i) jb pb qb Db)) := by
  classical
  have hterm := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _ => tendsto_monomial_ratioG hσ (hq i) hqb hpb (hdom i))
  refine hterm.congr fun t => ?_
  rw [Finset.sum_div]

/-- A dominated sum with nonzero limit constant is eventually nonvanishing. -/
theorem eventually_sum_gammaEltG_ne_zero {ι : Type*} [Fintype ι] {σ : ℝ} (hσ : 0 < σ) (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (D i) jb pb qb Db)
    (hc : (∑ i, gammaMonomialLimit (j i) (p i) (q i) (D i) jb pb qb Db) ≠ 0) :
    ∀ᶠ t : ℝ in atTop, (∑ i, gammaEltG σ (j i) (p i) (q i) (D i) t) ≠ 0 := by
  have hratio := tendsto_sum_ratio_gammaEltG hσ j p q D jb pb qb Db hq hqb hpb hdom
  filter_upwards [hratio.eventually_ne hc] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-- **Eq. (5) for coefficients that are finite sums, on an arbitrary vertical line.** -/
theorem tendsto_ratio_gammaEltG_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {σ : ℝ} (hσ : 0 < σ)
    (j : κ → ι → ℕ) (p q : κ → ι → Polynomial ℂ) (D : κ → ι → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (D a i) jb pb qb Db) (β : κ)
    (hc : (∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db) ≠ 0) (a : κ) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaEltG σ (j a i) (p a i) (q a i) (D a i) t)
        / ∑ i, gammaEltG σ (j β i) (p β i) (q β i) (D β i) t) atTop
      (nhds ((∑ i, gammaMonomialLimit (j a i) (p a i) (q a i) (D a i) jb pb qb Db)
        / ∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db)) := by
  classical
  have hnum := tendsto_sum_ratio_gammaEltG hσ (j a) (p a) (q a) (D a) jb pb qb Db
    (fun i => hq a i) hqb hpb (fun i => hdom a i)
  have hden := tendsto_sum_ratio_gammaEltG hσ (j β) (p β) (q β) (D β) jb pb qb Db
    (fun i => hq β i) hqb hpb (fun i => hdom β i)
  have hdiv := hnum.div hden hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_gammaEltG_ne_zero hσ jb hpb hqb Db] with t ht
  simp only [Pi.div_apply]
  rcases eq_or_ne (∑ i, gammaEltG σ (j β i) (p β i) (q β i) (D β i) t) 0 with hB | hB
  · rw [hB]
    simp
  · field_simp

/-- **Eq. (9) on an arbitrary vertical line, for coefficients that are finite sums with distinct
exponent pairs.** -/
theorem rank_finite_of_gammaEltG_sum_distinct {n N k : ℕ} {σ R r ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ) (D : Fin N → Fin k → ℕ)
    (hp : ∀ a i, p a i ≠ 0) (hq : ∀ a i, q a i ≠ 0) (β : Fin N) (i₀ : Fin k)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (D a i)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀))
    (hdist : ∀ i, i ≠ i₀ → (j β i, D β i) ≠ (j β i₀, D β i₀))
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaEltG σ (j α i) (p α i) (q α i) (D α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hc : (∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀)) ≠ 0 := by
    rw [sum_gammaMonomialLimit_eq_one (j β) (p β) (q β) (D β) i₀ (hp β i₀) (hq β i₀) hdist]
    exact one_ne_zero
  set d : Fin N → ℂ := fun α =>
    (∑ i, gammaMonomialLimit (j α i) (p α i) (q α i) (D α i)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀))
      / ∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i)
        (j β i₀) (p β i₀) (q β i₀) (D β i₀) with hd
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (d α)) := by
    intro α
    have h := tendsto_ratio_gammaEltG_sum hσ j p q D (j β i₀) (p β i₀) (q β i₀) (D β i₀)
      hq (hq β i₀) (hp β i₀) hdom β hc α
    refine h.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_sum_gammaEltG_ne_zero hσ (j β) (p β) (q β) (D β)
      (j β i₀) (p β i₀) (q β i₀) (D β i₀) (fun i => hq β i) (hq β i₀) (hp β i₀)
      (fun i => hdom β i) hc] with t ht
    rw [hF β t]
    exact ht
  have hdβ : d β ≠ 0 := by
    rw [hd]
    simp only
    rw [div_self hc]
    exact one_ne_zero
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb

end GaloisForLFunctions
