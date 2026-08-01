import GaloisForLFunctions.HTGeometry.GammaFieldGeneralLineSums
import GaloisForLFunctions.HTGeometry.DigammaFieldValuation
import GaloisForLFunctions.HTGeometry.GammaFieldJetCollapse

/-!
# The finite-phase law in full generality

A general monomial of the Gamma field is `Γ^j · (p/q) · ∏ (ψ⁽ⁱ⁾)^{E i}`.  Splitting off the
order-zero jet factor writes it as a pure monomial times a product of positive-order polygammas, and
those vanish on every vertical line, so the boundary datum is that of the pure part and a monomial
carrying a derivative factor is negligible.

Sums of such monomials therefore have convergent normalized ratios and are eventually nonvanishing,
which is all the line-agnostic collapse consumes.  The result is eq. (9) in the generality of the
card: an arbitrary vertical line of the right half plane, and coefficients that are arbitrary elements
of `ℂ(s)[Γ, ψ, ψ′, …]` in monomial expansion.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A full-tower Gamma-field monomial on an arbitrary vertical line. -/
noncomputable def gammaJetEltG (σ : ℝ) (j : ℕ) (p q : Polynomial ℂ) {r : ℕ}
    (E : Fin (r + 1) → ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
    * (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / q.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
    * ∏ i : Fin (r + 1), (digammaJetLine σ (i : ℕ) t) ^ (E i)

theorem gammaJetEltG_eq (σ : ℝ) (j : ℕ) (p q : Polynomial ℂ) {r : ℕ} (E : Fin (r + 1) → ℕ)
    (t : ℝ) :
    gammaJetEltG σ j p q E t
      = gammaEltG σ j p q (E 0) t
        * ∏ i : Fin r, (digammaJetLine σ ((i.succ : Fin (r + 1)) : ℕ) t) ^ (E i.succ) := by
  rw [gammaJetEltG, gammaEltG, Fin.prod_univ_succ]
  have h0 : digammaJetLine σ ((0 : Fin (r + 1)) : ℕ) t
      = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [digammaJetLine, Fin.val_zero, iteratedDeriv_zero]
  rw [h0]
  ring

/-- **Eq. (5) for full-tower monomials on an arbitrary vertical line.** -/
theorem tendsto_ratio_gammaJetEltG {σ : ℝ} (hσ : 0 < σ) {r : ℕ} (ja : ℕ) (pa qa : Polynomial ℂ)
    (Ea : Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa (Ea 0) jb pb qb Db) :
    Tendsto (fun t : ℝ => gammaJetEltG σ ja pa qa Ea t / gammaEltG σ jb pb qb Db t)
      atTop (nhds (gammaMonomialLimit ja pa qa (Ea 0) jb pb qb Db
        * ∏ i : Fin r, (0 : ℂ) ^ (Ea i.succ))) := by
  have hmono := tendsto_monomial_ratioG hσ (ja := ja) (pa := pa) (qa := qa) (Da := Ea 0)
    (jb := jb) (pb := pb) (qb := qb) (Db := Db) hqa hqb hpb hdom
  have htail := tendsto_tail_prod (σ := σ) hσ Ea
  have hprod := hmono.mul htail
  refine hprod.congr fun t => ?_
  rw [gammaJetEltG_eq]
  ring

/-- **Eq. (3) for a finite sum of full-tower monomials on an arbitrary vertical line.** -/
theorem tendsto_sum_ratio_gammaJetEltG {ι : Type*} [Fintype ι] {σ : ℝ} (hσ : 0 < σ) {r : ℕ}
    (j : ι → ℕ) (p q : ι → Polynomial ℂ) (E : ι → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (E i 0) jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaJetEltG σ (j i) (p i) (q i) (E i) t) / gammaEltG σ jb pb qb Db t) atTop
      (nhds (∑ i, gammaMonomialLimit (j i) (p i) (q i) (E i 0) jb pb qb Db
        * ∏ k : Fin r, (0 : ℂ) ^ (E i k.succ))) := by
  classical
  have hterm := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _ => tendsto_ratio_gammaJetEltG hσ (j i) (p i) (q i) (E i) jb pb qb Db
      (hq i) hqb hpb (hdom i))
  refine hterm.congr fun t => ?_
  rw [Finset.sum_div]

theorem eventually_sum_gammaJetEltG_ne_zero {ι : Type*} [Fintype ι] {σ : ℝ} (hσ : 0 < σ) {r : ℕ}
    (j : ι → ℕ) (p q : ι → Polynomial ℂ) (E : ι → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (E i 0) jb pb qb Db)
    (hc : (∑ i, gammaJetLimit (j i) (p i) (q i) (E i) jb pb qb Db) ≠ 0) :
    ∀ᶠ t : ℝ in atTop, (∑ i, gammaJetEltG σ (j i) (p i) (q i) (E i) t) ≠ 0 := by
  have hratio := tendsto_sum_ratio_gammaJetEltG hσ j p q E jb pb qb Db hq hqb hpb hdom
  filter_upwards [hratio.eventually_ne hc] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-- **Eq. (5) for full-tower sums on an arbitrary vertical line.** -/
theorem tendsto_ratio_gammaJetEltG_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {σ : ℝ} (hσ : 0 < σ)
    {r : ℕ} (j : κ → ι → ℕ) (p q : κ → ι → Polynomial ℂ) (E : κ → ι → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db) (β : κ)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0) (a : κ) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaJetEltG σ (j a i) (p a i) (q a i) (E a i) t)
        / ∑ i, gammaJetEltG σ (j β i) (p β i) (q β i) (E β i) t) atTop
      (nhds ((∑ i, gammaJetLimit (j a i) (p a i) (q a i) (E a i) jb pb qb Db)
        / ∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db)) := by
  classical
  have hnum := tendsto_sum_ratio_gammaJetEltG hσ (j a) (p a) (q a) (E a) jb pb qb Db
    (fun i => hq a i) hqb hpb (fun i => hdom a i)
  have hden := tendsto_sum_ratio_gammaJetEltG hσ (j β) (p β) (q β) (E β) jb pb qb Db
    (fun i => hq β i) hqb hpb (fun i => hdom β i)
  have hdiv := hnum.div hden hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_gammaEltG_ne_zero hσ jb hpb hqb Db] with t ht
  simp only [Pi.div_apply]
  rcases eq_or_ne (∑ i, gammaJetEltG σ (j β i) (p β i) (q β i) (E β i) t) 0 with hB | hB
  · rw [hB]
    simp
  · field_simp

/-- **Eq. (9) in full generality: an arbitrary vertical line, coefficients arbitrary elements of
`ℂ(s)[Γ, ψ, ψ′, …]` in monomial expansion.** -/
theorem rank_finite_of_gammaJetEltG_sum_relation {n N k r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
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
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
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
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ hf hfu hftb

end GaloisForLFunctions
