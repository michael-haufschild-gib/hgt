import GaloisForLFunctions.HTGeometry.GammaFieldRecurrenceCollapse

/-!
# The projective boundary of finite sums

An element of `ℂ(s)[Γ, ψ]` written in monomial expansion is a finite sum of Gamma-field monomials.
Normalized by a monomial dominating every summand, the sum converges to the sum of the individual
limit data, so it is asymptotic to that monomial times a constant; when the constant is nonzero the
sum is eventually nonvanishing and quotients of such sums converge as well.

This is eq. (3) and eq. (5) for coefficients that are finite sums rather than single monomials.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The projective limit of one Gamma-field monomial against another. -/
noncomputable def gammaMonomialLimit (ja : ℕ) (pa qa : Polynomial ℂ) (Da : ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ) : ℂ :=
  if ja = jb ∧ (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
    then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0

/-- Domination of one monomial datum by another, lexicographically in
`(Γ-exponent, degree, digamma exponent)`. -/
def GammaMonomialDominates (ja : ℕ) (pa qa : Polynomial ℂ) (Da : ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ) : Prop :=
  jb < ja ∨ (ja = jb ∧ ((pa * qb).natDegree < (qa * pb).natDegree ∨
    ((pa * qb).natDegree = (qa * pb).natDegree ∧ Da ≤ Db)))

theorem tendsto_monomial_ratio (m : ℕ) {ja : ℕ} {pa qa : Polynomial ℂ} {Da : ℕ}
    {jb : ℕ} {pb qb : Polynomial ℂ} {Db : ℕ}
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa Da jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      gammaFieldElt m ja pa qa Da t / gammaFieldElt m jb pb qb Db t) atTop
      (nhds (gammaMonomialLimit ja pa qa Da jb pb qb Db)) :=
  tendsto_ratio_gammaFieldElt_lex m pa qa pb qb hqa hqb hpb hdom

/-- **Eq. (3) for a finite sum.**  A finite sum of Gamma-field monomials, each dominated by a fixed
monomial, is asymptotic to that monomial times the sum of the limit data. -/
theorem tendsto_sum_ratio_gammaFieldElt {ι : Type*} [Fintype ι] (m : ℕ) (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (D i) jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaFieldElt m (j i) (p i) (q i) (D i) t) / gammaFieldElt m jb pb qb Db t) atTop
      (nhds (∑ i, gammaMonomialLimit (j i) (p i) (q i) (D i) jb pb qb Db)) := by
  classical
  have hterm := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _ => tendsto_monomial_ratio m (hq i) hqb hpb (hdom i))
  refine hterm.congr fun t => ?_
  rw [Finset.sum_div]

/-- A dominated sum with nonzero limit constant is eventually nonvanishing. -/
theorem eventually_sum_gammaFieldElt_ne_zero {ι : Type*} [Fintype ι] (m : ℕ) (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (D : ι → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hpb : pb ≠ 0) (hqb : qb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (D i) jb pb qb Db)
    (hc : (∑ i, gammaMonomialLimit (j i) (p i) (q i) (D i) jb pb qb Db) ≠ 0) :
    ∀ᶠ t : ℝ in atTop, (∑ i, gammaFieldElt m (j i) (p i) (q i) (D i) t) ≠ 0 := by
  have hratio := tendsto_sum_ratio_gammaFieldElt m j p q D jb pb qb Db hq hqb hpb hdom
  filter_upwards [hratio.eventually_ne hc] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-- **Eq. (5) for coefficients that are finite sums.**  When every monomial of every coefficient is
dominated by a fixed monomial and the normalizing coefficient has nonzero limit constant, the
normalized coefficient ratios converge. -/
theorem tendsto_ratio_gammaFieldSum {ι κ : Type*} [Fintype ι] [Fintype κ] (m : ℕ)
    (j : κ → ι → ℕ) (p q : κ → ι → Polynomial ℂ) (D : κ → ι → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (D a i) jb pb qb Db)
    (β : κ)
    (hc : (∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db) ≠ 0) (a : κ) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaFieldElt m (j a i) (p a i) (q a i) (D a i) t)
        / ∑ i, gammaFieldElt m (j β i) (p β i) (q β i) (D β i) t) atTop
      (nhds ((∑ i, gammaMonomialLimit (j a i) (p a i) (q a i) (D a i) jb pb qb Db)
        / ∑ i, gammaMonomialLimit (j β i) (p β i) (q β i) (D β i) jb pb qb Db)) := by
  classical
  have hnum := tendsto_sum_ratio_gammaFieldElt m (j a) (p a) (q a) (D a) jb pb qb Db
    (fun i => hq a i) hqb hpb (fun i => hdom a i)
  have hden := tendsto_sum_ratio_gammaFieldElt m (j β) (p β) (q β) (D β) jb pb qb Db
    (fun i => hq β i) hqb hpb (fun i => hdom β i)
  have hdiv := hnum.div hden hc
  refine hdiv.congr' ?_
  filter_upwards [eventually_gammaFieldElt_ne_zero m jb hpb hqb Db] with t ht
  simp only [Pi.div_apply]
  rcases eq_or_ne (∑ i, gammaFieldElt m (j β i) (p β i) (q β i) (D β i) t) 0 with hB | hB
  · rw [hB]
    simp
  · field_simp

end GaloisForLFunctions
