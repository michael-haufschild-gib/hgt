import GaloisForLFunctions.HTGeometry.GammaVerticalDominationGeneral
import GaloisForLFunctions.HTGeometry.GammaFieldAbstractCollapse

/-!
# The finite-phase law on an arbitrary vertical line

With `Γ` dominating every polynomial and logarithmic factor on any vertical line of the right half
plane, the projective boundary of the Gamma field and the collapse it feeds are no longer tied to the
half-integer lines.

`gammaEltG σ` is the Gamma-field monomial on the line `Re s = σ`; its ratios converge under the same
lexicographic dominance, and the abstract collapse — itself line-agnostic — turns that into finiteness
of the rational Bohr frequency rank for any `σ > 0`.
-/

open Filter Topology Complex Polynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A Gamma-field monomial on an arbitrary vertical line. -/
noncomputable def gammaEltG (σ : ℝ) (j : ℕ) (p q : Polynomial ℂ) (D : ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
    * (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / q.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
    * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ D

theorem eventually_gamma_ne_zero_general (σ : ℝ) :
    ∀ᶠ t : ℝ in atTop, Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  refine Complex.Gamma_ne_zero fun n => ?_
  intro hcon
  have him : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
  rw [hcon] at him
  simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at him
  linarith [him]

theorem eventually_gammaEltG_ne_zero {σ : ℝ} (hσ : 0 < σ) (j : ℕ) {p q : Polynomial ℂ}
    (hp : p ≠ 0) (hq : q ≠ 0) (D : ℕ) :
    ∀ᶠ t : ℝ in atTop, gammaEltG σ j p q D t ≠ 0 := by
  have hψ : ∀ᶠ t : ℝ in atTop,
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical (le_of_lt hσ)).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_gamma_ne_zero_general σ, eventually_eval_ne_zero σ hp,
    eventually_eval_ne_zero σ hq, hψ] with t hΓ hpt hqt hψt
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hΓ) (div_ne_zero hpt hqt)) (pow_ne_zero _ hψt)

/-- **The Gamma direction on an arbitrary vertical line.** -/
theorem tendsto_ratio_gammaEltG_of_gamma_lt {σ : ℝ} (hσ : 0 < σ) (pa qa pb qb : Polynomial ℂ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {ja jb Da Db : ℕ} (hj : jb < ja) :
    Tendsto (fun t : ℝ => gammaEltG σ ja pa qa Da t / gammaEltG σ jb pb qb Db t)
      atTop (nhds 0) := by
  classical
  have hv : qa * pb ≠ 0 := mul_ne_zero hqa hpb
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ja = jb + c := ⟨ja - jb, by omega⟩
  have hcpos : 0 < c := by omega
  have hF1 := tendsto_gamma_pow_mul_digamma_vertical_general hσ hcpos (pa * qb).natDegree Da
  have hF2 := tendsto_eval_div_pow_natDegree_vertical σ (pa * qb)
  have hF3 := tendsto_ratio_poly_le σ 1 (qa * pb) hv (by simp)
  have hF4 := tendsto_digamma_pow_ratio (le_of_lt hσ) (Da := 0) (Db := Db) (Nat.zero_le Db)
  have hprod := ((hF1.mul hF2).mul hF3).mul hF4
  rw [zero_mul, zero_mul, zero_mul] at hprod
  refine hprod.congr' ?_
  have hψ : ∀ᶠ t : ℝ in atTop,
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical (le_of_lt hσ)).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_vertical_ne_zero σ, eventually_eval_ne_zero σ hqa,
    eventually_eval_ne_zero σ hqb, eventually_eval_ne_zero σ hpb, hψ,
    eventually_gamma_ne_zero_general σ] with t hs hqat hqbt hpbt hψt hΓt
  simp only [gammaEltG, Polynomial.eval_mul, Polynomial.eval_one, pow_zero, hc, pow_add]
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hzdef
  exact (key_ratio_identity (Complex.Gamma z ^ jb) (Complex.Gamma z ^ c)
    (z ^ (pa * qb).natDegree) (Complex.digamma z ^ Da) (Complex.digamma z ^ Db)
    (pa.eval z) (qa.eval z) (pb.eval z) (qb.eval z)
    (pow_ne_zero _ hΓt) (pow_ne_zero _ hs) hqat hqbt hpbt (pow_ne_zero _ hψt)).symm

/-- **Eq. (5) for the Gamma field on an arbitrary vertical line.** -/
theorem tendsto_ratio_gammaEltG_lex {σ : ℝ} (hσ : 0 < σ) (pa qa pb qb : Polynomial ℂ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {ja jb Da Db : ℕ}
    (hlex : jb < ja ∨ (ja = jb ∧ ((pa * qb).natDegree < (qa * pb).natDegree ∨
      ((pa * qb).natDegree = (qa * pb).natDegree ∧ Da ≤ Db)))) :
    Tendsto (fun t : ℝ => gammaEltG σ ja pa qa Da t / gammaEltG σ jb pb qb Db t)
      atTop (nhds (if ja = jb ∧ (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)) := by
  classical
  rcases hlex with hj | ⟨hjeq, hrest⟩
  · rw [if_neg (fun h => absurd h.1 (Nat.ne_of_gt hj))]
    exact tendsto_ratio_gammaEltG_of_gamma_lt hσ pa qa pb qb hqa hqb hpb hj
  · subst hjeq
    have hbase := tendsto_ratio_digammaField_lex (σ := σ) hσ pa qa pb qb hqa hqb hpb
      (Da := Da) (Db := Db) hrest
    have hif : (if ja = ja ∧ (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)
        = (if (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0) := by
      by_cases h : (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
      · rw [if_pos ⟨rfl, h⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.2), if_neg h]
    rw [hif]
    refine hbase.congr' ?_
    filter_upwards [eventually_gamma_ne_zero_general σ] with t hΓt
    have hG : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ ja ≠ 0 := pow_ne_zero _ hΓt
    simp only [gammaEltG]
    rw [mul_assoc, mul_assoc]
    exact (mul_div_mul_left _ _ hG).symm

/-- The limit datum of a family of Gamma-field monomials on an arbitrary line. -/
noncomputable def gammaLimitG {n : ℕ} (j : Fin n → ℕ) (p q : Fin n → Polynomial ℂ)
    (D : Fin n → ℕ) (β : Fin n) : Fin n → ℂ := fun α =>
  if j α = j β ∧ (p α * q β).natDegree = (q α * p β).natDegree ∧ D α = D β
    then (p α * q β).leadingCoeff / (q α * p β).leadingCoeff else 0

/-- **Eq. (9) over the Gamma field on an arbitrary vertical line.** -/
theorem rank_finite_of_gammaEltG_relation {n N : ℕ} {σ R r ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → ℕ) (p q : Fin N → Polynomial ℂ) (D : Fin N → ℕ) (β : Fin N)
    (hp : ∀ α, p α ≠ 0) (hq : ∀ α, q α ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) = gammaEltG σ (j α) (p α) (q α) (D α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (hlex : ∀ α, j β < j α ∨ (j α = j β ∧
      ((p α * q β).natDegree < (q α * p β).natDegree ∨
        ((p α * q β).natDegree = (q α * p β).natDegree ∧ D α ≤ D β))))
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  have hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (gammaLimitG j p q D β α)) := by
    intro α
    have h := tendsto_ratio_gammaEltG_lex hσ (p α) (q α) (p β) (q β) (hq α) (hq β) (hp β)
      (ja := j α) (jb := j β) (Da := D α) (Db := D β) (hlex α)
    refine h.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_gammaEltG_ne_zero hσ (j β) (hp β) (hq β) (D β)] with t ht
    rw [hF β t]
    exact ht
  have hdβ : gammaLimitG j p q D β β ≠ 0 := by
    rw [gammaLimitG, if_pos ⟨rfl, by rw [mul_comm], rfl⟩, mul_comm (p β) (q β)]
    exact fun hzero => (Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero (hq β) (hp β)))
      (by
        have := div_eq_zero_iff.mp hzero
        rcases this with h | h
        · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero (hq β) (hp β)))
        · exact h)
  exact rank_finite_of_coeff_limits hr hρ hrρ hR hΦ hap e F (gammaLimitG j p q D β) β hcoeff hFβ
    hrel he hdβ hf hfu hftb

end GaloisForLFunctions
