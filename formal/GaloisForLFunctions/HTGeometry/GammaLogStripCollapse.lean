import GaloisForLFunctions.HTGeometry.GammaLogValuationBoundary
import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull

/-!
# Unconditional finite-phase collapse against the algebraic-logarithmic Gamma scale

The coefficients `s^a (log s)^b · P(Γ)/Q(Γ)` are exactly the monomials of the Gamma field in the
grading `(k, a, b)` of eq. (26), with `k` the Gamma valuation.  Combining the ordering theorems with
the Bohr hull of the strip gives an instance of eq. (8) in which **nothing remains hypothetical**:
if a holomorphic vertically almost-periodic `f` satisfies a finite differential relation whose
coefficients are such monomials and one of them strictly dominates all the others, then the
differential monomial attached to the dominant coefficient vanishes identically on the strip.

The dominance relation `StrictlySubordinateAt` is the lexicographic order of eq. (26): a strictly
larger Gamma valuation, or — at equal Gamma valuation — a strictly smaller algebraic-logarithmic
monomial.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-! ### Transfer from the vertical line to a return sequence -/

theorem tendsto_vertical_along_returns {F : ℂ → ℂ} {L : ℂ} {z₀ : ℂ}
    (h : Tendsto (fun t : ℝ => F ((z₀.re : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds L))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun l => F (z₀ + (T l : ℂ) * Complex.I)) atTop (nhds L) := by
  have hshift : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hT
  refine (h.comp hshift).congr (fun l => ?_)
  simp only [Function.comp_apply]
  rw [add_mul_I_eq_ofReal_re_add z₀ (T l)]

theorem eventually_vertical_along_returns {p : ℂ → Prop} {z₀ : ℂ}
    (h : ∀ᶠ t : ℝ in atTop, p ((z₀.re : ℂ) + (t : ℂ) * Complex.I))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    ∀ᶠ l in atTop, p (z₀ + (T l : ℂ) * Complex.I) := by
  have hshift : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hT
  filter_upwards [hshift.eventually h] with l hl
  rw [add_mul_I_eq_ofReal_re_add z₀ (T l)]
  exact hl

/-! ### Nonvanishing of an algebraic-logarithmic Gamma monomial -/

theorem gammaRationalDatum_fn_eventually_ne_zero (D : GammaRationalDatum) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ t : ℝ in atTop, D.fn ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hg := Gamma_vertical_tendsto_nhdsWithin_zero hσ
  have hg0 : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := Gamma_vertical_tendsto_zero hσ
  have hnum := (((Polynomial.continuous D.numUnit).tendsto 0).comp hg0).eventually
    (isOpen_ne.mem_nhds D.numUnit_ne)
  have hden := (((Polynomial.continuous D.denUnit).tendsto 0).comp hg0).eventually
    (isOpen_ne.mem_nhds D.denUnit_ne)
  filter_upwards [hg.eventually self_mem_nhdsWithin, hnum, hden] with t hgt hn hd
  have hgne : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by simpa using hgt
  have hnum' : D.num.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
    simp only [GammaRationalDatum.num, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ hgne) hn
  have hden' : D.den.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
    simp only [GammaRationalDatum.den, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ hgne) hd
  exact div_ne_zero hnum' hden'

theorem logFn_eventually_ne_zero (D : GammaRationalDatum) (a b : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ t : ℝ in atTop, D.logFn a b ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hlogtop := tendsto_norm_log_vertical_atTop hσ.le
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlogtop.eventually_ge_atTop 1,
    gammaRationalDatum_fn_eventually_ne_zero D hσ] with t ht hlog1 hfn
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  have hlogne : Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlog1
    linarith
  simp only [GammaRationalDatum.logFn]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hsne) (pow_ne_zero _ hlogne)) hfn

/-! ### The strict subordination relation of eq. (26) -/

/-- `(D₁, a₁, b₁)` is strictly subordinate to `(D₂, a₂, b₂)`: either its Gamma valuation is strictly
larger, or the valuations agree and its algebraic-logarithmic monomial is lexicographically
smaller. -/
def StrictlySubordinateAt (D₁ D₂ : GammaRationalDatum) (a₁ b₁ a₂ b₂ : ℕ) : Prop :=
  (∃ n : ℕ, 0 < n ∧ D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder)) ∨
    (D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder ∧
      (a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂)))

/-- A strictly larger Gamma valuation kills the ratio whatever algebraic-logarithmic monomials
accompany it. -/
theorem gammaRationalDatum_logRatio_tendsto_zero_of_gap
    (D₁ D₂ : GammaRationalDatum) (a₁ b₁ a₂ b₂ n : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder)) (hnpos : 0 < n)
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.logFn a₁ b₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.logFn a₂ b₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hnum := tendsto_pow_mul_log_pow_mul_Gamma_pow hσ a₁ b₁ n hnpos
  have hg0 : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := Gamma_vertical_tendsto_zero hσ
  have hunit : Tendsto (fun t : ℝ =>
      (D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
      (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
      atTop (nhds ((D₁.numUnit.eval 0 * D₂.denUnit.eval 0) /
        (D₁.denUnit.eval 0 * D₂.numUnit.eval 0))) :=
    ((((Polynomial.continuous D₁.numUnit).tendsto 0).mul
      ((Polynomial.continuous D₂.denUnit).tendsto 0)).div
      (((Polynomial.continuous D₁.denUnit).tendsto 0).mul
        ((Polynomial.continuous D₂.numUnit).tendsto 0))
      (mul_ne_zero D₁.denUnit_ne D₂.numUnit_ne)).comp hg0
  have hlogtop := tendsto_norm_log_vertical_atTop hσ.le
  have hmodel : Tendsto (fun t : ℝ =>
      (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
          (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₁ *
          (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n) *
        ((D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
          (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))) *
        ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
          (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)⁻¹)) atTop (nhds 0) := by
    have hprod := hnum.mul hunit
    rw [zero_mul] at hprod
    rw [tendsto_zero_iff_norm_tendsto_zero] at hprod ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hprod
    filter_upwards [eventually_ge_atTop (1 : ℝ), hlogtop.eventually_ge_atTop 1] with t ht hlog1
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      le_trans ht (le_norm_vertical σ ht0.le)
    have hinv : ‖((((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂ *
        (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ b₂)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, norm_mul, norm_pow, norm_pow]
      rw [inv_le_one₀ (by positivity)]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hs1) (one_le_pow₀ hlog1)
    rw [norm_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _)) (le_of_eq (mul_one _))
  refine hmodel.congr' ?_
  have hgne : ∀ᶠ t : ℝ in atTop, Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    have hg := Gamma_vertical_tendsto_nhdsWithin_zero hσ
    exact hg.eventually self_mem_nhdsWithin
  have hunits : ∀ (R : Polynomial ℂ), R.eval 0 ≠ 0 →
      ∀ᶠ t : ℝ in atTop, R.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
    intro R hR
    exact (((Polynomial.continuous R).tendsto 0).comp hg0).eventually (isOpen_ne.mem_nhds hR)
  filter_upwards [hgne, hunits D₁.denUnit D₁.denUnit_ne, hunits D₂.numUnit D₂.numUnit_ne,
    hunits D₂.denUnit D₂.denUnit_ne] with t hg h1 h2 h3
  have hfac := gammaRational_ratio_eq (g := Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
    hg D₁.numUnit D₁.denUnit D₂.numUnit D₂.denUnit
    D₁.numOrder D₁.denOrder D₂.numOrder D₂.denOrder n hn h1 h2 h3
  rw [logFn_ratio_eq]
  simp only [GammaRationalDatum.fn, GammaRationalDatum.num, GammaRationalDatum.den]
  rw [hfac]
  field_simp

/-- **Strict subordination sends the normalized ratio to zero.** -/
theorem gammaRationalDatum_logRatio_tendsto_zero_of_subordinate
    (D₁ D₂ : GammaRationalDatum) (a₁ b₁ a₂ b₂ : ℕ)
    (hsub : StrictlySubordinateAt D₁ D₂ a₁ b₁ a₂ b₂) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.logFn a₁ b₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.logFn a₂ b₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  rcases hsub with ⟨n, hnpos, hn⟩ | ⟨heq, hlex⟩
  · exact gammaRationalDatum_logRatio_tendsto_zero_of_gap D₁ D₂ a₁ b₁ a₂ b₂ n hn hnpos hσ
  · exact gammaRationalDatum_logRatio_tendsto_zero_of_lex D₁ D₂ heq hlex hσ

/-! ### The collapse -/

/-- **Unconditional finite-phase collapse against algebraic-logarithmic Gamma monomials.**  Let `f`
be holomorphic on the open vertical strip of half-width `η ≤ σ` about `σ` and Bohr almost periodic
there.  If `f` satisfies a finite differential relation whose coefficients are the monomials
`s^{a α} (log s)^{b α} · P_α(Γ)/Q_α(Γ)`, and the coefficient at `β` strictly dominates every other in
the ordering (26), then the differential monomial attached to `β` vanishes identically on the strip.

Both analytic inputs are theorems: the return times come from the Bohr hull, and the coefficient
projective boundary is the valuation ordering. -/
theorem gammaLog_strip_relation_dominant_monomial_eq_zero
    {ι : Type*} [DecidableEq ι] (E : Finset ι)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (a b : ι → ℕ) (β : ι) (hβ : β ∈ E)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (a α) (b α) (a β) (b β))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (D α).logFn (a α) (b α) s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 := by
  classical
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse E hη f exps
      (fun α => (D α).logFn (a α) (b α)) β hβ hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  have hFβ : ∀ᶠ l in atTop,
      (D β).logFn (a β) (b β) (z₀ + (T l : ℂ) * Complex.I) ≠ 0 :=
    eventually_vertical_along_returns (p := fun s => (D β).logFn (a β) (b β) s ≠ 0)
      (z₀ := z₀) (logFn_eventually_ne_zero (D β) (a β) (b β) hzre) hT
  have hcoeff : ∀ α ∈ E, Tendsto
      (fun l => (D α).logFn (a α) (b α) (z₀ + (T l : ℂ) * Complex.I) /
        (D β).logFn (a β) (b β) (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (if α = β then (1 : ℂ) else 0)) := by
    intro α hα
    rcases eq_or_ne α β with hab | hab
    · subst hab
      have hone : Tendsto
          (fun l => (D α).logFn (a α) (b α) (z₀ + (T l : ℂ) * Complex.I) /
            (D α).logFn (a α) (b α) (z₀ + (T l : ℂ) * Complex.I)) atTop (nhds (1 : ℂ)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hFβ] with l hl
        exact (div_self hl).symm
      simpa using hone
    · have hzero := gammaRationalDatum_logRatio_tendsto_zero_of_subordinate
        (D α) (D β) (a α) (b α) (a β) (b β) (hdom α hα hab) hzre
      simpa [hab] using tendsto_vertical_along_returns
        (F := fun s => (D α).logFn (a α) (b α) s / (D β).logFn (a β) (b β) s)
        (z₀ := z₀) hzero hT
  have hcollapse := hmain z₀ hz₀ (fun α => if α = β then (1 : ℂ) else 0) hFβ hcoeff
  have hred := Finset.sum_eq_single_of_mem β hβ
    (f := fun α : ι => (if α = β then (1 : ℂ) else 0) * diffMonomial f (exps α) z₀)
    (by
      intro c _ hc
      simp [hc])
  have hzero := hcollapse.1
  rw [hred] at hzero
  simpa using hzero

end

end GaloisForLFunctions
