import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance

/-!
# The quantitative-Hölder interface for half-argument digamma jets

**QH** is the statement: no nonzero differential polynomial in the point `s` and the
half-argument digamma jets `ψ(s/2), ψ'(s/2), …` is exponentially small on the real ray.
It is the single analytic wall between Hölder's theorem and the hypertranscendence of the
completed zeta function: a differential-algebraic relation for `ξ` produces, after the
Dirichlet-frequency collapse, a half-argument digamma jet polynomial that is exponentially
small — QH forces it to vanish as a polynomial.

This module machine-checks everything on the vanishing side of that wall:

* `halfDigamma_jet_annihilator_eq_zero` — **the vanishing case of QH is a theorem**: a
  half-argument jet polynomial vanishing off the poles is the zero polynomial, by the
  substitution `s ↦ 2s` into Hölder's theorem (`digamma_jet_annihilator_eq_zero`).
* `halfDigamma_jet_annihilator_eq_zero_of_ray` — vanishing on the far real ray already
  suffices: the jet evaluation is analytic on the pole-free plane, which is connected as
  the complement of a countable set, so the identity theorem propagates the vanishing.
* `QuantitativeHolder` — the QH proposition itself.
* `WatsonFlatness` — the named analytic input: an exponentially small jet evaluation
  vanishes on the far ray (classically via sectorial Gevrey-1 bounds for the digamma
  asymptotic series and Watson uniqueness).
* `quantitativeHolder_of_watsonFlatness` — **QH reduces to Watson flatness**: modulo that
  single named input, the machine-checked identity-theorem ray rigidity and Hölder's
  theorem discharge all remaining content of QH.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial Filter

/-- Evaluation of a differential polynomial on the half-argument digamma jets:
`P(z, ψ(z/2), ψ'(z/2), …, ψ⁽ⁿ⁾(z/2))`. -/
def halfDigammaJetEval (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (z : ℂ) : ℂ :=
  MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) =>
    iteratedDeriv (j : ℕ) Complex.digamma (z / 2)) P

/-! ## The vanishing case of QH -/

/-- The substitution doubling the point variable. -/
def doubleSub (n : ℕ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (MvPolynomial.C 2 * MvPolynomial.X 0) (fun j => MvPolynomial.X j.succ)

/-- The substitution halving the point variable. -/
def halveSub (n : ℕ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (MvPolynomial.C (1 / 2) * MvPolynomial.X 0) (fun j => MvPolynomial.X j.succ)

theorem halveSub_comp_doubleSub (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    bind₁ (halveSub n) (bind₁ (doubleSub n) P) = P := by
  rw [MvPolynomial.bind₁_bind₁]
  have hgen : (fun i : Fin (n + 2) => bind₁ (halveSub n) (doubleSub n i))
      = (MvPolynomial.X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
    funext i
    induction i using Fin.cases with
    | zero =>
        simp only [doubleSub, Fin.cases_zero, map_mul, bind₁_C_right, bind₁_X_right,
          halveSub]
        rw [← mul_assoc, ← map_mul]
        norm_num
    | succ j =>
        simp only [doubleSub, Fin.cases_succ, bind₁_X_right, halveSub]
  rw [hgen, MvPolynomial.bind₁_X_left]
  rfl

/-- **The vanishing case of QH is a theorem**: a differential polynomial whose evaluation
on the half-argument digamma jets vanishes off the poles is the zero polynomial. -/
theorem halfDigamma_jet_annihilator_eq_zero (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ z : ℂ, (∀ p : ℕ, z / 2 ≠ -(p : ℂ)) → halfDigammaJetEval n P z = 0) :
    P = 0 := by
  have hQ : bind₁ (doubleSub n) P = 0 := by
    apply digamma_jet_annihilator_eq_zero
    intro w hw
    rw [eval_bind₁]
    have hvec : (fun i : Fin (n + 2) =>
        MvPolynomial.eval (Fin.cons w fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) Complex.digamma w) (doubleSub n i))
        = Fin.cons (2 * w) (fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) Complex.digamma ((2 * w) / 2)) := by
      funext i
      induction i using Fin.cases with
      | zero =>
          simp only [doubleSub, Fin.cases_zero, map_mul, eval_C, eval_X, Fin.cons_zero]
      | succ j =>
          simp only [doubleSub, Fin.cases_succ, eval_X, Fin.cons_succ]
          rw [show (2 * w) / 2 = w by ring]
    rw [hvec]
    exact hPz (2 * w) (by
      intro p
      rw [show (2 * w) / 2 = w by ring]
      exact hw p)
  have hback := halveSub_comp_doubleSub n P
  rw [hQ, map_zero] at hback
  exact hback.symm

/-! ## Ray rigidity: vanishing far out on the real ray suffices -/

/-- The half-argument jet evaluation is analytic off the poles `−2ℕ`. -/
theorem analyticAt_halfDigammaJetEval (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ}
    (hz : ∀ p : ℕ, z / 2 ≠ -(p : ℂ)) :
    AnalyticAt ℂ (fun w => halfDigammaJetEval n P w) z := by
  have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  have hhalf : AnalyticAt ℂ (fun w : ℂ => w / 2) z :=
    analyticAt_id.div analyticAt_const (by norm_num)
  have hjet : ∀ j : ℕ,
      AnalyticAt ℂ (fun w : ℂ => iteratedDeriv j Complex.digamma (w / 2)) z := by
    intro j
    have h1 : AnalyticAt ℂ (iteratedDeriv j Complex.digamma) (z / 2) := by
      rw [← hψ]
      exact analyticAt_iteratedDeriv_logDeriv j _ hz
    have hc := AnalyticAt.comp (f := fun w : ℂ => w / 2) (x := z) h1 hhalf
    simpa only [Function.comp_def] using hc
  induction P using MvPolynomial.induction_on with
  | C c =>
      have : (fun w => halfDigammaJetEval n (MvPolynomial.C c) w) = fun _ => c := by
        funext w
        simp [halfDigammaJetEval]
      rw [this]
      exact analyticAt_const
  | add p q hp hq =>
      have : (fun w => halfDigammaJetEval n (p + q) w)
          = fun w => halfDigammaJetEval n p w + halfDigammaJetEval n q w := by
        funext w
        simp [halfDigammaJetEval]
      rw [this]
      exact hp.add hq
  | mul_X p i hp =>
      have hsplit : (fun w => halfDigammaJetEval n (p * MvPolynomial.X i) w)
          = fun w => halfDigammaJetEval n p w
              * ((Fin.cons w fun j : Fin (n + 1) =>
                  iteratedDeriv (j : ℕ) Complex.digamma (w / 2) : Fin (n + 2) → ℂ)) i := by
        funext w
        simp [halfDigammaJetEval]
      rw [hsplit]
      refine hp.mul ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact analyticAt_id
      | succ j =>
          simp only [Fin.cons_succ]
          exact hjet (j : ℕ)

/-- **Ray rigidity**: a half-argument jet polynomial vanishing on the far real ray is the
zero polynomial.  The jet evaluation is analytic on the pole-free plane — connected as the
complement of a countable set — so the identity theorem propagates ray vanishing
everywhere, and the vanishing case of QH finishes. -/
theorem halfDigamma_jet_annihilator_eq_zero_of_ray (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ᶠ σ : ℝ in atTop, halfDigammaJetEval n P σ = 0) : P = 0 := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hPz
  set x₀ : ℝ := max M 1 + 1 with hx₀_def
  set Ω : Set ℂ := {z : ℂ | ∀ p : ℕ, z / 2 ≠ -(p : ℂ)} with hΩ_def
  have hΩ_open : IsOpen Ω := by
    have : Ω = (fun z : ℂ => z / 2) ⁻¹' {w : ℂ | ∀ p : ℕ, w ≠ -(p : ℂ)} := rfl
    rw [this]
    exact (offPoles_isOpen).preimage (continuous_id.div_const 2)
  have hΩ_conn : IsPreconnected Ω := by
    have hΩ_compl : Ω = (Set.range fun p : ℕ => (-(2 * p : ℕ) : ℂ))ᶜ := by
      ext z
      simp only [hΩ_def, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      constructor
      · intro h p hEq
        apply h p
        rw [← hEq]
        push_cast
        ring
      · intro h p hEq
        apply h p
        rw [show z = 2 * (z / 2) by ring, hEq]
        push_cast
        ring
    rw [hΩ_compl]
    refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
      (Set.countable_range _)).isConnected.isPreconnected
    rw [Complex.rank_real_complex]
    norm_num
  have hmem : ∀ σ : ℝ, 0 < σ → (σ : ℂ) ∈ Ω := by
    intro σ hσ p hEq
    have hcast : ((σ / 2 : ℝ) : ℂ) = ((-(p : ℝ) : ℝ) : ℂ) := by
      push_cast
      linear_combination hEq
    have hreal := Complex.ofReal_inj.mp hcast
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have hx₀pos : (0 : ℝ) < x₀ := by
    have h1 : (1 : ℝ) ≤ max M 1 := le_max_right M 1
    rw [hx₀_def]
    linarith
  have hx₀Ω : ((x₀ : ℝ) : ℂ) ∈ Ω := hmem x₀ hx₀pos
  have hanalytic : AnalyticOnNhd ℂ (fun w => halfDigammaJetEval n P w) Ω :=
    fun z hz => analyticAt_halfDigammaJetEval n P hz
  -- frequently-vanishing at the interior real point `x₀`
  have hfreq : ∃ᶠ z in nhdsWithin ((x₀ : ℝ) : ℂ) {((x₀ : ℝ) : ℂ)}ᶜ,
      halfDigammaJetEval n P z = 0 := by
    have htendsto : Tendsto (fun σ : ℝ => (σ : ℂ))
        (nhdsWithin x₀ {x₀}ᶜ) (nhdsWithin ((x₀ : ℝ) : ℂ) {((x₀ : ℝ) : ℂ)}ᶜ) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hσ ⊢
        exact fun hEq => hσ (Complex.ofReal_inj.mp hEq)
    refine htendsto.frequently ?_
    have hev : ∀ᶠ σ : ℝ in nhdsWithin x₀ {x₀}ᶜ, halfDigammaJetEval n P σ = 0 := by
      have hnhds : ∀ᶠ σ : ℝ in nhds x₀, halfDigammaJetEval n P σ = 0 := by
        have hIoi : Set.Ioi M ∈ nhds x₀ := Ioi_mem_nhds (by
          have h1 : M ≤ max M 1 := le_max_left M 1
          rw [hx₀_def]
          linarith)
        filter_upwards [hIoi] with σ hσ
        exact hM σ (le_of_lt hσ)
      exact hnhds.filter_mono nhdsWithin_le_nhds
    exact hev.frequently
  have hzero : Set.EqOn (fun w => halfDigammaJetEval n P w) 0 Ω :=
    hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩ_conn hx₀Ω hfreq
  exact halfDigamma_jet_annihilator_eq_zero n P (fun z hz => hzero hz)

/-! ## The QH proposition and its reduction to Watson flatness -/

/-- **QH — quantitative Hölder.**  No nonzero differential polynomial in the point and the
half-argument digamma jets is exponentially small on the real ray. -/
def QuantitativeHolder : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ),
    (∃ c : ℝ, 0 < c ∧
      (fun σ : ℝ => halfDigammaJetEval n P σ)
        =O[atTop] fun σ => Real.exp (-c * σ)) →
    P = 0

/-- **Watson flatness** — the named analytic input separating QH from Hölder's theorem: an
exponentially small half-argument jet evaluation vanishes on the far real ray.  Classically
this follows from the sectorial Gevrey-1 asymptotics of the digamma function and Watson's
uniqueness theorem: the evaluation is Gevrey-1-flat in a sector of opening greater than `π`,
hence zero. -/
def WatsonFlatness : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (c : ℝ), 0 < c →
    ((fun σ : ℝ => halfDigammaJetEval n P σ)
      =O[atTop] fun σ => Real.exp (-c * σ)) →
    ∀ᶠ σ : ℝ in atTop, halfDigammaJetEval n P σ = 0

/-- **QH reduces to Watson flatness.**  Modulo the single named analytic input, the
machine-checked ray rigidity and Hölder's theorem discharge all remaining content of QH: a
Watson-flat exponentially small jet evaluation vanishes on the ray, hence identically, hence
as a polynomial. -/
theorem quantitativeHolder_of_watsonFlatness (hW : WatsonFlatness) :
    QuantitativeHolder := by
  rintro n P ⟨c, hc, hO⟩
  exact halfDigamma_jet_annihilator_eq_zero_of_ray n P (hW n P c hc hO)

end GaloisForLFunctions

end
