import GaloisForLFunctions.HTGeometry.EulerQGammaAnalytic
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# Meromorphic continuation of the Euler q-Gamma response

Cutting the zeta ladder after `K` factors,
`F_σ^K(s) = ζ(σ)^s · C_σ · (∏_{k<K} ζ(σ(1+s+k))) · D_σ(σ(1+s+K))`,
gives a function that agrees with the response on the convergence chamber, does not depend on `K`
where two cut-offs are both admissible, and is meromorphic wherever the last factor converges — the
first factor is entire, the middle ones are finitely many meromorphic zeta values, and the last is
analytic by the term-by-term differentiation of the arithmetic Dirichlet series.  Since every `s`
becomes admissible for large enough `K`, this is a meromorphic continuation of `F_σ` to all of `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Meromorphy along an affine substitution -/

theorem meromorphicAt_comp_affine {f : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) {s : ℂ}
    (hf : MeromorphicAt f (a * s + b)) : MeromorphicAt (fun z : ℂ => f (a * z + b)) s := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have haff : AnalyticAt ℂ (fun z : ℂ => a * z + b) s :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hcomp : AnalyticAt ℂ
      ((fun w : ℂ => (w - (a * s + b)) ^ n • f w) ∘ (fun z : ℂ => a * z + b)) s :=
    AnalyticAt.comp (g := fun w : ℂ => (w - (a * s + b)) ^ n • f w)
      (f := fun z : ℂ => a * z + b) hn haff
  have hmul : AnalyticAt ℂ
      (fun z : ℂ => (a ^ n)⁻¹ *
        (((fun w : ℂ => (w - (a * s + b)) ^ n • f w) ∘ (fun z : ℂ => a * z + b)) z)) s :=
    analyticAt_const.mul hcomp
  refine hmul.congr ?_
  filter_upwards with z
  simp only [Function.comp_apply, smul_eq_mul]
  have hz : a * z + b - (a * s + b) = a * (z - s) := by ring
  rw [hz, mul_pow]
  field_simp

/-! ## Meromorphy of the zeta value -/

theorem meromorphicAt_riemannZeta (z : ℂ) : MeromorphicAt riemannZeta z := by
  by_cases hz : z = 1
  · subst hz
    exact meromorphicAt_riemannZeta_one
  · exact (analyticOn_riemannZeta z hz).meromorphicAt

/-! ## The cut ladder -/

/-- The `K`-th shifted argument `σ(1+s) + Kσ` of the ladder. -/
def eqgArg (σ : EulerSigma) (K : ℕ) (s : ℂ) : ℂ :=
  eqgExponent σ s + (K : ℂ) * (σ.val : ℂ)

theorem eqgArg_affine (σ : EulerSigma) (K : ℕ) (s : ℂ) :
    eqgArg σ K s = (σ.val : ℂ) * s + (σ.val : ℂ) * (1 + (K : ℂ)) := by
  rw [eqgArg, eqgExponent]
  ring

theorem sigma_ne_zero (σ : EulerSigma) : ((σ.val : ℂ)) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact σ.pos.ne'

/-- The Euler q-Gamma response with the zeta ladder cut after `K` factors. -/
def eqgCont (σ : EulerSigma) (K : ℕ) (s : ℂ) : ℂ :=
  riemannZeta (σ.val : ℂ) ^ s
    * (((eqgConst σ : ℝ) : ℂ)
      * ((∏ k ∈ Finset.range K, riemannZeta (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ)))
        * eqgDirichlet σ (eqgArg σ K s)))

/-- **The cut ladder computes the response on the convergence chamber.** -/
theorem eqgCont_eq_response (σ : EulerSigma) (K : ℕ) {s : ℂ} (hs : 1 < (eqgExponent σ s).re) :
    eqgCont σ K s = eqgResponse σ s := by
  rw [eqgCont, eqgResponse, eqgArg, eqgDirichlet_ladder_step σ hs K]

/-- **The cut is immaterial**: raising `K` by one changes nothing where both are admissible. -/
theorem eqgCont_succ (σ : EulerSigma) (K : ℕ) {s : ℂ} (hK : 1 < (eqgArg σ K s).re) :
    eqgCont σ (K + 1) s = eqgCont σ K s := by
  have hshift := eqgDirichlet_shift σ hK
  have harg : eqgArg σ K s + (σ.val : ℂ) = eqgArg σ (K + 1) s := by
    rw [eqgArg, eqgArg]
    push_cast
    ring
  rw [harg] at hshift
  rw [eqgCont, eqgCont, Finset.prod_range_succ, hshift]
  have harg' : eqgArg σ K s = eqgExponent σ s + (K : ℂ) * (σ.val : ℂ) := rfl
  rw [harg']
  ring

/-! ## Meromorphy -/

theorem analyticAt_zeta_sigma_cpow (σ : EulerSigma) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (σ.val : ℂ) ^ z) s := by
  have hfun : (fun z : ℂ => riemannZeta (σ.val : ℂ) ^ z)
      = fun z : ℂ => Complex.exp (Complex.log (riemannZeta (σ.val : ℂ)) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero (zeta_sigma_ne_zero σ)]
  rw [hfun]
  exact (analyticAt_const.mul analyticAt_id).cexp

theorem meromorphicAt_zeta_ladder_factor (σ : EulerSigma) (k : ℕ) (s : ℂ) :
    MeromorphicAt (fun z : ℂ => riemannZeta (eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))) s := by
  have haff : ∀ z : ℂ, eqgExponent σ z + (k : ℂ) * (σ.val : ℂ)
      = (σ.val : ℂ) * z + (σ.val : ℂ) * (1 + (k : ℂ)) := fun z => eqgArg_affine σ k z
  have hfun : (fun z : ℂ => riemannZeta (eqgExponent σ z + (k : ℂ) * (σ.val : ℂ)))
      = fun z : ℂ => riemannZeta ((σ.val : ℂ) * z + (σ.val : ℂ) * (1 + (k : ℂ))) := by
    funext z
    rw [haff z]
  rw [hfun]
  exact meromorphicAt_comp_affine (sigma_ne_zero σ) (meromorphicAt_riemannZeta _)

theorem analyticAt_eqgDirichlet_arg (σ : EulerSigma) (K : ℕ) {s : ℂ}
    (hK : 1 < (eqgArg σ K s).re) :
    AnalyticAt ℂ (fun z : ℂ => eqgDirichlet σ (eqgArg σ K z)) s := by
  have haff : AnalyticAt ℂ (fun z : ℂ => eqgArg σ K z) s := by
    have hfun : (fun z : ℂ => eqgArg σ K z)
        = fun z : ℂ => (σ.val : ℂ) * z + (σ.val : ℂ) * (1 + (K : ℂ)) := by
      funext z
      exact eqgArg_affine σ K z
    rw [hfun]
    exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
  exact (analyticAt_eqgDirichlet σ hK).comp haff

/-- **Theorem 5.1, continuation clause.**  The cut ladder is meromorphic wherever it converges. -/
theorem meromorphicAt_eqgCont (σ : EulerSigma) (K : ℕ) {s : ℂ} (hK : 1 < (eqgArg σ K s).re) :
    MeromorphicAt (eqgCont σ K) s := by
  have h1 : MeromorphicAt (fun z : ℂ => riemannZeta (σ.val : ℂ) ^ z) s :=
    (analyticAt_zeta_sigma_cpow σ s).meromorphicAt
  have h2 : MeromorphicAt
      (fun z : ℂ => ∏ k ∈ Finset.range K,
        riemannZeta (eqgExponent σ z + (k : ℂ) * (σ.val : ℂ))) s :=
    MeromorphicAt.fun_prod fun k _ => meromorphicAt_zeta_ladder_factor σ k s
  have h3 : MeromorphicAt (fun z : ℂ => eqgDirichlet σ (eqgArg σ K z)) s :=
    (analyticAt_eqgDirichlet_arg σ K hK).meromorphicAt
  have hconst : MeromorphicAt (fun _ : ℂ => ((eqgConst σ : ℝ) : ℂ)) s :=
    analyticAt_const.meromorphicAt
  exact h1.fun_mul (hconst.fun_mul (h2.fun_mul h3))

/-- Every point becomes admissible after finitely many ladder steps. -/
theorem exists_admissible_cut (σ : EulerSigma) (s : ℂ) :
    ∃ K : ℕ, 1 < (eqgArg σ K s).re := by
  obtain ⟨K, hK⟩ := exists_nat_gt ((1 - (eqgExponent σ s).re) / σ.val)
  refine ⟨K, ?_⟩
  have hre : (eqgArg σ K s).re = (eqgExponent σ s).re + (K : ℝ) * σ.val := by
    rw [eqgArg]
    simp
  rw [hre]
  have hσ : 0 < σ.val := σ.pos
  have hmul : (1 - (eqgExponent σ s).re) < (K : ℝ) * σ.val := by
    rw [div_lt_iff₀ hσ] at hK
    exact hK
  linarith

/-- **Theorem 5.1, continuation.**  `F_σ` continues meromorphically to every point of `ℂ`, and the
continuation agrees with the response on the convergence chamber. -/
theorem eqgResponse_meromorphic_continuation (σ : EulerSigma) (s : ℂ) :
    ∃ K : ℕ, MeromorphicAt (eqgCont σ K) s ∧
      ∀ t : ℂ, 1 < (eqgExponent σ t).re → eqgCont σ K t = eqgResponse σ t := by
  obtain ⟨K, hK⟩ := exists_admissible_cut σ s
  exact ⟨K, meromorphicAt_eqgCont σ K hK, fun t ht => eqgCont_eq_response σ K ht⟩

/-! ## The translation law of the continuation -/

/-- **Theorem 5.1, translation law of the continuation.**  An unconditional identity of the cut
ladders: `ζ(σ)·F^{K+1}_σ(s) = ζ(σ(1+s))·F^K_σ(s+1)` for every `s` and every `K`.  On the
convergence chamber this is (EQG.13); off it, it is the translation law of the meromorphic
continuation. -/
theorem eqgCont_translation (σ : EulerSigma) (K : ℕ) (s : ℂ) :
    riemannZeta (σ.val : ℂ) * eqgCont σ (K + 1) s
      = riemannZeta (eqgExponent σ s) * eqgCont σ K (s + 1) := by
  have hshiftArg : ∀ k : ℕ, eqgExponent σ (s + 1) + (k : ℂ) * (σ.val : ℂ)
      = eqgExponent σ s + ((k : ℂ) + 1) * (σ.val : ℂ) := by
    intro k
    rw [eqgExponent, eqgExponent]
    ring
  have hprod : (∏ k ∈ Finset.range K,
        riemannZeta (eqgExponent σ (s + 1) + (k : ℂ) * (σ.val : ℂ)))
      = ∏ k ∈ Finset.range K,
        riemannZeta (eqgExponent σ s + ((k : ℕ) + 1 : ℕ) * (σ.val : ℂ)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hshiftArg k]
    push_cast
    ring_nf
  have hsplit : (∏ k ∈ Finset.range (K + 1),
        riemannZeta (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ)))
      = (∏ k ∈ Finset.range K,
          riemannZeta (eqgExponent σ s + ((k : ℕ) + 1 : ℕ) * (σ.val : ℂ)))
        * riemannZeta (eqgExponent σ s + ((0 : ℕ) : ℂ) * (σ.val : ℂ)) :=
    Finset.prod_range_succ' _ K
  have hzero : eqgExponent σ s + ((0 : ℕ) : ℂ) * (σ.val : ℂ) = eqgExponent σ s := by
    push_cast
    ring
  have hargK : eqgArg σ K (s + 1) = eqgArg σ (K + 1) s := by
    rw [eqgArg, eqgArg, eqgExponent, eqgExponent]
    push_cast
    ring
  rw [eqgCont, eqgCont, hsplit, hzero, hprod, hargK,
    Complex.cpow_add _ _ (zeta_sigma_ne_zero σ), Complex.cpow_one]
  ring

end

end GaloisForLFunctions.HTGeometry
