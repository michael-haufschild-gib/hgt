import GaloisForLFunctions.RHTower.WeilProducerLittlewoodBound
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog

/-!
# Littlewood's bound for `ζ` under RH, through the Weil cone

**Theorems.**  Under RH:
- (`exists_norm_riemannZeta_le_littlewood_of_riemannHypothesis`, Littlewood) there are `C` and `T₀`
  with `|ζ(σ + it)| ≤ exp(C log|t| / log log|t|)` for `½ ≤ σ ≤ 2` and `|t| ≥ T₀`;
- (`log_norm_riemannZeta_le_soundararajan`, Soundararajan) `log|ζ(σ + it)|` is bounded by the
  `log(x/n)`-weighted prime polynomial at `σ₀ = ½ + λ/log x`, plus `(1 + λ)/2 · log|t|/log x + O(1/log x)`.

**Proof.**  Under RH, `Λ` is full-cone Weil-positive (`weilPositiveFull_vonMangoldt_of_riemannHypothesis`).
For `lam = Λ` the horizontal logarithm `producerLogZeta` is `log ζ`: the continuation `A_Λ` equals
`−ζ'/ζ` on the zero-free quadrants `{Re z > ½, ±Im z > 0}` by the identity theorem.  So
`ζ(u + it)·exp(−log F_Λ(u + it))` has zero derivative in `u > ½`.  At `u = 2` its value is `1`,
because `exp Σ Λ(n) n^{−s}/log n = ζ(s)` there.  The bound is the Weil-cone Littlewood bound
(`exists_re_producerLogZeta_le_littlewood`) with `κ = 1`, extended to `σ = ½` by continuity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-- The von Mangoldt weights as a real sequence. -/
abbrev vonMangoldtReal : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)

theorem lamC_vonMangoldt : lamC vonMangoldtReal = fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  unfold lamC
  split_ifs with hn
  · rfl
  · have : ArithmeticFunction.vonMangoldt n = 0 := by interval_cases n <;> simp
    simp [this]

theorem lamLogC_vonMangoldt : lamLogC vonMangoldtReal = eulerLogDirichletCoeff := by
  funext n
  rw [lamLogC, lamC_vonMangoldt, eulerLogDirichletCoeff, Complex.natCast_log]

theorem riemannZeta_ne_zero_of_half_lt (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re)
    (hz1 : z ≠ 1) : riemannZeta z ≠ 0 := by
  intro h0
  have := hRH z h0 (by
    rintro ⟨n, rfl⟩
    simp at hz
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith) hz1
  linarith

/-- Under RH, `A_Λ = −ζ'/ζ` on `Re z > ½` off the real axis. -/
theorem producerA_vonMangoldt_eq (hRH : RiemannHypothesis) (hW : WeilPositiveFull vonMangoldtReal)
    {z : ℂ} (hz : 1 / 2 < z.re) (hzim : z.im ≠ 0) :
    producerA hW z = -deriv riemannZeta z / riemannZeta z := by
  set S : Set ℂ := {w : ℂ | 1 / 2 < w.re ∧ 0 < z.im * w.im} with hS
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im))
  have hSc : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    simp only [hS, Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hx hy ⊢
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have key : ∀ p q : ℝ, 0 < p → 0 < q → 0 < a * p + b * q := by
      intro p q hp hq
      rcases ha.lt_or_eq with h | h
      · have h1 := mul_pos h hp
        have h2 := mul_nonneg hb hq.le
        linarith
      · rw [← h] at hab ⊢
        have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
    constructor
    · have := key (x.re - 1 / 2) (y.re - 1 / 2) (by linarith) (by linarith)
      linarith
    · have := key (z.im * x.im) (z.im * y.im) hx2 hy2
      linarith
  have hne1 : ∀ w ∈ S, w ≠ 1 := fun w hw h1 => by
    have := hw.2
    rw [h1, Complex.one_im, mul_zero] at this
    exact lt_irrefl _ this
  have hdA : DifferentiableOn ℂ (producerA hW) S := fun w hw =>
    (hasDerivAt_producerA hW hw.1 (hne1 w hw)).differentiableAt.differentiableWithinAt
  have hdζ : DifferentiableOn ℂ riemannZeta S := fun w hw =>
    (differentiableAt_riemannZeta (hne1 w hw)).differentiableWithinAt
  have hdZ : DifferentiableOn ℂ (fun w => -deriv riemannZeta w / riemannZeta w) S :=
    ((hdζ.deriv hSo).neg).div hdζ fun w hw =>
      riemannZeta_ne_zero_of_half_lt hRH hw.1 (hne1 w hw)
  set z₀ : ℂ := 2 + z.im * I with hz₀
  have hz₀S : z₀ ∈ S := by
    refine ⟨by simp [hz₀]; norm_num, ?_⟩
    have : z₀.im = z.im := by simp [hz₀]
    rw [this]; exact mul_self_pos.mpr hzim
  have hzS : z ∈ S := ⟨hz, mul_self_pos.mpr hzim⟩
  have hev : producerA hW =ᶠ[𝓝 z₀] fun w => -deriv riemannZeta w / riemannZeta w := by
    have hO : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : z₀ ∈ {w : ℂ | 1 < w.re} := by simp [hz₀]
    refine Filter.eventuallyEq_of_mem (hO.mem_nhds hmem) fun w hw => ?_
    rw [producerA_eq_LSeries hW hw, lamC_vonMangoldt,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  exact (hdA.analyticOnNhd hSo).eqOn_of_preconnected_of_eventuallyEq (hdZ.analyticOnNhd hSo)
    hSc.isPreconnected hz₀S hev hzS

/-- **For `Λ`, the horizontal logarithm is `log ζ`.**  Under RH, for `σ > ½` and `t ≠ 0`,
`ζ(σ + it) = exp(log F_Λ(σ + it))`. -/
theorem riemannZeta_eq_cexp_producerLogZeta (hRH : RiemannHypothesis)
    (hW : WeilPositiveFull vonMangoldtReal) {σ t : ℝ} (hσ : 1 / 2 < σ) (ht : t ≠ 0) :
    riemannZeta ((σ : ℂ) + t * I) = cexp (producerLogZeta hW σ t) := by
  set P : ℝ → ℂ := fun u => producerLogZeta hW u t with hP
  set f : ℝ → ℂ := fun v => producerA hW ((v : ℂ) + t * I) with hf
  set g : ℝ → ℂ := fun u => riemannZeta ((u : ℂ) + t * I) * cexp (-P u) with hg
  have hdom : ∀ v : ℝ, 1 / 2 < v → (v : ℂ) + t * I ∈ producerDomain := fun v hv =>
    horizontal_mem_producerDomain hv ht
  have hfc : ContinuousOn f (Ioi (1 / 2)) :=
    (continuousOn_producerA hW).comp (by fun_prop) fun v hv => hdom v hv
  -- derivative of `P`
  have hPd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt P (-f x) x := by
    intro x hx
    have hII : IntervalIntegrable f volume x 2 := by
      refine (hfc.mono fun v hv => ?_).intervalIntegrable
      rcases Set.mem_uIcc.mp hv with h | h
      · exact lt_of_lt_of_le hx h.1
      · show 1 / 2 < v; linarith [h.1]
    have hsm : StronglyMeasurableAtFilter f (𝓝 x) volume :=
      hfc.stronglyMeasurableAtFilter isOpen_Ioi x hx
    have hca : ContinuousAt f x := hfc.continuousAt (isOpen_Ioi.mem_nhds hx)
    have h := (intervalIntegral.integral_hasDerivAt_left hII hsm hca).const_add
      (LSeries (lamLogC vonMangoldtReal) ((2 : ℂ) + t * I))
    exact h
  -- derivative of `g` vanishes
  have hgd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt g 0 x := by
    intro x hx
    have hm := hdom x hx
    have hζ : HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + t * I))
        (deriv riemannZeta ((x : ℂ) + t * I)) x :=
      ((differentiableAt_riemannZeta hm.2).hasDerivAt.comp_add_const (x : ℂ) (t * I)).comp_ofReal
    have hE : HasDerivAt (fun u : ℝ => cexp (-P u)) (cexp (-P x) * (-(-f x))) x :=
      ((hPd x hx).neg).cexp
    have h := hζ.mul hE
    refine h.congr_deriv ?_
    have hA := producerA_vonMangoldt_eq hRH hW (z := (x : ℂ) + t * I) (by simpa using hx)
      (by simpa using ht)
    have hne := riemannZeta_ne_zero_of_half_lt hRH (z := (x : ℂ) + t * I) (by simpa using hx) hm.2
    simp only [hf, neg_neg]
    rw [hA]
    field_simp
    ring
  -- constancy on `[σ, 2]`
  have hσ2 : σ ≤ 2 ∨ 2 < σ := le_or_gt σ 2
  have hg2 : g 2 = 1 := by
    have h2 : P 2 = canonicalEulerLogZeta ((2 : ℂ) + t * I) := by
      simp only [hP]
      rw [producerLogZeta_eq_LSeries hW (by norm_num) t, lamLogC_vonMangoldt]
      push_cast
      rfl
    have hz : riemannZeta ((2 : ℂ) + t * I) = cexp (P 2) := by
      rw [h2, exp_canonicalEulerLogZeta_eq_riemannZeta (by simp)]
    simp only [hg]
    push_cast
    rw [hz, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hconst : g σ = g 2 := by
    have hcont : ∀ a b : ℝ, 1 / 2 < a → ContinuousOn g (Icc a b) := fun a b ha =>
      fun x hx => (hgd x (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hder : ∀ a b : ℝ, 1 / 2 < a → ∀ x ∈ Ico a b, HasDerivWithinAt g 0 (Ici x) x :=
      fun a b ha x hx => (hgd x (by linarith [hx.1])).hasDerivWithinAt
    rcases hσ2 with h | h
    · exact (constant_of_has_deriv_right_zero (hcont σ 2 hσ) (hder σ 2 hσ) 2
        ⟨h, le_rfl⟩).symm
    · exact constant_of_has_deriv_right_zero (hcont 2 σ (by norm_num)) (hder 2 σ (by norm_num))
        σ ⟨h.le, le_rfl⟩
  have h1 : riemannZeta ((σ : ℂ) + t * I) * cexp (-P σ) = 1 := by
    have := hconst.trans hg2
    simpa [hg] using this
  calc riemannZeta ((σ : ℂ) + t * I)
      = riemannZeta ((σ : ℂ) + t * I) * cexp (-P σ) * cexp (P σ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = cexp (producerLogZeta hW σ t) := by rw [h1, one_mul]

/-- **Littlewood's theorem from RH, through the Weil cone.**  Under RH there are `C`, `T₀` with
`|ζ(σ + it)| ≤ exp(C log|t| / log log|t|)` for `½ ≤ σ ≤ 2` and `|t| ≥ T₀`. -/
theorem exists_norm_riemannZeta_le_littlewood_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C T₀ : ℝ, ∀ σ t : ℝ, T₀ ≤ |t| → 1 / 2 ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
        Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) := by
  have hW : WeilPositiveFull vonMangoldtReal :=
    RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  obtain ⟨C, T₀, hC⟩ := exists_re_producerLogZeta_le_littlewood hW (κ := 1) zero_le_one
    (fun n _ => by
      rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log)
  refine ⟨C, max T₀ 1, fun σ t ht hσ hσ2 => ?_⟩
  have hT : T₀ ≤ |t| := (le_max_left _ _).trans ht
  have ht0 : t ≠ 0 := fun h => by
    have := (le_max_right T₀ 1).trans ht
    rw [h, abs_zero] at this
    linarith
  set B : ℝ := Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) with hB
  have hopen : ∀ σ' : ℝ, 1 / 2 < σ' → σ' ≤ 2 → ‖riemannZeta ((σ' : ℂ) + t * I)‖ ≤ B := by
    intro σ' h1 h2
    rw [riemannZeta_eq_cexp_producerLogZeta hRH hW h1 ht0, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hC σ' t hT h1 h2)
  rcases hσ.lt_or_eq with h | h
  · exact hopen σ h hσ2
  · -- the critical line, by continuity from the right
    subst h
    have hne : ((1 / 2 : ℝ) : ℂ) + t * I ≠ 1 := fun h1 => ht0 (by
      have := congrArg Complex.im h1
      simpa using this)
    have hlin : Continuous fun σ' : ℝ => (σ' : ℂ) + t * I := by fun_prop
    have hcont : ContinuousAt (fun σ' : ℝ => ‖riemannZeta ((σ' : ℂ) + t * I)‖) (1 / 2) :=
      (ContinuousAt.comp (g := riemannZeta) (f := fun σ' : ℝ => (σ' : ℂ) + t * I) (x := 1 / 2)
        (differentiableAt_riemannZeta hne).continuousAt hlin.continuousAt).norm
    have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2)))
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 2)] with σ' hσ'
    exact hopen σ' hσ'.1 hσ'.2.le

/-- **Soundararajan's inequality for `ζ` from RH.**  Under RH, for `t ≠ 0`, `L > 0` and
`½ < σ ≤ σ₀ ≤ 2` with `λ = (σ₀ − ½)L` satisfying `e^{−λ} ≤ λ`:
`log|ζ(σ + it)| ≤ Re D_L(σ₀ + it)/L + Re U(σ₀ + it)/L + ∫_σ^{σ₀} Re U + (2Σ Λ(n)/n² + ε_L)/L`. -/
theorem log_norm_riemannZeta_le_soundararajan (hRH : RiemannHypothesis) {σ σ₀ t L : ℝ}
    (hσ : 1 / 2 < σ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ 2) (ht : t ≠ 0) (hL : 0 < L)
    (hlam : Real.exp (-((σ₀ - 1 / 2) * L)) ≤ (σ₀ - 1 / 2) * L) :
    Real.log ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (producerPoly vonMangoldtReal L ((σ₀ : ℂ) + t * I)).re / L +
        (archU ((σ₀ : ℂ) + t * I)).re / L + (∫ u in σ..σ₀, (archU ((u : ℂ) + t * I)).re) +
        (2 * (∑' n : ℕ, |vonMangoldtReal n| / (n : ℝ) ^ (2 : ℝ)) +
          (Real.exp ((1 - σ₀) * L) + Real.exp (-σ₀ * L) * (1 + (1 - Real.exp (-2 * L))⁻¹)) /
            (L * t ^ 2)) / L := by
  have hW : WeilPositiveFull vonMangoldtReal :=
    RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  rw [riemannZeta_eq_cexp_producerLogZeta hRH hW hσ ht, Complex.norm_exp, Real.log_exp]
  exact re_producerLogZeta_le hW hσ hσσ₀ hσ₀ ht hL hlam

end RHTower.WeilSpectral

end
