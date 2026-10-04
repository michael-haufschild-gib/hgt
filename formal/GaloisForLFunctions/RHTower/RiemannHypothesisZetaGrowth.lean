import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import GaloisForLFunctions.RHTower.ZetaChiLineSharp
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog

/-!
# Growth of `ζ` and `1/ζ` under the Riemann hypothesis

**Right of the critical line** (`exists_norm_riemannZeta_two_sided`).  Under RH, for
`0 < δ < 1/2` and `ε > 0` there is `T₀` with

`(|t| + 3)^{−ε} ≤ |ζ(σ + it)| ≤ (|t| + 3)^ε`   for `1/2 + δ ≤ σ ≤ 5/2`, `|t| ≥ T₀`.

Under RH the von Mangoldt weights are full-cone Weil-positive, and the producer Lindelöf bound
(`exists_producerZeta_subpolynomial_of_weilPositiveFull`) gives a branch `g` of
`Σ Λ(n) n^{−s}/log n` on the disc `B(3 + it, 5/2 − δ/4)` with `(|t|+3)^{∓ε}` bounds on `e^g`.  On
`Re s > 1` that series is `log ζ`, so `e^g = ζ` on the disc by the identity theorem.

**Left of the critical line** (`exists_norm_riemannZeta_left_le`).  For `0 < σ < 1/2`,
`|ζ(σ + it)| ≤ C |t|^{1/2 − σ} (|t| + 3)^ε` for `|t| ≥ T₀`: the functional equation
`ζ(s) = χ(s) ζ(1 − s)`, Titchmarsh's bound `|χ(σ + it)| ≤ C |t|^{1/2 − σ}`, and the first bound at
`1 − σ > 1/2`.
-/

open Complex Metric Filter Topology Set

noncomputable section

namespace RHTower.ZetaGrowth

/-- The coefficients `Λ(n)/log n` of the producer for the von Mangoldt weights. -/
theorem logZetaCoeff_vonMangoldt :
    logZetaCoeff (fun n => if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) =
      eulerLogDirichletCoeff := by
  funext n
  unfold logZetaCoeff eulerLogDirichletCoeff
  simp only
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, Complex.ofReal_div, Complex.natCast_log]
  · have : ArithmeticFunction.vonMangoldt n = 0 := by interval_cases n <;> simp
    rw [if_neg hn, this]; simp

/-- **Two-sided Lindelöf bound right of the critical line under RH.** -/
theorem exists_norm_riemannZeta_two_sided (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
      (|t| + 3) ^ (-ε) ≤ ‖riemannZeta ((σ : ℂ) + t * I)‖ ∧
        ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ (|t| + 3) ^ ε := by
  have hW := weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  obtain ⟨T₀, hT₀⟩ := exists_producerZeta_subpolynomial_of_weilPositiveFull hW hδ hδ1 hε
  refine ⟨max T₀ 6, fun t ht σ hσ1 hσ2 => ?_⟩
  obtain ⟨g, hgd, hgeq, hgb⟩ := hT₀ t (le_trans (le_max_left _ _) ht)
  set B : Set ℂ := ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4) with hB
  have ht6 : 6 ≤ |t| := le_trans (le_max_right _ _) ht
  have hone : (1 : ℂ) ∉ B := by
    intro h
    rw [hB, mem_ball, Complex.dist_eq] at h
    have hi := Complex.abs_im_le_norm ((1 : ℂ) - ((3 : ℂ) + t * I))
    simp at hi
    linarith
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball _ _).isPreconnected
  have hζd : DifferentiableOn ℂ riemannZeta B := fun z hz =>
    (differentiableAt_riemannZeta fun h => hone (h ▸ hz)).differentiableWithinAt
  have hcen : (3 : ℂ) + t * I ∈ B := mem_ball_self (by linarith)
  have hev : riemannZeta =ᶠ[𝓝 ((3 : ℂ) + t * I)] fun z => Complex.exp (g z) := by
    have hre : ∀ᶠ z in 𝓝 ((3 : ℂ) + t * I), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hre, hBo.mem_nhds hcen] with z hz hzB
    rw [hgeq z hzB hz, logZetaCoeff_vonMangoldt]
    exact (exp_canonicalEulerLogZeta_eq_riemannZeta hz).symm
  have heq := (hζd.analyticOnNhd hBo).eqOn_of_preconnected_of_eventuallyEq
    ((hgd.cexp).analyticOnNhd hBo) hBc hcen hev
  have hmem : (σ : ℂ) + t * I ∈ B := by
    rw [hB, mem_ball, Complex.dist_eq]
    have : (σ : ℂ) + t * I - ((3 : ℂ) + t * I) = ((σ - 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  rw [heq hmem]
  exact hgb σ hσ1 hσ2

theorem gammaR_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have := congrArg Complex.im hn
  simp at this
  exact hs this

/-- **Reflected growth left of the critical line under RH.** -/
theorem exists_norm_riemannZeta_left_le (hRH : RiemannHypothesis) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ C * |t| ^ (1 / 2 - σ) * (|t| + 3) ^ ε := by
  obtain ⟨C, hC, hχ⟩ := exists_norm_zetaChi_line_le hσ1
  obtain ⟨T₀, hT₀⟩ := exists_norm_riemannZeta_two_sided hRH (δ := 1 / 2 - σ) (by linarith)
    (by linarith) hε
  refine ⟨C, max T₀ 2, hC, fun t ht => ?_⟩
  have ht2 : 2 ≤ |t| := le_trans (le_max_right _ _) ht
  have hT : T₀ ≤ |-t| := by rw [abs_neg]; exact le_trans (le_max_left _ _) ht
  set s : ℂ := (σ : ℂ) + t * I with hs
  have him : s.im ≠ 0 := by
    rw [hs]; simp; intro h; rw [h] at ht2; simp at ht2; linarith
  have hs0 : s ≠ 0 := fun h => him (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h => him (by rw [h]; simp)
  have hG : Gammaℝ (1 - s) ≠ 0 := gammaR_ne_zero_of_im_ne_zero (by simpa using him)
  rw [zeta_eq_zetaChi_mul hs0 hs1 hG, norm_mul]
  have h1s : 1 - s = (((1 - σ : ℝ) : ℂ)) + ((-t : ℝ) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hz := (hT₀ (-t) hT (1 - σ) (by linarith) (by linarith)).2
  rw [abs_neg] at hz
  rw [h1s]
  calc ‖zetaChi s‖ * ‖riemannZeta (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖
      ≤ (C * |t| ^ (1 / 2 - σ)) * (|t| + 3) ^ ε :=
        mul_le_mul (hχ t ht2) hz (norm_nonneg _) (by positivity)
    _ = C * |t| ^ (1 / 2 - σ) * (|t| + 3) ^ ε := by ring

end RHTower.ZetaGrowth
