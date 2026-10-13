import GaloisForLFunctions.RHTower.FiniteOffLineLandau
import GaloisForLFunctions.RHTower.WeilLagBandLimitedDichotomy

/-!
# One-sided lag bounds force positive configurations on-line

A configuration is a countable family of exponents `w_i ∈ ℂ` with `Re w_i ≤ B` and only finitely
many in each disc, carrying weights `a_i` with `Σ ‖a_i‖ < ∞`; its lag function is
`Φ(t) = Re Σ_i a_i e^{t w_i}`.

**Theorem** (`re_nonpos_of_lag_le`). If the weights are positive reals and `Φ(t) ≤ M` for every
`t ≥ s₀`, then `Re w_i ≤ 0` for every `i`.

**Theorem** (`re_nonpos_of_not_isMeagre`). The same holds as soon as the set of spacings `ℓ > 0`
whose progression `m ↦ Φ(mℓ)` is bounded above is not meagre.

**Theorem** (`re_nonpos_of_lagRe_le_upper`, `re_nonpos_of_abs_lagRe_le_upper`). For complex
weights, let the exponents be distinct with `Im w_i ≥ 0` (one exponent per conjugate pair) and the
weights nonzero. A one-sided bound on a half-line forces `Re w_i ≤ 0` when `Re a_i > 0` at the real
exponents; a two-sided bound does so when only `Re a_i ≠ 0` there. The non-meagre versions are
`re_nonpos_of_not_isMeagre_upper` and `re_nonpos_of_not_isMeagre_abs_upper`.

So for every locally finite configuration a bound along a non-meagre set of progressions is rigid,
whereas a bound along almost every progression is not
(`AlmostEverySpacing.exists_lag_configuration_ae_spacing_bddAbove`), and without local finiteness a
bound on a whole half-line is not (`exists_positive_lag_configuration_bandLimited`).

**Proofs.** *Real pole* (`false_of_realPole`). Let `φ ≤ M` on `[0, ∞)` have Laplace transform `Λ`
analytic at every real `t > p > 0`, with `Re Λ(σ)` unbounded above on `(p, ∞)`. The transform of
`(M − φ)₊ du + du` has abscissa `c ≥ 0` and equals `(M+1)/s − Λ(s)` on `(max(c, p), ∞)` by the
identity theorem. If `c ≤ p`, the left side is `≥ 0` while `(M+1)/σ − Re Λ(σ)` is unbounded below;
if `c > p`, the right side is analytic at `c`, against Landau's theorem.

*Real exponents* (`re_nonpos_of_real`). If `Re a_i > 0` at every real exponent `w_i > 0`, the
transform of `Φ` is `½ Σ_i (a_i/(s − w_i) + ā_i/(s − w̄_i))`, analytic off the closed set of
exponents. At the largest real exponent `p = w_j > 0` its real part is at least
`Re a_j/(σ − p) − 2Σ‖a_i‖/η`, `η` the distance from `p` to the other exponents.

*Twist* (`re_nonpos_of_lag_le`). If `Re w_j > 0`, then `Φ(t)(1 + cos(t Im w_j))` is the lag function
of the configuration `{w_i, w_i ± i Im w_j}` with positive weights. It is bounded above, and it has
the real exponent `w_j − i Im w_j = Re w_j > 0`.

*Complex weights.* Twist by `1 + cos(t Im w_k + arg a_k)` at the rightmost exponent `w_k` of the
height `Im w_j`: the twisted real exponent `Re w_k` is then the largest one and carries the positive
weight `|a_k| e^{s₁ Re w_k}/2`. A two-sided bound handles real exponents of either sign through `±Φ`.

*Baire* (`exists_halfLine_le_of_not_isMeagre`). The level sets `{ℓ ≥ 1/(k+1) | ∀ m, Φ(mℓ) ≤ M}` are closed.
A non-meagre union of them has a level set with an interior point, hence an interval `(c, d)` of
spacings, and the products `mℓ` cover a half-line.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.LocallyFiniteExponentialSumRigidity

namespace RHTower.OneSidedConfiguration

noncomputable section

/-! ## Landau's theorem across a real pole -/

/-- **A real pole with unbounded real part obstructs a one-sided bound.** -/
theorem false_of_realPole {φ : ℝ → ℝ} (hφ : Measurable φ) {K M : ℝ}
    (hK : ∀ u, 0 < u → |φ u| ≤ K * Real.exp (u / 2)) (hM : ∀ u, 0 ≤ u → φ u ≤ M)
    {Λ : ℂ → ℂ}
    (hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * Complex.exp (-s * (u : ℂ)) = Λ s)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hΛ : ∀ t : ℝ, p < t → AnalyticAt ℂ Λ t)
    (hblow : ∀ N : ℝ, ∃ σ : ℝ, p < σ ∧ N ≤ (Λ σ).re) : False := by
  have hM' : ∀ u, 0 ≤ u → φ u ≤ M * Real.exp (0 * u) := fun u hu => by
    simpa using hM u hu
  obtain ⟨hc, hc0⟩ := isAbscissa_landau (M := M) (a := 0) hφ hK (by norm_num)
  set c : ℝ := sInf {σ : ℝ | laplaceMass (landauMeasure φ 0 M) σ ≠ ⊤} with hcdef
  have hc34 : c ≤ 3 / 4 := by
    refine csInf_le ⟨0, fun σ hσ => ?_⟩ ?_
    · by_contra hlt
      apply hσ
      rw [laplaceMass_landau_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]),
        add_top]
    · show laplaceMass (landauMeasure φ 0 M) (3 / 4) ≠ ⊤
      rw [laplaceMass_landau_eq]
      exact ENNReal.add_ne_top.mpr ⟨laplaceMass_landauDensity_ne_top hφ hK (by norm_num)
        (by norm_num), laplaceMass_volume_ne_top (by norm_num)⟩
  set H : ℂ → ℂ := fun z => ((M : ℂ) + 1) / (z - ((0 : ℝ) : ℂ)) - Λ z with hH
  have hHan : ∀ t : ℝ, p < t → AnalyticAt ℂ H t := fun t ht =>
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (show (t : ℂ) - ((0 : ℝ) : ℂ) ≠ 0 by
        rw [Complex.ofReal_zero, sub_zero]; exact_mod_cast (hp0.trans ht).ne')).sub (hΛ t ht)
  have hT1 : max c p < 1 := max_lt (by linarith) hp1
  have heq : ∀ σ : ℝ, max c p < σ → H σ = (laplaceReal (landauMeasure φ 0 M) σ : ℂ) := by
    intro σ hσ
    have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hTdiff : DifferentiableOn ℂ (complexLaplace (landauMeasure φ 0 M)) {z : ℂ | c < z.re} :=
      fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
    have hLa : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (landauMeasure φ 0 M) (t : ℂ))
        (Ioi (max c p)) := by
      intro t ht
      have htc : c < t := lt_of_le_of_lt (le_max_left _ _) ht
      have h1 : AnalyticAt ℂ (complexLaplace (landauMeasure φ 0 M)) (t : ℂ) :=
        hTdiff.analyticAt (hV.mem_nhds (by simpa using htc))
      exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    have hHt : AnalyticOnNhd ℝ (fun t : ℝ => H (t : ℂ)) (Ioi (max c p)) := fun t ht =>
      (hHan t (lt_of_le_of_lt (le_max_right _ _) ht)).restrictScalars.comp
        (Complex.ofRealCLM.analyticAt t)
    have hfg : (fun t : ℝ => complexLaplace (landauMeasure φ 0 M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
        (fun t : ℝ => H (t : ℂ)) := by
      refine Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
      exact complexLaplace_landau_eq hφ hK (by norm_num) hM' hΛφ (by simpa using ht.1)
    have h := hLa.eqOn_of_preconnected_of_eventuallyEq hHt isPreconnected_Ioi hT1 hfg
    exact (h (show σ ∈ Ioi (max c p) from hσ)).symm.trans (complexLaplace_ofReal _ σ)
  rcases le_or_gt c p with hcp | hpc
  · obtain ⟨σ, hpσ, hN⟩ := hblow ((|M| + 1) / p + 1)
    have hσ0 : 0 < σ := hp0.trans hpσ
    have h := congrArg Complex.re (heq σ (max_lt (hcp.trans_lt hpσ) hpσ))
    have hre : (H σ).re = (M + 1) / σ - (Λ σ).re := by
      have : ((M : ℂ) + 1) / ((σ : ℂ) - ((0 : ℝ) : ℂ)) = (((M + 1) / σ : ℝ) : ℂ) := by
        push_cast; ring
      simp only [hH, Complex.sub_re, this, Complex.ofReal_re]
    have hL0 : 0 ≤ laplaceReal (landauMeasure φ 0 M) σ :=
      integral_nonneg fun u => (Real.exp_pos _).le
    have hbd : (M + 1) / σ ≤ (|M| + 1) / p :=
      (div_le_div_of_nonneg_right (by linarith [le_abs_self M]) hσ0.le).trans
        (div_le_div_of_nonneg_left (by positivity) hp0 hpσ.le)
    rw [Complex.ofReal_re, hre] at h
    linarith
  · obtain ⟨d, hd, hball⟩ :=
      Metric.eventually_nhds_iff_ball.mp (hHan c hpc).eventually_analyticAt
    exact false_of_analyticAt_abscissa hc hd (Φ := H) (fun z hz => hball z hz)
      fun σ hσc _ => heq σ (max_lt hσc (hpc.trans hσc))

/-! ## Configurations and their Laplace transforms -/

variable {ι : Type*}

/-- The lag function `Φ(t) = Re Σ_i a_i e^{t w_i}`. -/
def lagRe (a w : ι → ℂ) (t : ℝ) : ℝ := (∑' i, a i * cexp (t * w i)).re

theorem norm_term_le {a w : ι → ℂ} {B : ℝ} (hB : ∀ i, (w i).re ≤ B) {t : ℝ} (ht : 0 ≤ t)
    (i : ι) : ‖a i * cexp (t * w i)‖ ≤ ‖a i‖ * Real.exp (t * B) := by
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have : ((t : ℂ) * w i).re = t * (w i).re := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left (hB i) ht

theorem summable_term {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {t : ℝ} (ht : 0 ≤ t) : Summable fun i => a i * cexp (t * w i) :=
  Summable.of_norm_bounded (ha.mul_right _) (norm_term_le hB ht)

theorem norm_lagSum_le {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑' i, a i * cexp (t * w i)‖ ≤ (∑' i, ‖a i‖) * Real.exp (t * B) := by
  refine (norm_tsum_le_tsum_norm (summable_term ha hB ht).norm).trans ?_
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum (norm_term_le hB ht) (summable_term ha hB ht).norm (ha.mul_right _)

/-- `t ↦ Σ_i a_i e^{max(t,0) w_i}` is continuous. -/
theorem continuous_lagSum_max {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) :
    Continuous fun t : ℝ => ∑' i, a i * cexp ((max t 0 : ℝ) * w i) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have hB' : ∀ i, (w i).re ≤ |B| := fun i => (hB i).trans (le_abs_self B)
  have hloc : ContinuousOn (fun t : ℝ => ∑' i, a i * cexp ((max t 0 : ℝ) * w i))
      (Icc (t₀ - 1) (t₀ + 1)) := by
    refine continuousOn_tsum (fun i => (continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_id.max continuous_const)).mul
        continuous_const))).continuousOn)
      (ha.mul_right (Real.exp ((|t₀| + 1) * |B|))) fun i t ht => ?_
    refine (norm_term_le hB' (le_max_right t 0) i).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg B)
    have h1 := abs_sub_abs_le_abs_sub t t₀
    have h2 : |t - t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (max_le (le_abs_self t) (abs_nonneg t)).trans (by linarith)
  exact (hloc t₀ ⟨by linarith, by linarith⟩).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

theorem integrableOn_lagSum_mul_cexp {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {s : ℂ} (hs : B < s.re) :
    IntegrableOn (fun u : ℝ => (∑' i, a i * cexp (u * w i)) * cexp (-s * u)) (Ioi 0) := by
  have hc : Continuous fun u : ℝ => (∑' i, a i * cexp ((max u 0 : ℝ) * w i)) * cexp (-s * u) :=
    (continuous_lagSum_max ha hB).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hmaj : IntegrableOn (fun u : ℝ => (∑' i, ‖a i‖) * Real.exp (-(s.re - B) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  refine IntegrableOn.congr_fun (hmaj.mono' hc.aestronglyMeasurable ?_) (fun u hu => ?_)
    measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [max_eq_left (le_of_lt hu), norm_mul, norm_cexp_neg_mul]
    calc ‖∑' i, a i * cexp (u * w i)‖ * Real.exp (-s.re * u)
        ≤ ((∑' i, ‖a i‖) * Real.exp (u * B)) * Real.exp (-s.re * u) :=
          mul_le_mul_of_nonneg_right (norm_lagSum_le ha hB (le_of_lt hu)) (Real.exp_pos _).le
      _ = (∑' i, ‖a i‖) * Real.exp (-(s.re - B) * u) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  · simp only [max_eq_left (le_of_lt (show (0:ℝ) < u from hu))]

/-- For `Re s > B`, `∫_0^∞ (Σ_i a_i e^{u w_i}) e^{−su} du = Σ_i a_i/(s − w_i)`. -/
theorem integral_lagSum_mul_cexp [Countable ι] {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    {B : ℝ} (hB : ∀ i, (w i).re ≤ B) {s : ℂ} (hs : B < s.re) :
    ∫ u in Ioi (0:ℝ), (∑' i, a i * cexp (u * w i)) * cexp (-s * u) = cauchySeries w a s := by
  have hre : ∀ i, (-(s - w i)).re < 0 := fun i => by simp; linarith [hB i]
  have hterm : ∀ i, a i / (s - w i) = ∫ u in Ioi (0 : ℝ), a i * cexp (-(s - w i) * u) := by
    intro i
    have hne : s - w i ≠ 0 := fun h => by have := hre i; rw [h] at this; simp at this
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre i) 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  have hint : ∀ i, Integrable (fun u : ℝ => a i * cexp (-(s - w i) * u))
      (volume.restrict (Ioi 0)) :=
    fun i => (integrableOn_exp_mul_complex_Ioi (hre i) 0).const_mul _
  have hpos : ∀ i, 0 < s.re - (w i).re := fun i => by linarith [hB i]
  have hnorm : ∀ i, ∫ u in Ioi (0 : ℝ), ‖a i * cexp (-(s - w i) * u)‖ =
      ‖a i‖ / (s.re - (w i).re) := by
    intro i
    have hfun : (fun u : ℝ => ‖a i * cexp (-(s - w i) * u)‖) =
        fun u => ‖a i‖ * Real.exp (-(s.re - (w i).re) * u) := by
      funext u
      rw [norm_mul, Complex.norm_exp]
      congr 2
      simp
    rw [hfun, integral_const_mul, integral_exp_mul_Ioi (by linarith [hpos i]) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hsum : Summable fun i => ∫ u in Ioi (0 : ℝ), ‖a i * cexp (-(s - w i) * u)‖ := by
    simp_rw [hnorm]
    have hη : 0 < s.re - B := by linarith
    exact Summable.of_nonneg_of_le (fun i => div_nonneg (norm_nonneg _) (hpos i).le)
      (fun i => div_le_div_of_nonneg_left (norm_nonneg _) hη (by linarith [hB i]))
      (ha.div_const _)
  unfold cauchySeries
  simp_rw [hterm]
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [← tsum_mul_right]
  refine tsum_congr fun i => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- The Laplace transform of the lag function: `½ Σ_i (a_i/(s − w_i) + ā_i/(s − w̄_i))`. -/
def pairSeries (a w : ι → ℂ) (s : ℂ) : ℂ :=
  (cauchySeries w a s + cauchySeries (fun i => conj (w i)) (fun i => conj (a i)) s) / 2

theorem ofReal_lagRe (a w : ι → ℂ) (t : ℝ) :
    (lagRe a w t : ℂ) = ((∑' i, a i * cexp (t * w i)) +
      ∑' i, conj (a i) * cexp (t * conj (w i))) / 2 := by
  rw [lagRe, Complex.re_eq_add_conj, Complex.conj_tsum]
  congr 2
  refine tsum_congr fun i => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem integral_lagRe_mul_cexp [Countable ι] {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    {B : ℝ} (hB : ∀ i, (w i).re ≤ B) {s : ℂ} (hs : B < s.re) :
    ∫ u in Ioi (0:ℝ), (lagRe a w u : ℂ) * cexp (-s * u) = pairSeries a w s := by
  have ha' : Summable fun i => ‖conj (a i)‖ := by simpa using ha
  have hB' : ∀ i, (conj (w i)).re ≤ B := fun i => by simpa using hB i
  have h1 := integrableOn_lagSum_mul_cexp ha hB hs
  have h2 := integrableOn_lagSum_mul_cexp ha' hB' hs
  have hpt : ∀ u : ℝ, (lagRe a w u : ℂ) * cexp (-s * u) =
      ((∑' i, a i * cexp (u * w i)) * cexp (-s * u) +
        (∑' i, conj (a i) * cexp (u * conj (w i))) * cexp (-s * u)) / 2 := fun u => by
    rw [ofReal_lagRe]; ring
  simp_rw [hpt]
  rw [integral_div, integral_add h1 h2, integral_lagSum_mul_cexp ha hB hs,
    integral_lagSum_mul_cexp ha' hB' hs, pairSeries]

theorem analyticAt_pairSeries {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {z : ℂ} (hz : ∀ i, w i ≠ z)
    (hz' : ∀ i, conj (w i) ≠ z) : AnalyticAt ℂ (pairSeries a w) z := by
  have hfin' : ∀ R : ℝ, {i | ‖conj (w i)‖ ≤ R}.Finite := by simpa using hfin
  have ha' : Summable fun i => ‖conj (a i)‖ := by simpa using ha
  have h1 : AnalyticAt ℂ (cauchySeries w a) z :=
    (differentiableOn_cauchySeries hfin ha).analyticAt
      ((isClosed_range hfin).isOpen_compl.mem_nhds fun ⟨i, hi⟩ => hz i hi)
  have h2 : AnalyticAt ℂ (cauchySeries (fun i => conj (w i)) (fun i => conj (a i))) z :=
    (differentiableOn_cauchySeries hfin' ha').analyticAt
      ((isClosed_range hfin').isOpen_compl.mem_nhds fun ⟨i, hi⟩ => hz' i hi)
  exact (h1.add h2).div analyticAt_const two_ne_zero

/-! ## The blow-up at a real exponent -/

/-- Near a real exponent `p = w_j` whose weights have nonnegative real part, the real part of the
Cauchy series is at least `Re b_j/(σ − p) − Σ‖b_i‖/(η/2)`. -/
theorem re_cauchySeries_ge {w b : ι → ℂ} (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite)
    (hb : Summable fun i => ‖b i‖) {p : ℝ} {j : ι} (hj : w j = p)
    (hpos : ∀ i, w i = p → 0 ≤ (b i).re) {η : ℝ} (hη : 0 < η)
    (hsep : ∀ i, w i ≠ p → η ≤ dist (p : ℂ) (w i)) {σ : ℝ} (hσ : p < σ)
    (hση : σ < p + η / 2) :
    (b j).re / (σ - p) - (∑' i, ‖b i‖) / (η / 2) ≤ (cauchySeries w b σ).re := by
  classical
  have hη2 : 0 < η / 2 := half_pos hη
  have hσp : 0 < σ - p := sub_pos.mpr hσ
  have hfar : ∀ i, w i ≠ p → η / 2 ≤ ‖(σ : ℂ) - w i‖ := by
    intro i hi
    have h1 := hsep i hi
    have h2 := dist_triangle (p : ℂ) σ (w i)
    have h3 : dist (p : ℂ) (σ : ℂ) = σ - p := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm, abs_of_pos hσp]
    rw [h3] at h2
    rw [← Complex.dist_eq]
    linarith
  have hnot : (σ : ℂ) ∉ range w := by
    rintro ⟨i, hi⟩
    by_cases hip : w i = p
    · rw [hip] at hi; exact hσ.ne (Complex.ofReal_injective hi)
    · have := hfar i hip; rw [hi, sub_self, norm_zero] at this; linarith
  have hs := summable_cauchy hfin hb hnot
  have hpt : ∀ i, (if i = j then (b j).re / (σ - p) else 0) - ‖b i‖ / (η / 2) ≤
      (b i / ((σ : ℂ) - w i)).re := by
    intro i
    by_cases hip : w i = p
    · have hval : (b i / ((σ : ℂ) - w i)).re = (b i).re / (σ - p) := by
        rw [hip, ← Complex.ofReal_sub, Complex.div_ofReal_re]
      rw [hval]
      have hq : 0 ≤ (b i).re / (σ - p) := div_nonneg (hpos i hip) hσp.le
      have hn : 0 ≤ ‖b i‖ / (η / 2) := div_nonneg (norm_nonneg _) hη2.le
      split_ifs with hij
      · subst hij; linarith
      · linarith
    · have hij : i ≠ j := fun h => hip (h ▸ hj)
      rw [if_neg hij, zero_sub]
      have h1 := norm_div_sub_le hη2 (b := b i) (hfar i hip)
      have h2 := Complex.abs_re_le_norm (b i / ((σ : ℂ) - w i))
      have h3 := neg_abs_le (b i / ((σ : ℂ) - w i)).re
      linarith
  have hsumL : Summable fun i => (if i = j then (b j).re / (σ - p) else 0) - ‖b i‖ / (η / 2) :=
    (hasSum_ite_eq j _).summable.sub (hb.div_const _)
  have hle := Summable.tsum_le_tsum hpt hsumL (Complex.hasSum_re hs.hasSum).summable
  rw [Summable.tsum_sub (hasSum_ite_eq j _).summable (hb.div_const _), tsum_ite_eq,
    tsum_div_const] at hle
  rw [cauchySeries, Complex.re_tsum hs]
  exact hle

/-- **The pair series blows up at a real exponent with positive weight.** -/
theorem exists_re_pairSeries_ge {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {p : ℝ} {j : ι} (hj : w j = p)
    (hj0 : 0 < (a j).re) (hpos : ∀ i, w i = p → 0 ≤ (a i).re) (N : ℝ) :
    ∃ σ : ℝ, p < σ ∧ N ≤ (pairSeries a w σ).re := by
  have hfin' : ∀ R : ℝ, {i | ‖conj (w i)‖ ≤ R}.Finite := by simpa using hfin
  have ha' : Summable fun i => ‖conj (a i)‖ := by simpa using ha
  obtain ⟨η₁, hη₁, hs₁⟩ := exists_pos_le_dist hfin (p : ℂ)
  obtain ⟨η₂, hη₂, hs₂⟩ := exists_pos_le_dist hfin' (p : ℂ)
  have hη : 0 < min η₁ η₂ := lt_min hη₁ hη₂
  have hA0 : 0 ≤ ∑' i, ‖a i‖ := tsum_nonneg fun _ => norm_nonneg _
  set η := min η₁ η₂ with hηdef
  set A := ∑' i, ‖a i‖ with hAdef
  set K := |N| + A / (η / 2) + 1 with hK
  have hK0 : 0 < K := by positivity
  set t := min (η / 4) ((a j).re / K) with htdef
  have ht : 0 < t := lt_min (by positivity) (div_pos hj0 hK0)
  have htK : t * K ≤ (a j).re := (le_div_iff₀ hK0).mp (min_le_right _ _)
  have hKt : K ≤ (a j).re / t := by
    rw [le_div_iff₀ ht]; linarith [mul_comm t K]
  have hσ : p < p + t := by linarith
  have hση : p + t < p + η / 2 := by linarith [min_le_left (η / 4) ((a j).re / K)]
  have hsub : p + t - p = t := by ring
  have c1 := re_cauchySeries_ge hfin ha hj hpos hη
    (fun i hi => (min_le_left _ _).trans (hs₁ i hi)) hσ hση
  have hjc : conj (w j) = p := by rw [hj, Complex.conj_ofReal]
  have hposc : ∀ i, conj (w i) = p → 0 ≤ (conj (a i)).re := by
    intro i hi
    have : w i = p := by rw [← Complex.conj_conj (w i), hi, Complex.conj_ofReal]
    simpa using hpos i this
  have c2 := re_cauchySeries_ge hfin' ha' hjc hposc hη
    (fun i hi => (min_le_right _ _).trans (hs₂ i hi)) hσ hση
  have hnc : (∑' i, ‖conj (a i)‖) = A := by simp [hAdef]
  rw [Complex.conj_re, hnc, hsub] at c2
  rw [hsub] at c1
  refine ⟨p + t, hσ, ?_⟩
  have hre : (pairSeries a w ((p + t : ℝ) : ℂ)).re =
      ((cauchySeries w a ((p + t : ℝ) : ℂ)).re +
        (cauchySeries (fun i => conj (w i)) (fun i => conj (a i)) ((p + t : ℝ) : ℂ)).re) / 2 := by
    rw [pairSeries, Complex.div_ofNat_re, Complex.add_re]
  rw [hre]
  have hN : N ≤ |N| := le_abs_self N
  linarith

/-! ## Real exponents of a one-sided configuration -/

/-- At every maximal positive real exponent `w_k` the weight `a_k` has positive real part, and the
weights of the other indices with the same exponent have nonnegative real parts. -/
def MaxRealPositive (a w : ι → ℂ) : Prop :=
  ∀ k, (w k).im = 0 → 0 < (w k).re →
    (∀ i, (w i).im = 0 → 0 < (w i).re → (w i).re ≤ (w k).re) →
      0 < (a k).re ∧ ∀ i, w i = w k → 0 ≤ (a i).re

theorem maxRealPositive_of_pos {a w : ι → ℂ}
    (hpos : ∀ i, (w i).im = 0 → 0 < (w i).re → 0 < (a i).re) : MaxRealPositive a w :=
  fun k hk hk0 _ => ⟨hpos k hk hk0, fun i hi =>
    (hpos i (by rw [hi]; exact hk) (by rw [hi]; exact hk0)).le⟩

theorem re_nonpos_of_real_of_quarter [Countable ι] {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) (hB : ∀ i, (w i).re ≤ 1 / 4)
    (hmax : MaxRealPositive a w) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) : (w j).re ≤ 0 := by
  by_contra hj0
  replace hj0 := not_le.mp hj0
  have hPfin : {i | (w i).im = 0 ∧ 0 < (w i).re}.Finite := (hfin (1 / 4)).subset fun i hi => by
    have h1 := Complex.norm_le_abs_re_add_abs_im (w i)
    rw [hi.1, abs_zero, add_zero, abs_of_pos hi.2] at h1
    exact h1.trans (hB i)
  obtain ⟨k, hkP, hkmax⟩ := Set.exists_max_image {i | (w i).im = 0 ∧ 0 < (w i).re}
    (fun i => (w i).re) hPfin ⟨j, hj, hj0⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, (w k).re = p := ⟨_, rfl⟩
  have hwk : w k = p := Complex.ext (by simp [hp]) (by simp [hkP.1])
  have hp0 : 0 < p := hp ▸ hkP.2
  have hp1 : p < 1 := by linarith [hB k]
  set φ : ℝ → ℝ := fun u => (∑' i, a i * cexp ((max u 0 : ℝ) * w i)).re with hφdef
  have hφc : Continuous φ := Complex.continuous_re.comp (continuous_lagSum_max ha hB)
  have hφpos : ∀ u, 0 ≤ u → φ u = lagRe a w u := fun u hu => by
    simp only [hφdef, max_eq_left hu, lagRe]
  have hK : ∀ u, 0 < u → |φ u| ≤ (∑' i, ‖a i‖) * Real.exp (u / 2) := by
    intro u hu
    rw [hφpos u hu.le, lagRe]
    refine (Complex.abs_re_le_norm _).trans ((norm_lagSum_le ha hB hu.le).trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (tsum_nonneg fun _ => norm_nonneg _)
  have hΛφ : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ u in Ioi (0:ℝ), (φ u : ℂ) * cexp (-s * (u : ℂ)) = pairSeries a w s := by
    intro s hs
    rw [← integral_lagRe_mul_cexp ha hB (by linarith : (1 / 4 : ℝ) < s.re)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hφpos u (le_of_lt hu)]
  have hΛ : ∀ t : ℝ, p < t → AnalyticAt ℂ (pairSeries a w) t := by
    intro t ht
    have hne : ∀ i, w i ≠ t := by
      intro i hi
      have him : (w i).im = 0 := by rw [hi]; simp
      have hre : (w i).re = t := by rw [hi]; simp
      have hle : (w i).re ≤ (w k).re := hkmax i ⟨him, by rw [hre]; linarith⟩
      linarith
    refine analyticAt_pairSeries ha hfin hne fun i hi => hne i ?_
    rw [← Complex.conj_conj (w i), hi, Complex.conj_ofReal]
  obtain ⟨hk0, hkF⟩ := hmax k hkP.1 hkP.2 fun i hi hi0 => hkmax i ⟨hi, hi0⟩
  have hposp : ∀ i, w i = p → 0 ≤ (a i).re := fun i hi => hkF i (by rw [hi, hwk])
  exact false_of_realPole hφc.measurable hK (fun u hu => by rw [hφpos u hu]; exact hM u hu)
    hΛφ hp0 hp1 hΛ (exists_re_pairSeries_ge ha hfin hwk hk0 hposp)

/-- **Real exponents of a one-sided configuration are nonpositive.** If `Re w_i ≤ B`, the
exponents are locally finite, the weights at a maximal real exponent `w_k > 0` have nonnegative real
parts with `Re a_k > 0`, and `Φ(t) ≤ M` for `t ≥ 0`, then every real exponent is `≤ 0`. -/
theorem re_nonpos_of_real [Countable ι] {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖)
    (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ} (hB : ∀ i, (w i).re ≤ B)
    (hmax : MaxRealPositive a w) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → lagRe a w t ≤ M) (j : ι) (hj : (w j).im = 0) : (w j).re ≤ 0 := by
  set l : ℝ := 4 * (|B| + 1) with hl
  have hl0 : 0 < l := by positivity
  have key := re_nonpos_of_real_of_quarter (w := fun i => w i / l) ha ?_ ?_ ?_ (M := M) ?_ j ?_
  · rw [Complex.div_ofReal_re] at key
    by_contra h
    have := div_pos (lt_of_not_ge h) hl0
    linarith
  · intro R
    refine (hfin (R * l)).subset fun i hi => ?_
    simp only [mem_setOf_eq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0] at hi ⊢
    exact (div_le_iff₀ hl0).mp hi
  · intro i
    rw [Complex.div_ofReal_re, div_le_iff₀ hl0]
    linarith [hB i, le_abs_self B]
  · intro k hk hk0 hkmax
    have him : ∀ i, (w i / l).im = 0 ↔ (w i).im = 0 := fun i => by
      rw [Complex.div_ofReal_im, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right hl0.ne', Or.inl⟩
    have hre : ∀ i, (w i / l).re = (w i).re / l := fun i => Complex.div_ofReal_re _ _
    have hk0' : 0 < (w k).re := by
      rw [hre] at hk0; exact (div_pos_iff_of_pos_right hl0).mp hk0
    obtain ⟨h1, h2⟩ := hmax k ((him k).mp hk) hk0' fun i hi hi0 => by
      have := hkmax i ((him i).mpr hi) (by rw [hre]; exact div_pos hi0 hl0)
      rw [hre, hre] at this
      exact (div_le_div_iff_of_pos_right hl0).mp this
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    exact ⟨h1, fun i hi => h2 i ((div_left_inj' hl').mp hi)⟩
  · intro t ht
    have h := hM (t / l) (div_nonneg ht hl0.le)
    have heq : lagRe a (fun i => w i / l) t = lagRe a w (t / l) := by
      unfold lagRe
      congr 1
      refine tsum_congr fun i => ?_
      congr 2
      push_cast
      field_simp
    rw [heq]; exact h
  · rw [Complex.div_ofReal_im, hj, zero_div]

/-! ## The twist by `1 + cos(γt)` -/

/-- The shifts `0, iγ, −iγ` of the twisted configuration. -/
def twistShift (γ : ℝ) : Fin 3 → ℂ := ![0, I * γ, -(I * γ)]

/-- The weights `1, ½, ½` of the twisted configuration. -/
def twistWeight : Fin 3 → ℝ := ![1, 1 / 2, 1 / 2]

theorem twistWeight_pos (k : Fin 3) : 0 < twistWeight k := by
  fin_cases k <;> norm_num [twistWeight]

theorem twistWeight_le_one (k : Fin 3) : twistWeight k ≤ 1 := by
  fin_cases k <;> norm_num [twistWeight]

theorem re_twistShift (γ : ℝ) (k : Fin 3) : (twistShift γ k).re = 0 := by
  fin_cases k <;> simp [twistShift]

theorem norm_twistShift_le (γ : ℝ) (k : Fin 3) : ‖twistShift γ k‖ ≤ |γ| := by
  fin_cases k <;> simp [twistShift]

/-- `1 + ½e^{iγx} + ½e^{−iγx} = 1 + cos(γx)`. -/
theorem sum_twist (γ x : ℝ) :
    ∑ k : Fin 3, (twistWeight k : ℂ) * cexp (x * twistShift γ k) =
      ((1 + Real.cos (γ * x) : ℝ) : ℂ) := by
  rw [Fin.sum_univ_three]
  simp only [twistWeight, twistShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  rw [Complex.cos]
  have e1 : (x : ℂ) * (I * γ) = γ * x * I := by ring
  have e2 : (x : ℂ) * -(I * γ) = -(γ * x) * I := by ring
  rw [e1, e2, mul_zero, Complex.exp_zero]
  ring

/-- The exponents `w_i, w_i + iγ, w_i − iγ`. -/
def twistExp (γ : ℝ) (w : ι → ℂ) (q : Fin 3 × ι) : ℂ := w q.2 + twistShift γ q.1

/-- The weights `c_i·(1, ½, ½)·e^{s₁(w_i + shift)}` of the twisted configuration shifted by `s₁`. -/
def twistCoef (γ s₁ : ℝ) (c : ι → ℝ) (w : ι → ℂ) (q : Fin 3 × ι) : ℂ :=
  ((c q.2 * twistWeight q.1 : ℝ) : ℂ) * cexp (s₁ * twistExp γ w q)

theorem re_twistExp (γ : ℝ) (w : ι → ℂ) (q : Fin 3 × ι) :
    (twistExp γ w q).re = (w q.2).re := by
  simp [twistExp, re_twistShift]

/-- `Φ_twist(t) = Φ(t + s₁)(1 + cos(γ(t + s₁)))`. -/
theorem lagRe_twist {c : ι → ℝ} {w : ι → ℂ} (hc0 : ∀ i, 0 ≤ c i) (hcs : Summable c) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (γ : ℝ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) {t : ℝ} (ht : 0 ≤ t) :
    lagRe (twistCoef γ s₁ c w) (twistExp γ w) t =
      lagRe (fun i => (c i : ℂ)) w (t + s₁) * (1 + Real.cos (γ * (t + s₁))) := by
  have hsumC : Summable fun i => ‖(c i : ℂ)‖ := by
    refine hcs.congr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 i)]
  set F : Fin 3 → ℂ := fun k => (twistWeight k : ℂ) * cexp (((t + s₁ : ℝ) : ℂ) * twistShift γ k)
    with hF
  set G : ι → ℂ := fun i => (c i : ℂ) * cexp (((t + s₁ : ℝ) : ℂ) * w i) with hG
  have hGs : Summable G := summable_term hsumC hB (add_nonneg ht hs₁)
  have e : ∀ x : ℂ, cexp (s₁ * x) * cexp (t * x) = cexp (((t + s₁ : ℝ) : ℂ) * x) := fun x => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e' : ∀ x y : ℂ, cexp (((t + s₁ : ℝ) : ℂ) * y) * cexp (((t + s₁ : ℝ) : ℂ) * x) =
      cexp (((t + s₁ : ℝ) : ℂ) * (x + y)) := fun x y => by
    rw [← Complex.exp_add]; congr 1; ring
  have hpt : ∀ q : Fin 3 × ι, twistCoef γ s₁ c w q * cexp (t * twistExp γ w q) = F q.1 * G q.2 := by
    intro q
    calc twistCoef γ s₁ c w q * cexp (t * twistExp γ w q)
        = ((c q.2 * twistWeight q.1 : ℝ) : ℂ) *
            (cexp (s₁ * twistExp γ w q) * cexp (t * twistExp γ w q)) := by
          rw [twistCoef, mul_assoc]
      _ = ((c q.2 * twistWeight q.1 : ℝ) : ℂ) * cexp (((t + s₁ : ℝ) : ℂ) * twistExp γ w q) := by
          rw [e]
      _ = F q.1 * G q.2 := by
          rw [hF, hG]
          simp only
          rw [mul_mul_mul_comm, e', twistExp]
          push_cast
          ring
  have hprod : Summable fun q : Fin 3 × ι => F q.1 * G q.2 := by
    refine Summable.of_norm ?_
    refine (summable_prod_of_nonneg fun q => norm_nonneg _).mpr
      ⟨fun k => (hGs.mul_left (F k)).norm, Summable.of_finite⟩
  have htsum : ∑' q : Fin 3 × ι, F q.1 * G q.2 = (∑ k, F k) * ∑' i, G i := by
    rw [Summable.tsum_prod' hprod (fun k => hGs.mul_left (F k)), tsum_fintype, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (tsum_mul_left (f := G) (a := F k) :)
  have hsumF : ∑ k, F k = ((1 + Real.cos (γ * (t + s₁)) : ℝ) : ℂ) := sum_twist γ (t + s₁)
  unfold lagRe
  rw [tsum_congr hpt, htsum, hsumF, mul_comm, Complex.re_mul_ofReal]

/-! ## One-sided bounds force positive configurations on-line -/

/-- **One-sided bounds force positive configurations on-line.** Let `c_i > 0` be summable and let
the exponents `w_i` be locally finite with `Re w_i ≤ B`. If `Re Σ_i c_i e^{t w_i} ≤ M` for every
`t ≥ s₀`, then `Re w_i ≤ 0` for every `i`. -/
theorem re_nonpos_of_lag_le [Countable ι] {c : ι → ℝ} {w : ι → ℂ} (hc : ∀ i, 0 < c i)
    (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {M s₀ : ℝ}
    (hM : ∀ t : ℝ, s₀ ≤ t → lagRe (fun i => (c i : ℂ)) w t ≤ M) (j : ι) : (w j).re ≤ 0 := by
  by_contra hj
  replace hj := not_le.mp hj
  set s₁ := max s₀ 0 with hs₁
  have hs₁0 : 0 ≤ s₁ := le_max_right _ _
  set γ := (w j).im with hγ
  have hc0 : ∀ i, 0 ≤ c i := fun i => (hc i).le
  have hcoef : ∀ q : Fin 3 × ι, ‖twistCoef γ s₁ c w q‖ ≤ c q.2 * Real.exp (s₁ * B) := by
    intro q
    rw [twistCoef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hc0 _) (twistWeight_pos _).le), Complex.norm_exp]
    have hre : ((s₁ : ℂ) * twistExp γ w q).re = s₁ * (w q.2).re := by
      rw [Complex.re_ofReal_mul, re_twistExp]
    rw [hre]
    exact mul_le_mul (mul_le_of_le_one_right (hc0 _) (twistWeight_le_one _))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB _) hs₁0)) (Real.exp_pos _).le (hc0 _)
  have hnormQ : Summable fun q : Fin 3 × ι => ‖twistCoef γ s₁ c w q‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef ?_
    exact (summable_prod_of_nonneg fun q => mul_nonneg (hc0 q.2) (Real.exp_pos _).le).mpr
      ⟨fun k => hcs.mul_right _, Summable.of_finite⟩
  have hfinQ : ∀ R : ℝ, {q : Fin 3 × ι | ‖twistExp γ w q‖ ≤ R}.Finite := by
    intro R
    refine ((Set.finite_univ : (univ : Set (Fin 3)).Finite).prod (hfin (R + |γ|))).subset
      fun q hq => ⟨mem_univ _, ?_⟩
    simp only [mem_setOf_eq, twistExp] at hq ⊢
    have h1 := norm_sub_le (w q.2 + twistShift γ q.1) (twistShift γ q.1)
    rw [add_sub_cancel_right] at h1
    linarith [norm_twistShift_le γ q.1]
  have hBQ : ∀ q, (twistExp γ w q).re ≤ B := fun q => by rw [re_twistExp]; exact hB _
  have hposQ : ∀ q, (twistExp γ w q).im = 0 → 0 < (twistExp γ w q).re →
      0 < (twistCoef γ s₁ c w q).re := by
    intro q him _
    have hx : twistExp γ w q = ((twistExp γ w q).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [twistCoef, hx, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    exact mul_pos (mul_pos (hc _) (twistWeight_pos _)) (Real.exp_pos _)
  have hMQ : ∀ t : ℝ, 0 ≤ t → lagRe (twistCoef γ s₁ c w) (twistExp γ w) t ≤ 2 * max M 0 := by
    intro t ht
    rw [lagRe_twist hc0 hcs hB γ hs₁0 ht]
    have h1 := hM (t + s₁) (by linarith [le_max_left s₀ 0])
    have hcos := Real.neg_one_le_cos (γ * (t + s₁))
    have hcos' := Real.cos_le_one (γ * (t + s₁))
    have hm := le_max_left M 0
    have hm0 := le_max_right M 0
    nlinarith
  have hjQ : (twistExp γ w (2, j)).im = 0 := by simp [twistExp, twistShift, hγ]
  have key := re_nonpos_of_real hnormQ hfinQ hBQ (maxRealPositive_of_pos hposQ) hMQ (2, j) hjQ
  rw [re_twistExp] at key
  linarith

/-- **Baire.** Let `g` be continuous and equal to `f` on `[0, ∞)`. If the spacings `ℓ > 0` whose
progression `m ↦ f(mℓ)` is bounded above form a non-meagre set, then `f` is bounded above on a
half-line. -/
theorem exists_halfLine_le_of_not_isMeagre {f g : ℝ → ℝ} (hg : Continuous g)
    (hfg : ∀ t, 0 ≤ t → g t = f t)
    (hS : ¬ IsMeagre {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => f (m * ℓ))}) :
    ∃ M s₀ : ℝ, ∀ t, s₀ ≤ t → f t ≤ M := by
  set level : ℕ → ℕ → Set ℝ :=
    fun k M => {ℓ | 1 / ((k : ℝ) + 1) ≤ ℓ ∧ ∀ m : ℕ, g (m * ℓ) ≤ M} with hlevel
  have hclosed : ∀ k M, IsClosed (level k M) := by
    intro k M
    have : level k M = Ici (1 / ((k : ℝ) + 1)) ∩ ⋂ m : ℕ, {ℓ | g (m * ℓ) ≤ M} := by
      ext ℓ; simp [hlevel]
    rw [this]
    exact isClosed_Ici.inter (isClosed_iInter fun m =>
      isClosed_le (hg.comp (continuous_const.mul continuous_id)) continuous_const)
  have hsub : {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => f (m * ℓ))} ⊆
      ⋃ k : ℕ, ⋃ M : ℕ, level k M := by
    rintro ℓ ⟨hℓ, M₀, hM₀⟩
    refine mem_iUnion.mpr ⟨⌈1 / ℓ⌉₊, mem_iUnion.mpr ⟨⌈M₀⌉₊, ?_, fun m => ?_⟩⟩
    · have hk := mul_le_mul_of_nonneg_left (Nat.le_ceil (1 / ℓ)) hℓ.le
      rw [mul_one_div_cancel hℓ.ne'] at hk
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · rw [hfg _ (mul_nonneg (Nat.cast_nonneg m) hℓ.le)]
      exact (hM₀ ⟨m, rfl⟩).trans (Nat.le_ceil M₀)
  have hne : ∃ k M : ℕ, (interior (level k M)).Nonempty := by
    by_contra hcon
    simp only [not_exists, Set.not_nonempty_iff_eq_empty] at hcon
    exact hS (IsMeagre.mono hsub (isMeagre_iUnion fun k => isMeagre_iUnion fun M =>
      IsNowhereDense.isMeagre ((hclosed k M).isNowhereDense_iff.mpr (hcon k M))))
  obtain ⟨k, M, x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hxlev : x ∈ level k M := interior_subset hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxlev.1
  refine ⟨M, x * (x + ε) / (x + ε - x) + 1, fun t ht => ?_⟩
  obtain ⟨m, -, ℓ, hℓ, rfl⟩ := exists_nat_mul_mem_Ioo hx0 (by linarith : x < x + ε)
    (by linarith : x * (x + ε) / (x + ε - x) < t)
  have hℓlev : ℓ ∈ level k M := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hℓ.1, hℓ.2])
  rw [← hfg _ (mul_nonneg (Nat.cast_nonneg m) (hx0.trans hℓ.1).le)]
  exact hℓlev.2 m

/-- The lag function agrees on `[0, ∞)` with the continuous function `t ↦ Re Σ a_i e^{max(t,0) w_i}`. -/
theorem exists_continuous_eq_lagRe {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ t, 0 ≤ t → g t = lagRe a w t :=
  ⟨fun t => (∑' i, a i * cexp ((max t 0 : ℝ) * w i)).re,
    Complex.continuous_re.comp (continuous_lagSum_max ha hB),
    fun t ht => by simp only [max_eq_left ht, lagRe]⟩

/-- **Non-meagre sets of spacings are rigid.** If the set of spacings `ℓ > 0` for which
`m ↦ Re Σ_i c_i e^{mℓ w_i}` is bounded above is not meagre, then `Re w_i ≤ 0` for every `i`. -/
theorem re_nonpos_of_not_isMeagre [Countable ι] {c : ι → ℝ} {w : ι → ℂ} (hc : ∀ i, 0 < c i)
    (hcs : Summable c) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B)
    (hS : ¬ IsMeagre {ℓ : ℝ | 0 < ℓ ∧
      BddAbove (range fun m : ℕ => lagRe (fun i => (c i : ℂ)) w (m * ℓ))}) (j : ι) :
    (w j).re ≤ 0 := by
  have hsumC : Summable fun i => ‖(c i : ℂ)‖ := by
    refine hcs.congr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hc i)]
  obtain ⟨g, hg, hfg⟩ := exists_continuous_eq_lagRe hsumC hB
  obtain ⟨M, s₀, h⟩ := exists_halfLine_le_of_not_isMeagre hg hfg hS
  exact re_nonpos_of_lag_le hc hcs hfin hB h j

/-! ## Complex weights -/

/-- The weights `1, ½e^{iθ}, ½e^{−iθ}` of the phase twist `1 + cos(γt + θ)`. -/
def phaseWeight (θ : ℝ) : Fin 3 → ℂ := ![1, cexp (θ * I) / 2, cexp (-(θ * I)) / 2]

theorem norm_phaseWeight_le (θ : ℝ) (k : Fin 3) : ‖phaseWeight θ k‖ ≤ 1 := by
  fin_cases k <;> simp [phaseWeight, Complex.norm_exp] <;> norm_num

/-- `1 + ½e^{iθ}e^{iγx} + ½e^{−iθ}e^{−iγx} = 1 + cos(γx + θ)`. -/
theorem sum_phaseTwist (γ θ x : ℝ) :
    ∑ k : Fin 3, phaseWeight θ k * cexp (x * twistShift γ k) =
      ((1 + Real.cos (γ * x + θ) : ℝ) : ℂ) := by
  rw [Fin.sum_univ_three]
  simp only [phaseWeight, twistShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  rw [Complex.cos]
  have e1 : cexp (θ * I) / 2 * cexp (x * (I * γ)) = cexp ((γ * x + θ) * I) / 2 := by
    rw [div_mul_eq_mul_div, ← Complex.exp_add]; congr 2; ring
  have e2 : cexp (-(θ * I)) / 2 * cexp (x * -(I * γ)) = cexp (-(γ * x + θ) * I) / 2 := by
    rw [div_mul_eq_mul_div, ← Complex.exp_add]; congr 2; ring
  rw [e1, e2, mul_zero, Complex.exp_zero]
  ring

/-- The phase-twisted configuration shifted by `s₁`: weights `a_i·(1, ½e^{iθ}, ½e^{−iθ})·e^{s₁(w_i + shift)}`. -/
def phaseCoef (γ θ s₁ : ℝ) (a w : ι → ℂ) (q : Fin 3 × ι) : ℂ :=
  a q.2 * phaseWeight θ q.1 * cexp (s₁ * twistExp γ w q)

/-- `Φ_twist(t) = Φ(t + s₁)(1 + cos(γ(t + s₁) + θ))`. -/
theorem lagRe_phaseTwist {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (γ θ : ℝ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) {t : ℝ} (ht : 0 ≤ t) :
    lagRe (phaseCoef γ θ s₁ a w) (twistExp γ w) t =
      lagRe a w (t + s₁) * (1 + Real.cos (γ * (t + s₁) + θ)) := by
  set F : Fin 3 → ℂ := fun k => phaseWeight θ k * cexp (((t + s₁ : ℝ) : ℂ) * twistShift γ k)
    with hF
  set G : ι → ℂ := fun i => a i * cexp (((t + s₁ : ℝ) : ℂ) * w i) with hG
  have hGs : Summable G := summable_term ha hB (add_nonneg ht hs₁)
  have e : ∀ x : ℂ, cexp (s₁ * x) * cexp (t * x) = cexp (((t + s₁ : ℝ) : ℂ) * x) := fun x => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e' : ∀ x y : ℂ, cexp (((t + s₁ : ℝ) : ℂ) * y) * cexp (((t + s₁ : ℝ) : ℂ) * x) =
      cexp (((t + s₁ : ℝ) : ℂ) * (x + y)) := fun x y => by
    rw [← Complex.exp_add]; congr 1; ring
  have hpt : ∀ q : Fin 3 × ι, phaseCoef γ θ s₁ a w q * cexp (t * twistExp γ w q) =
      F q.1 * G q.2 := by
    intro q
    calc phaseCoef γ θ s₁ a w q * cexp (t * twistExp γ w q)
        = a q.2 * phaseWeight θ q.1 *
            (cexp (s₁ * twistExp γ w q) * cexp (t * twistExp γ w q)) := by
          rw [phaseCoef, mul_assoc]
      _ = a q.2 * phaseWeight θ q.1 * cexp (((t + s₁ : ℝ) : ℂ) * twistExp γ w q) := by rw [e]
      _ = F q.1 * G q.2 := by
          rw [hF, hG]
          simp only
          rw [mul_mul_mul_comm, e', twistExp]
          ring
  have hprod : Summable fun q : Fin 3 × ι => F q.1 * G q.2 := by
    refine Summable.of_norm ?_
    exact (summable_prod_of_nonneg fun q => norm_nonneg _).mpr
      ⟨fun k => (hGs.mul_left (F k)).norm, Summable.of_finite⟩
  have htsum : ∑' q : Fin 3 × ι, F q.1 * G q.2 = (∑ k, F k) * ∑' i, G i := by
    rw [Summable.tsum_prod' hprod (fun k => hGs.mul_left (F k)), tsum_fintype, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (tsum_mul_left (f := G) (a := F k) :)
  have hsumF : ∑ k, F k = ((1 + Real.cos (γ * (t + s₁) + θ) : ℝ) : ℂ) :=
    sum_phaseTwist γ θ (t + s₁)
  unfold lagRe
  rw [tsum_congr hpt, htsum, hsumF, mul_comm, Complex.re_mul_ofReal]

theorem lagRe_shift (a w : ι → ℂ) (s₁ t : ℝ) :
    lagRe (fun i => a i * cexp (s₁ * w i)) w t = lagRe a w (t + s₁) := by
  unfold lagRe
  congr 1
  refine tsum_congr fun i => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem lagRe_neg (a w : ι → ℂ) (t : ℝ) : lagRe (fun i => -a i) w t = -lagRe a w t := by
  unfold lagRe
  simp only [neg_mul, tsum_neg, Complex.neg_re]

theorem summable_shift {a w : ι → ℂ} (ha : Summable fun i => ‖a i‖) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) :
    Summable fun i => ‖a i * cexp (s₁ * w i)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hB hs₁) (ha.mul_right _)

theorem re_mul_cexp_of_im_eq_zero (a w : ℂ) (s : ℝ) (hw : w.im = 0) :
    (a * cexp (s * w)).re = a.re * Real.exp (s * w.re) := by
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, w = r := ⟨w.re, Complex.ext (by simp) (by simp [hw])⟩
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.re_mul_ofReal, Complex.ofReal_re]

theorem maxRealPositive_of_unique {a w : ι → ℂ} (hinj : Function.Injective w) {k : ι}
    (huniq : ∀ k', (w k').im = 0 → 0 < (w k').re →
      (∀ i, (w i).im = 0 → 0 < (w i).re → (w i).re ≤ (w k').re) → k' = k)
    (hk : 0 < (a k).re) : MaxRealPositive a w := by
  intro k' h1 h2 h3
  obtain rfl := huniq k' h1 h2 h3
  exact ⟨hk, fun i hi => by rw [hinj hi]; exact hk.le⟩

/-- **Non-real exponents of a one-sided upper configuration.** Let the exponents be distinct with
`Im w_i ≥ 0`, the weights nonzero, and every real exponent `≤ 0`. If `Φ ≤ M` on a half-line, then
`Re w_i ≤ 0` for every `i`. The twist is `1 + cos(t Im w_k + arg a_k)` at the rightmost exponent
`w_k` of the height of `w_j`. -/
theorem re_nonpos_of_upper_of_real [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hinj : Function.Injective w) (hup : ∀ i, 0 ≤ (w i).im)
    (ha0 : ∀ i, a i ≠ 0) (hR : ∀ i, (w i).im = 0 → (w i).re ≤ 0) {M s₀ : ℝ}
    (hM : ∀ t : ℝ, s₀ ≤ t → lagRe a w t ≤ M) (j : ι) : (w j).re ≤ 0 := by
  by_contra hj
  replace hj := not_le.mp hj
  have hγ0 : 0 < (w j).im := lt_of_le_of_ne (hup j) fun h => by linarith [hR j h.symm]
  set γ := (w j).im with hγ
  set s₁ := max s₀ 0 with hs₁
  have hs₁0 : 0 ≤ s₁ := le_max_right _ _
  have hSfin : {i | (w i).im = γ ∧ 0 < (w i).re}.Finite := (hfin (B + γ)).subset fun i hi => by
    have h1 := Complex.norm_le_abs_re_add_abs_im (w i)
    rw [hi.1, abs_of_pos hi.2, abs_of_pos hγ0] at h1
    show ‖w i‖ ≤ B + γ
    linarith [hB i]
  obtain ⟨k, hkS, hkmax⟩ := Set.exists_max_image {i | (w i).im = γ ∧ 0 < (w i).re}
    (fun i => (w i).re) hSfin ⟨j, rfl, hj⟩
  set θ := Complex.arg (a k) with hθ
  have hcoef : ∀ q : Fin 3 × ι, ‖phaseCoef γ θ s₁ a w q‖ ≤ ‖a q.2‖ * Real.exp (s₁ * B) := by
    intro q
    rw [phaseCoef, norm_mul, norm_mul, Complex.norm_exp]
    have hre : ((s₁ : ℂ) * twistExp γ w q).re = s₁ * (w q.2).re := by
      rw [Complex.re_ofReal_mul, re_twistExp]
    rw [hre]
    calc ‖a q.2‖ * ‖phaseWeight θ q.1‖ * Real.exp (s₁ * (w q.2).re)
        ≤ ‖a q.2‖ * 1 * Real.exp (s₁ * B) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_phaseWeight_le θ q.1) (norm_nonneg _))
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB _) hs₁0)) (Real.exp_pos _).le
            (by positivity)
      _ = ‖a q.2‖ * Real.exp (s₁ * B) := by ring
  have hnormQ : Summable fun q : Fin 3 × ι => ‖phaseCoef γ θ s₁ a w q‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef ?_
    exact (summable_prod_of_nonneg fun q => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).mpr
      ⟨fun _ => ha.mul_right _, Summable.of_finite⟩
  have hfinQ : ∀ R : ℝ, {q : Fin 3 × ι | ‖twistExp γ w q‖ ≤ R}.Finite := by
    intro R
    refine ((Set.finite_univ : (univ : Set (Fin 3)).Finite).prod (hfin (R + |γ|))).subset
      fun q hq => ⟨mem_univ _, ?_⟩
    simp only [mem_setOf_eq, twistExp] at hq ⊢
    have h1 := norm_sub_le (w q.2 + twistShift γ q.1) (twistShift γ q.1)
    rw [add_sub_cancel_right] at h1
    linarith [norm_twistShift_le γ q.1]
  have hBQ : ∀ q, (twistExp γ w q).re ≤ B := fun q => by rw [re_twistExp]; exact hB _
  have hMQ : ∀ t : ℝ, 0 ≤ t →
      lagRe (phaseCoef γ θ s₁ a w) (twistExp γ w) t ≤ 2 * max M 0 := by
    intro t ht
    rw [lagRe_phaseTwist ha hB γ θ hs₁0 ht]
    have h1 := hM (t + s₁) (by linarith [le_max_left s₀ 0])
    have hcos := Real.neg_one_le_cos (γ * (t + s₁) + θ)
    have hcos' := Real.cos_le_one (γ * (t + s₁) + θ)
    have hm := le_max_left M 0
    have hm0 := le_max_right M 0
    nlinarith
  have him : ∀ q : Fin 3 × ι, (twistExp γ w q).im = (w q.2).im + (twistShift γ q.1).im :=
    fun q => by simp [twistExp]
  -- the positive real exponents of the twist sit at shift `−iγ` over height `γ`
  have hclass : ∀ q : Fin 3 × ι, (twistExp γ w q).im = 0 → 0 < (twistExp γ w q).re →
      q.1 = 2 ∧ (w q.2).im = γ := by
    rintro ⟨m, i⟩ h0 hpos
    rw [re_twistExp] at hpos
    rw [him] at h0
    fin_cases m
    · simp [twistShift] at h0; exact absurd (hR i h0) (not_le.mpr hpos)
    · simp [twistShift] at h0; linarith [hup i]
    · simp [twistShift] at h0; exact ⟨rfl, by linarith⟩
  have hkQ : (twistExp γ w (2, k)).im = 0 := by
    rw [him]; simp [twistShift, hkS.1]
  have hkQre : 0 < (twistExp γ w (2, k)).re := by rw [re_twistExp]; exact hkS.2
  have huniq : ∀ q : Fin 3 × ι, (twistExp γ w q).im = 0 → 0 < (twistExp γ w q).re →
      (twistExp γ w (2, k)).re ≤ (twistExp γ w q).re → q = (2, k) := by
    rintro ⟨m, i⟩ h0 hpos hle
    obtain ⟨hm, hi⟩ := hclass (m, i) h0 hpos
    simp only at hm hi
    rw [re_twistExp, re_twistExp] at hle
    rw [re_twistExp] at hpos
    have hle' : (w i).re ≤ (w k).re := hkmax i ⟨hi, hpos⟩
    have hwik : w i = w k := Complex.ext (le_antisymm hle' hle) (by rw [hi, hkS.1])
    rw [hm, hinj hwik]
  -- the twisted weight at `(2, k)` is `‖a_k‖ e^{s₁ Re w_k}/2 > 0`
  have hwq : twistExp γ w (2, k) = ((w k).re : ℂ) :=
    Complex.ext (by rw [re_twistExp]; simp) (by rw [hkQ]; simp)
  have hak : a k * cexp (-(θ * I)) = (‖a k‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (a k)]
    rw [← hθ, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hval : phaseCoef γ θ s₁ a w (2, k) = ((‖a k‖ / 2 * Real.exp (s₁ * (w k).re) : ℝ) : ℂ) := by
    simp only [phaseCoef, phaseWeight, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [hwq, ← mul_div_assoc, hak, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    push_cast; ring
  have hkpos : 0 < (phaseCoef γ θ s₁ a w (2, k)).re := by
    rw [hval, Complex.ofReal_re]
    exact mul_pos (div_pos (norm_pos_iff.mpr (ha0 k)) two_pos) (Real.exp_pos _)
  have hmaxQ : MaxRealPositive (phaseCoef γ θ s₁ a w) (twistExp γ w) := by
    intro q h0 hpos hqmax
    rw [huniq q h0 hpos (hqmax (2, k) hkQ hkQre)]
    refine ⟨hkpos, fun q' hq' => ?_⟩
    rw [huniq q' (by rw [hq']; exact hkQ) (by rw [hq']; exact hkQre) (by rw [hq'])]
    exact hkpos.le
  have key := re_nonpos_of_real hnormQ hfinQ hBQ hmaxQ hMQ (2, k) hkQ
  rw [re_twistExp] at key
  linarith [hkS.2]

/-- **One-sided bounds force upper configurations on-line (complex weights).** Let the exponents
`w_i` be distinct and locally finite with `0 ≤ Im w_i` and `Re w_i ≤ B`, and let the weights be
nonzero, summable, with `Re a_i > 0` at real exponents. If `Re Σ_i a_i e^{t w_i} ≤ M` for `t ≥ s₀`,
then `Re w_i ≤ 0` for every `i`. -/
theorem re_nonpos_of_lagRe_le_upper [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hinj : Function.Injective w) (hup : ∀ i, 0 ≤ (w i).im)
    (ha0 : ∀ i, a i ≠ 0) (hreal : ∀ i, (w i).im = 0 → 0 < (a i).re) {M s₀ : ℝ}
    (hM : ∀ t : ℝ, s₀ ≤ t → lagRe a w t ≤ M) (j : ι) : (w j).re ≤ 0 := by
  have hs₁0 : 0 ≤ max s₀ 0 := le_max_right _ _
  have hR : ∀ i, (w i).im = 0 → (w i).re ≤ 0 := by
    intro i hi
    refine re_nonpos_of_real (a := fun i => a i * cexp ((max s₀ 0 : ℝ) * w i))
      (summable_shift ha hB hs₁0) hfin hB (maxRealPositive_of_pos fun k hk _ => ?_) (M := M)
      (fun t ht => ?_) i hi
    · rw [re_mul_cexp_of_im_eq_zero _ _ _ hk]; exact mul_pos (hreal k hk) (Real.exp_pos _)
    · rw [lagRe_shift]; exact hM _ (by linarith [le_max_left s₀ 0])
  exact re_nonpos_of_upper_of_real ha hfin hB hinj hup ha0 hR hM j

/-- **Two-sided bounds force upper configurations on-line (any nonzero weights).** As
`re_nonpos_of_lagRe_le_upper`, with `|Re Σ_i a_i e^{t w_i}| ≤ M` on a half-line and only
`Re a_i ≠ 0` at real exponents. -/
theorem re_nonpos_of_abs_lagRe_le_upper [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hinj : Function.Injective w) (hup : ∀ i, 0 ≤ (w i).im)
    (ha0 : ∀ i, a i ≠ 0) (hreal : ∀ i, (w i).im = 0 → (a i).re ≠ 0) {M s₀ : ℝ}
    (hM : ∀ t : ℝ, s₀ ≤ t → |lagRe a w t| ≤ M) (j : ι) : (w j).re ≤ 0 := by
  have hs₁0 : 0 ≤ max s₀ 0 := le_max_right _ _
  set b : ι → ℂ := fun i => a i * cexp ((max s₀ 0 : ℝ) * w i) with hb
  have hbs : Summable fun i => ‖b i‖ := summable_shift ha hB hs₁0
  have hbM : ∀ t : ℝ, 0 ≤ t → |lagRe b w t| ≤ M := fun t ht => by
    rw [hb, lagRe_shift]; exact hM _ (by linarith [le_max_left s₀ 0])
  have hR : ∀ i, (w i).im = 0 → (w i).re ≤ 0 := by
    intro i hi
    by_contra hpos
    replace hpos := not_le.mp hpos
    have hPfin : {i | (w i).im = 0 ∧ 0 < (w i).re}.Finite := (hfin B).subset fun i hi => by
      have h1 := Complex.norm_le_abs_re_add_abs_im (w i)
      rw [hi.1, abs_zero, add_zero, abs_of_pos hi.2] at h1
      exact h1.trans (hB i)
    obtain ⟨k, hkP, hkmax⟩ := Set.exists_max_image {i | (w i).im = 0 ∧ 0 < (w i).re}
      (fun i => (w i).re) hPfin ⟨i, hi, hpos⟩
    have huniq : ∀ k', (w k').im = 0 → 0 < (w k').re →
        (∀ i, (w i).im = 0 → 0 < (w i).re → (w i).re ≤ (w k').re) → k' = k := fun k' h1 h2 h3 =>
      hinj (Complex.ext (le_antisymm (hkmax k' ⟨h1, h2⟩) (h3 k hkP.1 hkP.2)) (by rw [h1, hkP.1]))
    have hbk : (b k).re = (a k).re * Real.exp (max s₀ 0 * (w k).re) :=
      re_mul_cexp_of_im_eq_zero _ _ _ hkP.1
    rcases lt_or_gt_of_ne (hreal k hkP.1) with hneg | hposk
    · have key := re_nonpos_of_real (a := fun i => -b i) (by simpa using hbs) hfin hB
        (maxRealPositive_of_unique hinj huniq (by
          simp only [Complex.neg_re, hbk]
          nlinarith [Real.exp_pos (max s₀ 0 * (w k).re)]))
        (M := M) (fun t ht => by
          rw [lagRe_neg]; linarith [neg_abs_le (lagRe b w t), hbM t ht]) k hkP.1
      linarith [hkP.2]
    · have key := re_nonpos_of_real hbs hfin hB
        (maxRealPositive_of_unique hinj huniq (by
          rw [hbk]; exact mul_pos hposk (Real.exp_pos _)))
        (M := M) (fun t ht => (le_abs_self _).trans (hbM t ht)) k hkP.1
      linarith [hkP.2]
  exact re_nonpos_of_upper_of_real ha hfin hB hinj hup ha0 hR
    (fun t ht => (le_abs_self _).trans (hM t ht)) j

/-- **Non-meagre sets of spacings are rigid (complex weights).** For an upper configuration as in
`re_nonpos_of_lagRe_le_upper`, if the spacings `ℓ > 0` whose progression `m ↦ Φ(mℓ)` is bounded above
form a non-meagre set, then `Re w_i ≤ 0` for every `i`. -/
theorem re_nonpos_of_not_isMeagre_upper [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hinj : Function.Injective w) (hup : ∀ i, 0 ≤ (w i).im)
    (ha0 : ∀ i, a i ≠ 0) (hreal : ∀ i, (w i).im = 0 → 0 < (a i).re)
    (hS : ¬ IsMeagre {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => lagRe a w (m * ℓ))})
    (j : ι) : (w j).re ≤ 0 := by
  obtain ⟨g, hg, hfg⟩ := exists_continuous_eq_lagRe ha hB
  obtain ⟨M, s₀, h⟩ := exists_halfLine_le_of_not_isMeagre hg hfg hS
  exact re_nonpos_of_lagRe_le_upper ha hfin hB hinj hup ha0 hreal h j

/-- **Non-meagre sets of spacings are rigid (two-sided, any nonzero weights).** -/
theorem re_nonpos_of_not_isMeagre_abs_upper [Countable ι] {a w : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) (hfin : ∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) {B : ℝ}
    (hB : ∀ i, (w i).re ≤ B) (hinj : Function.Injective w) (hup : ∀ i, 0 ≤ (w i).im)
    (ha0 : ∀ i, a i ≠ 0) (hreal : ∀ i, (w i).im = 0 → (a i).re ≠ 0)
    (hS : ¬ IsMeagre {ℓ : ℝ | 0 < ℓ ∧ BddAbove (range fun m : ℕ => |lagRe a w (m * ℓ)|)})
    (j : ι) : (w j).re ≤ 0 := by
  obtain ⟨g, hg, hfg⟩ := exists_continuous_eq_lagRe ha hB
  obtain ⟨M, s₀, h⟩ := exists_halfLine_le_of_not_isMeagre (f := fun t => |lagRe a w t|)
    (g := fun t => |g t|) hg.abs (fun t ht => by simp only [hfg t ht]) hS
  exact re_nonpos_of_abs_lagRe_le_upper ha hfin hB hinj hup ha0 hreal h j

end

end RHTower.OneSidedConfiguration
