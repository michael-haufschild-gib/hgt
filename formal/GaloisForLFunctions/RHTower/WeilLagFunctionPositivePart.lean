import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth
import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# The positive-part lag criterion: sub-exponential positive excursions of `Φ` force RH

The one-sided criterion (`WeilLagFunctionOneSided`) needs a global ceiling `Φ ≤ M` on the real lag
function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`.  Landau's theorem only needs a nonnegative measure, and
`Φ₋ = max(−Φ, 0)` is one whatever `Φ` does; its Laplace transform is
`L[Φ₊](s) − G(s)` where `Φ₊ = max(Φ, 0)` and `G` is the Mittag-Leffler series of the zeros.  Hence
the *only* hypothesis needed is that the positive part `Φ₊` has Laplace abscissa `≤ a`:

* if `∫_0^∞ Φ₊(u) e^{−σu} du < ∞` for every `σ > a` (`0 ≤ a < ½`), then every zero of `ξ` has
  real part `≤ ½ + a`;
* if this holds for every `σ > 0`, the Riemann hypothesis follows.

In integrated form: if for every `ε > 0` the primitive `∫_0^T Φ₊` is `O(e^{εT})`, then RH.  The
positive excursions of the tail-averaged prime deficit only need sub-exponential *mass*; no
pointwise ceiling, no bound on the negative part, and no bound on `|Φ|` enter.  The clipped
densities `oneSidedDensity (∓1) 0` of the one-sided module are exactly `Φ₊` and `Φ₋`, so the
measures `Φ₊du + du` and `Φ₋du + du` are `oneSidedMeasure (-1) 0` and `oneSidedMeasure 1 0`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Positive and negative parts of the lag function -/

/-- `Φ₊ = max(Φ, 0)`, realised as the clipped density `oneSidedDensity (−1) 0`. -/
def lagPositivePart (u : ℝ) : ℝ := (oneSidedDensity (-1) 0 u : ℝ)

/-- `Φ₋ = max(−Φ, 0)`, realised as the clipped density `oneSidedDensity 1 0`. -/
def lagNegativePart (u : ℝ) : ℝ := (oneSidedDensity 1 0 u : ℝ)

theorem lagPositivePart_eq_max (u : ℝ) : lagPositivePart u = max (weilLagFunctionReal u) 0 := by
  unfold lagPositivePart oneSidedDensity
  rw [Real.coe_toNNReal']
  ring_nf

theorem lagNegativePart_eq_max (u : ℝ) : lagNegativePart u = max (-weilLagFunctionReal u) 0 := by
  unfold lagNegativePart oneSidedDensity
  rw [Real.coe_toNNReal']
  ring_nf

theorem lagPositivePart_nonneg (u : ℝ) : 0 ≤ lagPositivePart u := NNReal.coe_nonneg _

theorem lagNegativePart_nonneg (u : ℝ) : 0 ≤ lagNegativePart u := NNReal.coe_nonneg _

theorem lagPositivePart_sub_lagNegativePart (u : ℝ) :
    lagPositivePart u - lagNegativePart u = weilLagFunctionReal u := by
  rw [lagPositivePart_eq_max, lagNegativePart_eq_max]
  rcases le_or_gt 0 (weilLagFunctionReal u) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring

theorem measurable_lagPositivePart : Measurable lagPositivePart :=
  (measurable_oneSidedDensity _ _).coe_nnreal_real

theorem continuous_lagPositivePart : Continuous lagPositivePart := by
  have : lagPositivePart = fun u => max (weilLagFunctionReal u) 0 := funext lagPositivePart_eq_max
  rw [this]
  exact continuous_weilLagFunctionReal.max continuous_const

/-- The clipped density with `M = 0` and `|ε| ≤ 1` is at most `|Φ|`. -/
theorem oneSidedDensity_zero_le_abs {ε : ℝ} (hε : |ε| ≤ 1) (u : ℝ) :
    ((oneSidedDensity ε 0 u : ℝ)) ≤ |weilLagFunctionReal u| := by
  unfold oneSidedDensity
  rw [Real.coe_toNNReal']
  have h1 : |ε * weilLagFunctionReal u| ≤ |weilLagFunctionReal u| := by
    rw [abs_mul]
    calc |ε| * |weilLagFunctionReal u| ≤ 1 * |weilLagFunctionReal u| := by gcongr
      _ = _ := one_mul _
  have h2 := neg_abs_le (ε * weilLagFunctionReal u)
  have h3 := abs_nonneg (weilLagFunctionReal u)
  rcases le_or_gt (0 - ε * weilLagFunctionReal u) 0 with h | h
  · rw [max_eq_right h]; exact h3
  · rw [max_eq_left h.le]; linarith

/-- The flip identity `max(−εΦ, 0) = max(εΦ, 0) − εΦ` between the two clipped densities. -/
theorem oneSidedDensity_zero_flip (ε u : ℝ) :
    ((oneSidedDensity ε 0 u : ℝ)) = ((oneSidedDensity (-ε) 0 u : ℝ)) - ε * weilLagFunctionReal u := by
  unfold oneSidedDensity
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  simp only [zero_sub, neg_mul, neg_neg]
  rcases le_or_gt 0 (ε * weilLagFunctionReal u) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring

/-! ## The Laplace identity `L[Φ₋du + du] = L[Φ₊du + du] − G` -/

theorem integrableOn_oneSidedDensity_smul_cexp {ε M : ℝ} (hε : |ε| ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun u : ℝ => oneSidedDensity ε M u • Complex.exp (-s * (u : ℂ))) (Ioi 0) := by
  refine (integrableOn_majorant (M := M) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_oneSidedDensity ε M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (oneSidedDensity_le hε hu) (Real.exp_pos _).le

/-- On `Re s > ½`: `L[max(−εΦ,0)du + du](s) = L[max(εΦ,0)du + du](s) − ε G(s)`.  No hypothesis on
`Φ` enters: the measures are the clipped densities plus Lebesgue measure. -/
theorem complexLaplace_oneSidedMeasure_zero_flip {ε : ℝ} (hε : |ε| ≤ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (oneSidedMeasure ε 0) s =
      complexLaplace (oneSidedMeasure (-ε) 0) s - ε * lagPoleSeries s := by
  have hs0 : 0 < s.re := by linarith
  have hεn : |(-ε)| ≤ 1 := by rwa [abs_neg]
  have hcexp : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs0).mono' hcexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← integral_weilLagFunction_mul_cexp hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  unfold complexLaplace oneSidedMeasure
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (integrable_cexp_oneSided_density hε hs) hexpInt,
    integral_add_measure (integrable_cexp_oneSided_density hεn hs) hexpInt]
  rw [restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_self,
    integral_withDensity_eq_integral_smul (measurable_oneSidedDensity ε 0),
    integral_withDensity_eq_integral_smul (measurable_oneSidedDensity (-ε) 0)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), oneSidedDensity ε 0 u • Complex.exp (-s * (u : ℂ)) =
      oneSidedDensity (-ε) 0 u • Complex.exp (-s * (u : ℂ)) -
        (ε : ℂ) * ((weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u _
    rw [NNReal.smul_def, NNReal.smul_def, Complex.real_smul, Complex.real_smul]
    have h : ((oneSidedDensity ε 0 u : ℝ) : ℂ) =
        ((oneSidedDensity (-ε) 0 u : ℝ) : ℂ) - (ε : ℂ) * (weilLagFunctionReal u : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, oneSidedDensity_zero_flip ε u]
    rw [h]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (integrableOn_oneSidedDensity_smul_cexp hεn hs)
      ((integrable_weilLag_mul_cexp hs).const_mul _),
    integral_const_mul, hΦ]
  ring

/-! ## Analyticity of the transform right of the abscissa -/

theorem analyticAt_complexLaplace {ν : Measure ℝ} {c : ℝ} (hc : IsAbscissa ν c) {z : ℂ}
    (hz : c < z.re) : AnalyticAt ℂ (complexLaplace ν) z := by
  have hV : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | c < w.re}) ?_ (hV.mem_nhds hz)
  exact fun w hw => (hasDerivAt_complexLaplace hc hw).differentiableAt.differentiableWithinAt

/-! ## Abscissae -/

/-- Points where the transform of `oneSidedMeasure ε 0` converges are nonnegative. -/
theorem nonneg_of_laplaceMass_oneSidedMeasure_ne_top {ε σ : ℝ}
    (hσ : laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤) : 0 ≤ σ := by
  by_contra hneg
  apply hσ
  rw [laplaceMass_oneSided_eq, laplaceMass_volume_eq_top (not_le.mp hneg), add_top]

/-- If the clipped measure has finite transform right of `a`, its abscissa lies in `[0, a]`. -/
theorem exists_isAbscissa_oneSidedMeasure_le {ε a : ℝ} (hε : |ε| ≤ 1)
    (h : ∀ σ : ℝ, a < σ → laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤) :
    ∃ c : ℝ, IsAbscissa (oneSidedMeasure ε 0) c ∧ 0 ≤ c ∧ c ≤ a := by
  obtain ⟨hc, hc0⟩ := isAbscissa_oneSided (ε := ε) (M := 0) hε
  refine ⟨_, hc, hc0, ?_⟩
  by_contra hlt
  have hac : a < sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤} := not_le.mp hlt
  have hbdd : BddBelow {σ : ℝ | laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤} :=
    ⟨0, fun σ hσ => nonneg_of_laplaceMass_oneSidedMeasure_ne_top hσ⟩
  have hmem : (a + sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤}) / 2 ∈
      {σ : ℝ | laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤} := h _ (by linarith)
  have := csInf_le hbdd hmem
  linarith

/-- **Landau.**  If the transform of `max(εΦ,0)du + du` is finite right of `a < ½`, then the abscissa
of `max(−εΦ,0)du + du` is at most `a` as well: its continuation `L[max(εΦ,0)du+du] − εG` is
analytic at every real point `> a`. -/
theorem exists_isAbscissa_oneSidedMeasure_flip_le {ε a : ℝ} (hε : |ε| ≤ 1) (ha0 : 0 ≤ a)
    (h : ∀ σ : ℝ, a < σ → laplaceMass (oneSidedMeasure (-ε) 0) σ ≠ ⊤) :
    ∃ c : ℝ, IsAbscissa (oneSidedMeasure ε 0) c ∧ 0 ≤ c ∧ c ≤ a := by
  have hεn : |(-ε)| ≤ 1 := by rwa [abs_neg]
  obtain ⟨cP, hcP, -, hcPa⟩ := exists_isAbscissa_oneSidedMeasure_le hεn h
  obtain ⟨hc, hc0⟩ := isAbscissa_oneSided (ε := ε) (M := 0) hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤} with hcdef
  refine ⟨c, hc, hc0, ?_⟩
  by_contra hlt
  have hac : a < c := not_le.mp hlt
  have hcpos : 0 < c := lt_of_le_of_lt ha0 hac
  have hc34 : c ≤ 3 / 4 := by
    refine csInf_le ⟨0, fun σ hσ => nonneg_of_laplaceMass_oneSidedMeasure_ne_top hσ⟩ ?_
    show laplaceMass (oneSidedMeasure ε 0) (3 / 4) ≠ ⊤
    rw [laplaceMass_oneSided_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_oneSided_density_ne_top hε (by norm_num),
      laplaceMass_volume_ne_top (by norm_num)⟩
  have hne : xi ((c : ℂ) + 1 / 2) ≠ 0 := xi_ofReal_add_half_ne_zero hcpos
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hne
  set δ : ℝ := min (c - a) d / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (by linarith) hd)
  have hδc : δ ≤ (c - a) / 2 := by rw [hδdef]; linarith [min_le_left (c - a) d]
  have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right (c - a) d]
  refine false_of_analyticAt_abscissa hc hδ
    (Φ := fun z => complexLaplace (oneSidedMeasure (-ε) 0) z - (ε : ℂ) * lagPoleSeries z) ?_ ?_
  · intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have hzre : (c + a) / 2 < z.re := by
      have := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      have := abs_le.mp this
      linarith
    have hzP : cP < z.re := by linarith
    have hzxi : xi (z + 1 / 2) ≠ 0 := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      calc ‖z + 1 / 2 - ((c : ℂ) + 1 / 2)‖ = ‖z - c‖ := by congr 1; ring
        _ < δ := hz
        _ ≤ d / 2 := hδd
        _ < d := by linarith
    exact (analyticAt_complexLaplace hcP hzP).sub
      (analyticAt_const.mul (analyticAt_lagPoleSeries hzxi))
  · intro σ hσc _
    have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hTdiff : DifferentiableOn ℂ (complexLaplace (oneSidedMeasure ε 0)) {z : ℂ | c < z.re} :=
      fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
    have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (oneSidedMeasure ε 0) (t : ℂ)) (Ioi c) := by
      intro t ht
      have h1 : AnalyticAt ℂ (complexLaplace (oneSidedMeasure ε 0)) (t : ℂ) :=
        hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
      exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    have hH : AnalyticOnNhd ℝ
        (fun t : ℝ => complexLaplace (oneSidedMeasure (-ε) 0) (t : ℂ) - (ε : ℂ) * lagPoleSeries (t : ℂ))
        (Ioi c) := by
      intro t ht
      have htc : c < t := ht
      have ht0 : 0 < t := lt_trans hcpos htc
      have htP : cP < ((t : ℂ)).re := by simp; linarith
      have h1 : AnalyticAt ℂ
          (fun z => complexLaplace (oneSidedMeasure (-ε) 0) z - (ε : ℂ) * lagPoleSeries z) (t : ℂ) :=
        (analyticAt_complexLaplace hcP htP).sub
          (analyticAt_const.mul (analyticAt_lagPoleSeries (xi_ofReal_add_half_ne_zero ht0)))
      exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
    have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
    have hfg : (fun t : ℝ => complexLaplace (oneSidedMeasure ε 0) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
        (fun t : ℝ => complexLaplace (oneSidedMeasure (-ε) 0) (t : ℂ) - (ε : ℂ) * lagPoleSeries (t : ℂ)) := by
      refine Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
      exact complexLaplace_oneSidedMeasure_zero_flip hε (by simpa using ht.1)
    have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
    have hσ : complexLaplace (oneSidedMeasure ε 0) (σ : ℂ) =
        complexLaplace (oneSidedMeasure (-ε) 0) (σ : ℂ) - (ε : ℂ) * lagPoleSeries (σ : ℂ) :=
      heq (show σ ∈ Ioi c from hσc)
    rw [← hσ, complexLaplace_ofReal]

/-! ## The criteria -/

/-- **Strip form.**  If the transform of `max(εΦ,0)du + du` is finite right of `a ≥ 0`, `ε = ±1`,
then every zero copy has real part `≤ ½ + a`. -/
theorem re_le_half_add_of_oneSidedMeasure_laplace {ε a : ℝ} (hε : ε = 1 ∨ ε = -1) (ha0 : 0 ≤ a)
    (h : ∀ σ : ℝ, a < σ → laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεn : |(-ε)| ≤ 1 := by rwa [abs_neg]
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hnn : -(-ε) = ε := neg_neg ε
  obtain ⟨cP, hcP, -, hcPa⟩ := exists_isAbscissa_oneSidedMeasure_le hε1 h
  obtain ⟨cN, hcN, -, hcNa⟩ := exists_isAbscissa_oneSidedMeasure_flip_le hεn ha0 (by rwa [hnn])
  refine re_le_half_add_of_lagPoleSeries_extension ha0
    (F := fun z => (ε : ℂ) * (complexLaplace (oneSidedMeasure (-ε) 0) z -
      complexLaplace (oneSidedMeasure ε 0) z)) ?_ ?_ q
  · intro z hza _
    exact (differentiableAt_const _).mul
      ((hasDerivAt_complexLaplace hcN (by linarith)).differentiableAt.sub
        (hasDerivAt_complexLaplace hcP (by linarith)).differentiableAt)
  · intro s hs
    have hflip := complexLaplace_oneSidedMeasure_zero_flip hε1 hs
    linear_combination (-(ε : ℂ)) * hflip + (lagPoleSeries s) * hεsq

/-- **The positive-part criterion (strip form).**  If `∫_0^∞ Φ₊(u) e^{−σu} du < ∞` for every
`σ > a`, `a ≥ 0`, then every zero of `ξ` has real part `≤ ½ + a`. -/
theorem re_le_half_add_of_lagPositivePart_laplace {a : ℝ} (ha0 : 0 ≤ a)
    (h : ∀ σ : ℝ, a < σ → laplaceMass (oneSidedMeasure (-1) 0) σ ≠ ⊤) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a :=
  re_le_half_add_of_oneSidedMeasure_laplace (Or.inr rfl) ha0 h q

/-- **The positive-part criterion.**  If the positive part `Φ₊ = max(Φ, 0)` of the lag function has
Laplace abscissa `≤ 0`, i.e. `∫_0^∞ Φ₊(u) e^{−σu} du < ∞` for every `σ > 0`, then RH holds. -/
theorem riemannHypothesis_of_lagPositivePart_laplace
    (h : ∀ σ : ℝ, 0 < σ → laplaceMass (oneSidedMeasure (-1) 0) σ ≠ ⊤) : RiemannHypothesis := by
  have hε1 : |(-1 : ℝ)| ≤ 1 := by simp
  have hεn : |(1 : ℝ)| ≤ 1 := by simp
  obtain ⟨cP, hcP, -, hcPa⟩ := exists_isAbscissa_oneSidedMeasure_le hε1 h
  obtain ⟨cN, hcN, -, hcNa⟩ := exists_isAbscissa_oneSidedMeasure_flip_le (ε := 1) hεn le_rfl
    (by simpa using h)
  refine riemannHypothesis_of_lagPoleSeries_extension
    (F := fun z => complexLaplace (oneSidedMeasure (-1) 0) z - complexLaplace (oneSidedMeasure 1 0) z) ?_ ?_
  · intro z hz0 _
    exact (hasDerivAt_complexLaplace hcP (by linarith)).differentiableAt.sub
      (hasDerivAt_complexLaplace hcN (by linarith)).differentiableAt
  · intro s hs
    rw [complexLaplace_oneSidedMeasure_zero_flip hεn hs]
    push_cast
    ring

/-- The mirrored criterion: the negative part `Φ₋ = max(−Φ, 0)` with Laplace abscissa `≤ 0` forces RH. -/
theorem riemannHypothesis_of_lagNegativePart_laplace
    (h : ∀ σ : ℝ, 0 < σ → laplaceMass (oneSidedMeasure 1 0) σ ≠ ⊤) : RiemannHypothesis := by
  refine riemannHypothesis_of_lagPoleSeries_extension
    (F := fun z => complexLaplace (oneSidedMeasure (-1) 0) z - complexLaplace (oneSidedMeasure 1 0) z) ?_ ?_
  · have hε1 : |(1 : ℝ)| ≤ 1 := by simp
    have hεn : |(-1 : ℝ)| ≤ 1 := by simp
    obtain ⟨cN, hcN, -, hcNa⟩ := exists_isAbscissa_oneSidedMeasure_le hε1 h
    obtain ⟨cP, hcP, -, hcPa⟩ := exists_isAbscissa_oneSidedMeasure_flip_le (ε := -1) hεn le_rfl
      (by simpa using h)
    intro z hz0 _
    exact (hasDerivAt_complexLaplace hcP (by linarith)).differentiableAt.sub
      (hasDerivAt_complexLaplace hcN (by linarith)).differentiableAt
  · intro s hs
    rw [complexLaplace_oneSidedMeasure_zero_flip (by simp : |(1:ℝ)| ≤ 1) hs]
    push_cast
    ring

/-! ## The integrated form -/

/-- The clipped density is integrable on every compact interval. -/
theorem integrableOn_oneSidedDensity_zero_Icc (ε : ℝ) (T : ℝ) :
    IntegrableOn (fun u : ℝ => ((oneSidedDensity ε 0 u : ℝ))) (Icc 0 T) := by
  have hcont : Continuous (fun u : ℝ => ((oneSidedDensity ε 0 u : ℝ))) := by
    have : (fun u : ℝ => ((oneSidedDensity ε 0 u : ℝ))) = fun u => max (0 - ε * weilLagFunctionReal u) 0 := by
      funext u; unfold oneSidedDensity; rw [Real.coe_toNNReal']
    rw [this]
    exact (continuous_const.sub (continuous_weilLagFunctionReal.const_mul ε)).max continuous_const
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

/-- **Sub-exponential mass of the clipped density gives finite Laplace mass at every larger rate.**
If `∫_0^T max(εΦ,0) ≤ C e^{ηT}` for all `T ≥ 0`, then `laplaceMass (oneSidedMeasure ε 0) σ < ∞`
for every `σ > η`, `σ > 0`. -/
theorem laplaceMass_oneSidedMeasure_ne_top_of_integral_le {ε η σ C : ℝ}
    (hσ : 0 < σ) (hησ : η < σ)
    (hI : ∀ T : ℝ, 0 ≤ T → ∫ u in Icc (0:ℝ) T, ((oneSidedDensity ε 0 u : ℝ)) ≤ C * Real.exp (η * T)) :
    laplaceMass (oneSidedMeasure ε 0) σ ≠ ⊤ := by
  rw [laplaceMass_oneSided_eq]
  refine ENNReal.add_ne_top.mpr ⟨?_, laplaceMass_volume_ne_top hσ⟩
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_oneSidedDensity ε 0).coe_nnreal_ennreal hg]
  have hfg : ((fun u : ℝ => ((oneSidedDensity ε 0 u : ℝ≥0∞))) * fun u => ENNReal.ofReal (Real.exp (-σ * u)))
      = fun u : ℝ => ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u)) := rfl
  rw [hfg]
  -- `C ≥ 0` from `T = 1`
  have hC : 0 ≤ C := by
    have h1 := hI 1 zero_le_one
    have h0 : 0 ≤ ∫ u in Icc (0:ℝ) 1, ((oneSidedDensity ε 0 u : ℝ)) :=
      setIntegral_nonneg measurableSet_Icc fun u _ => NNReal.coe_nonneg _
    by_contra hneg
    have : C * Real.exp (η * 1) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (Real.exp_pos _)
    linarith
  -- the ratio of the geometric majorant
  set r : ℝ := Real.exp (-(σ - η)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hrdef, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  -- cover `(0,∞)` by the unit intervals `[n, n+1]`
  have hcover : Ioi (0:ℝ) ⊆ ⋃ n : ℕ, Icc (n:ℝ) (n + 1) := fun u hu =>
    mem_iUnion.mpr ⟨⌊u⌋₊, Nat.floor_le (le_of_lt hu), (Nat.lt_floor_add_one u).le⟩
  -- the block bound
  have hterm : ∀ n : ℕ,
      ∫⁻ u in Icc (n:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u))
        ≤ ENNReal.ofReal (C * Real.exp η * r ^ n) := by
    intro n
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    calc ∫⁻ u in Icc (n:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u))
        ≤ ∫⁻ u in Icc (n:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * n)) := by
          refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
          refine mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) _
          nlinarith [hu.1]
      _ = (∫⁻ u in Icc (n:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ≥0∞))) * ENNReal.ofReal (Real.exp (-σ * n)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ (∫⁻ u in Icc (0:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ≥0∞))) * ENNReal.ofReal (Real.exp (-σ * n)) :=
          mul_le_mul_left (lintegral_mono_set (Icc_subset_Icc hn0 le_rfl)) _
      _ = ENNReal.ofReal (∫ u in Icc (0:ℝ) (n + 1), ((oneSidedDensity ε 0 u : ℝ))) *
            ENNReal.ofReal (Real.exp (-σ * n)) := by
          congr 1
          rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_oneSidedDensity_zero_Icc ε _)
            (Filter.Eventually.of_forall fun u => NNReal.coe_nonneg _)]
          exact lintegral_congr fun u => (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal (C * Real.exp (η * (n + 1))) * ENNReal.ofReal (Real.exp (-σ * n)) := by
          gcongr
          exact hI _ (by positivity)
      _ = ENNReal.ofReal (C * Real.exp η * r ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  -- assemble
  have hsum : ∑' n : ℕ, ENNReal.ofReal (C * Real.exp η * r ^ n) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left _)]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top hsum ?_
  calc ∫⁻ u in Ioi (0:ℝ), ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u))
      ≤ ∫⁻ u in ⋃ n : ℕ, Icc (n:ℝ) (n + 1),
          ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u)) := lintegral_mono_set hcover
    _ ≤ ∑' n : ℕ, ∫⁻ u in Icc (n:ℝ) (n + 1),
          ((oneSidedDensity ε 0 u : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-σ * u)) := lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * Real.exp η * r ^ n) := ENNReal.tsum_le_tsum hterm

/-- **The integrated positive-part criterion (strip form).**  If for every rate `η > a` the primitive
of the positive part satisfies `∫_0^T Φ₊ ≤ C_η e^{ηT}`, `a ≥ 0`, then every zero has real part
`≤ ½ + a`. -/
theorem re_le_half_add_of_lagPositivePart_integral {a : ℝ} (ha0 : 0 ≤ a)
    (hI : ∀ η : ℝ, a < η → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ C * Real.exp (η * T)) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  refine re_le_half_add_of_lagPositivePart_laplace ha0 (fun σ hσ => ?_) q
  obtain ⟨C, hC⟩ := hI ((a + σ) / 2) (by linarith)
  exact laplaceMass_oneSidedMeasure_ne_top_of_integral_le (by linarith) (by linarith) hC

/-- **The integrated positive-part criterion.**  If the positive excursions of the lag function have
sub-exponential mass — for every `η > 0` there is `C` with `∫_0^T max(Φ, 0) ≤ C e^{ηT}` for all
`T ≥ 0` — then the Riemann hypothesis holds.  Under RH the primitive is bounded, so the criterion
is an equivalence. -/
theorem riemannHypothesis_of_lagPositivePart_integral_subexponential
    (hI : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ C * Real.exp (η * T)) : RiemannHypothesis := by
  refine riemannHypothesis_of_lagPositivePart_laplace fun σ hσ => ?_
  obtain ⟨C, hC⟩ := hI (σ / 2) (by positivity)
  exact laplaceMass_oneSidedMeasure_ne_top_of_integral_le hσ (by linarith) hC

/-- Under RH the primitive of the positive part is at most `(2 + γ − log 4π) T`. -/
theorem integral_lagPositivePart_le_of_riemannHypothesis (h : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ poleSharpConstant * T := by
  have hbound : ∀ u : ℝ, lagPositivePart u ≤ poleSharpConstant := by
    intro u
    rw [lagPositivePart_eq_max]
    have := norm_weilLagFunction_le_of_riemannHypothesis h u
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at this
    have h0 : 0 ≤ poleSharpConstant := le_trans (abs_nonneg _) this
    exact max_le ((le_abs_self _).trans this) h0
  calc ∫ u in Icc (0:ℝ) T, lagPositivePart u
      ≤ ∫ u in Icc (0:ℝ) T, poleSharpConstant := by
        refine setIntegral_mono_on (integrableOn_oneSidedDensity_zero_Icc (-1) T)
          (integrableOn_const (by simp)) measurableSet_Icc fun u _ => hbound u
    _ = poleSharpConstant * T := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]

/-- **Equivalence.**  RH holds iff the positive part of the lag function has sub-exponential primitive. -/
theorem riemannHypothesis_iff_lagPositivePart_integral_subexponential :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ C * Real.exp (η * T) := by
  constructor
  · intro h η hη
    refine ⟨poleSharpConstant / η, fun T hT => ?_⟩
    have h1 := integral_lagPositivePart_le_of_riemannHypothesis h hT
    have h0 : 0 ≤ poleSharpConstant := by
      have := norm_weilLagFunction_le_of_riemannHypothesis h 0
      exact le_trans (norm_nonneg _) this
    have hexp : η * T + 1 ≤ Real.exp (η * T) := by
      have := Real.add_one_le_exp (η * T); linarith
    calc ∫ u in Icc (0:ℝ) T, lagPositivePart u ≤ poleSharpConstant * T := h1
      _ ≤ poleSharpConstant / η * Real.exp (η * T) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hη]
        have h2 : poleSharpConstant * (η * T) ≤ poleSharpConstant * Real.exp (η * T) :=
          mul_le_mul_of_nonneg_left (by linarith) h0
        calc poleSharpConstant * T * η = poleSharpConstant * (η * T) := by ring
          _ ≤ _ := h2
  · exact riemannHypothesis_of_lagPositivePart_integral_subexponential

end

end RHTower
