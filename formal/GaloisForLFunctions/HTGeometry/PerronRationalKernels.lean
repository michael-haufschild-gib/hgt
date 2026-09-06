import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Perron integrals of rational kernels by Mellin inversion

For `Re a, Re b < σ`, `a ≠ b`, and `X > 0`,

`(1/2π) ∫ X^{σ+it} / ((σ+it−a)(σ+it−b)) dt = (X^a − X^b)/(a−b)` if `X > 1`, and `0` if `X ≤ 1`.

The window `y ↦ ((y^{−a} − y^{−b})/(a−b))·1_{(0,1)}(y)` has Mellin transform `1/((s−a)(s−b))` on
`Re s > max(Re a, Re b)`, its transform is integrable on vertical lines, and the window is continuous
on `(0,∞)`; Mathlib's Mellin inversion at `x = 1/X` evaluates the vertical integral.
-/

open MeasureTheory Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two-pole Perron window `((y^{−a} − y^{−b})/(a−b))·1_{(0,1)}(y)`. -/
def perronTwoPoleWindow (a b : ℂ) (y : ℝ) : ℂ :=
  Set.indicator (Ioo (0:ℝ) 1) (fun y : ℝ => ((y : ℂ) ^ (-a) - (y : ℂ) ^ (-b)) / (a - b)) y

theorem integral_Ioo_cpow {r : ℂ} (hr : -1 < r.re) :
    ∫ t in Ioo (0:ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) := by
  have h1 : r + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hr)]
  rw [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow h1]
  simp

theorem integrableOn_Ioo_cpow {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioo (0:ℝ) 1) := by
  have := (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  exact this.mono_set Ioo_subset_Ioc_self

/-- The Mellin integrand of the window is the indicator of an explicit power difference. -/
theorem cpow_smul_perronTwoPoleWindow (a b s : ℂ) :
    (fun t : ℝ => (t : ℂ) ^ (s - 1) • perronTwoPoleWindow a b t)
      = Set.indicator (Ioo (0:ℝ) 1)
          (fun t : ℝ => ((t : ℂ) ^ (s - 1 - a) - (t : ℂ) ^ (s - 1 - b)) / (a - b)) := by
  funext t
  unfold perronTwoPoleWindow
  by_cases ht : t ∈ Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    have e1 : (t : ℂ) ^ (s - 1 - a) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-a) := by
      rw [← Complex.cpow_add _ _ ht0]; ring_nf
    have e2 : (t : ℂ) ^ (s - 1 - b) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-b) := by
      rw [← Complex.cpow_add _ _ ht0]; ring_nf
    rw [e1, e2, smul_eq_mul]
    ring
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]

theorem mellin_perronTwoPoleWindow {a b s : ℂ} (ha : a.re < s.re) (hb : b.re < s.re)
    (hab : a ≠ b) :
    mellin (perronTwoPoleWindow a b) s = 1 / ((s - a) * (s - b)) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hsa : s - a ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp only [Complex.sub_re, Complex.zero_re] at this
    linarith
  have hsb : s - b ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp only [Complex.sub_re, Complex.zero_re] at this
    linarith
  have hra : -1 < (s - 1 - a).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hrb : -1 < (s - 1 - b).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  unfold mellin
  rw [cpow_smul_perronTwoPoleWindow, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0:ℝ) ∩ Ioo 0 1 = Ioo 0 1 from inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [integral_div, integral_sub (integrableOn_Ioo_cpow hra) (integrableOn_Ioo_cpow hrb),
    integral_Ioo_cpow hra, integral_Ioo_cpow hrb]
  have e1 : s - 1 - a + 1 = s - a := by ring
  have e2 : s - 1 - b + 1 = s - b := by ring
  rw [e1, e2]
  field_simp
  ring

theorem mellinConvergent_perronTwoPoleWindow {a b s : ℂ} (ha : a.re < s.re) (hb : b.re < s.re) :
    MellinConvergent (perronTwoPoleWindow a b) s := by
  have hra : -1 < (s - 1 - a).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hrb : -1 < (s - 1 - b).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  unfold MellinConvergent
  rw [cpow_smul_perronTwoPoleWindow]
  have hI : IntegrableOn (fun t : ℝ => ((t : ℂ) ^ (s - 1 - a) - (t : ℂ) ^ (s - 1 - b)) / (a - b))
      (Ioo (0:ℝ) 1) :=
    ((integrableOn_Ioo_cpow hra).sub (integrableOn_Ioo_cpow hrb)).div_const (a - b)
  exact (hI.integrable_indicator measurableSet_Ioo).integrableOn

/-- On the vertical line `Re s = σ > Re c`, `‖s − c‖² ≥ min(σ − Re c, 1)²·(1 + (t − Im c)²)`. -/
theorem one_div_normSq_line_le {σ : ℝ} {c : ℂ} (hc : c.re < σ) (t : ℝ) :
    1 / ‖(σ : ℂ) + t * I - c‖ ^ 2 ≤ (1 / min (σ - c.re) 1 ^ 2) * (1 / (1 + (t - c.im) ^ 2)) := by
  set m : ℝ := min (σ - c.re) 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmδ : m ≤ σ - c.re := min_le_left _ _
  have hw : (σ : ℂ) + t * I - c = ((σ - c.re : ℝ) : ℂ) + ((t - c.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hw, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith [sq_nonneg (t - c.im), sq_nonneg m, mul_le_mul_of_nonneg_left hmδ hm0.le,
    mul_le_mul_of_nonneg_left hm1 hm0.le, mul_self_nonneg (t - c.im)]

theorem verticalIntegrable_twoPole {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ) :
    VerticalIntegrable (fun s : ℂ => 1 / ((s - a) * (s - b))) σ := by
  unfold VerticalIntegrable
  have hne : ∀ (c : ℂ), c.re < σ → ∀ t : ℝ, (σ : ℂ) + t * I - c ≠ 0 := by
    intro c hc t h
    have := congrArg Complex.re h
    simp at this; linarith
  have hcont : Continuous (fun t : ℝ => 1 / (((σ : ℂ) + t * I - a) * ((σ : ℂ) + t * I - b))) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro t; exact mul_ne_zero (hne a ha t) (hne b hb t)
  set Ca : ℝ := 1 / min (σ - a.re) 1 ^ 2
  set Cb : ℝ := 1 / min (σ - b.re) 1 ^ 2
  have hint : Integrable (fun t : ℝ =>
      (Ca / 2) * (1 / (1 + (t - a.im) ^ 2)) + (Cb / 2) * (1 / (1 + (t - b.im) ^ 2))) := by
    have h1 := (integrable_inv_one_add_sq.comp_sub_right a.im).const_mul (Ca / 2)
    have h2 := (integrable_inv_one_add_sq.comp_sub_right b.im).const_mul (Cb / 2)
    simp only [one_div]
    exact h1.add h2
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_div, norm_one, norm_mul]
  set A := ‖(σ : ℂ) + t * I - a‖ with hA
  set B := ‖(σ : ℂ) + t * I - b‖ with hB
  have hA0 : 0 < A := norm_pos_iff.mpr (hne a ha t)
  have hB0 : 0 < B := norm_pos_iff.mpr (hne b hb t)
  have hAle := one_div_normSq_line_le ha t
  have hBle := one_div_normSq_line_le hb t
  rw [← hA] at hAle
  rw [← hB] at hBle
  -- AM–GM: 1/(AB) ≤ (1/A² + 1/B²)/2
  have hamgm : 1 / (A * B) ≤ (1 / A ^ 2 + 1 / B ^ 2) / 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (A - B), mul_pos hA0 hB0]
  calc 1 / (A * B) ≤ (1 / A ^ 2 + 1 / B ^ 2) / 2 := hamgm
    _ ≤ (Ca * (1 / (1 + (t - a.im) ^ 2)) + Cb * (1 / (1 + (t - b.im) ^ 2))) / 2 := by
        gcongr
    _ = (Ca / 2) * (1 / (1 + (t - a.im) ^ 2)) + (Cb / 2) * (1 / (1 + (t - b.im) ^ 2)) := by ring

/-- The window is continuous at every positive point (the two branches agree at `y = 1`). -/
theorem continuousAt_perronTwoPoleWindow (a b : ℂ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (perronTwoPoleWindow a b) y := by
  set g : ℝ → ℂ := fun y : ℝ => ((y : ℂ) ^ (-a) - (y : ℂ) ^ (-b)) / (a - b) with hg
  have hgc : ContinuousAt g y := by
    apply ContinuousAt.div_const
    exact (continuousAt_ofReal_cpow_const y (-a) (Or.inr hy.ne')).sub
      (continuousAt_ofReal_cpow_const y (-b) (Or.inr hy.ne'))
  rcases lt_trichotomy y 1 with hlt | heq | hgt
  · have hmem : Ioo (0:ℝ) 1 ∈ 𝓝 y := Ioo_mem_nhds hy hlt
    refine hgc.congr (Filter.eventuallyEq_of_mem hmem fun z hz => ?_)
    simp [perronTwoPoleWindow, Set.indicator_of_mem hz, hg]
  · subst heq
    have hg1 : g 1 = 0 := by simp [hg]
    rw [ContinuousAt, show perronTwoPoleWindow a b 1 = 0 by
      simp [perronTwoPoleWindow, Set.indicator_of_notMem]]
    refine squeeze_zero_norm' (a := fun z => ‖g z‖) (Filter.Eventually.of_forall fun z => ?_) ?_
    · show ‖perronTwoPoleWindow a b z‖ ≤ ‖g z‖
      unfold perronTwoPoleWindow
      by_cases hz : z ∈ Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, norm_zero]; exact norm_nonneg _
    · have := hgc.tendsto
      rw [hg1] at this
      exact (tendsto_zero_iff_norm_tendsto_zero.mp this)
  · have hmem : Ioi (1:ℝ) ∈ 𝓝 y := Ioi_mem_nhds hgt
    refine (continuousAt_const (y := (0 : ℂ))).congr (Filter.eventuallyEq_of_mem hmem fun z hz => ?_)
    have : z ∉ Ioo (0:ℝ) 1 := fun h => absurd h.2 (not_lt.mpr (le_of_lt hz))
    simp [perronTwoPoleWindow, Set.indicator_of_notMem this]

/-- **Perron integral of a two-pole kernel.** -/
theorem perron_twoPole {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (hab : a ≠ b) {X : ℝ} (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) /
          ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))
      = if 1 < X then ((X : ℂ) ^ a - (X : ℂ) ^ b) / (a - b) else 0 := by
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := by intro t; simp
  have hconv : MellinConvergent (perronTwoPoleWindow a b) (σ : ℂ) :=
    mellinConvergent_perronTwoPoleWindow (by simpa using ha) (by simpa using hb)
  have hvert : VerticalIntegrable (mellin (perronTwoPoleWindow a b)) σ := by
    have := verticalIntegrable_twoPole ha hb
    unfold VerticalIntegrable at this ⊢
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [mellin_perronTwoPoleWindow (by rw [hre]; exact ha) (by rw [hre]; exact hb) hab]
  have hx : (0:ℝ) < 1 / X := by positivity
  have key := mellinInv_mellin_eq σ (perronTwoPoleWindow a b) hx hconv hvert
    (continuousAt_perronTwoPoleWindow a b hx)
  unfold mellinInv at key
  have hbase : ∀ t : ℝ, ((1 / X : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) = (X : ℂ) ^ ((σ : ℂ) + t * I) := by
    intro t
    rw [one_div, Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hX.le]; exact Real.pi_pos.ne'.symm),
      Complex.cpow_neg, inv_inv]
  have hintegrand : (fun t : ℝ => ((1 / X : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) •
      mellin (perronTwoPoleWindow a b) ((σ : ℂ) + t * I))
      = fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
          ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b)) := by
    funext t
    rw [hbase, mellin_perronTwoPoleWindow (by rw [hre]; exact ha) (by rw [hre]; exact hb) hab,
      smul_eq_mul, mul_one_div]
  rw [hintegrand] at key
  rw [key]
  unfold perronTwoPoleWindow
  by_cases h1 : 1 < X
  · have hmem : 1 / X ∈ Ioo (0:ℝ) 1 := ⟨hx, by rw [div_lt_one hX]; exact h1⟩
    rw [if_pos h1, Set.indicator_of_mem hmem]
    congr 1
    rw [one_div, Complex.ofReal_inv, Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hX.le]; exact Real.pi_pos.ne'.symm),
      Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hX.le]; exact Real.pi_pos.ne'.symm),
      Complex.cpow_neg, Complex.cpow_neg, inv_inv, inv_inv]
  · have hnot : 1 / X ∉ Ioo (0:ℝ) 1 := by
      intro h; exact h1 ((div_lt_one hX).mp h.2)
    rw [if_neg h1, Set.indicator_of_notMem hnot]

/-- The two-pole integrand is dominated uniformly for `b` in the ball of radius `(σ − Re a)/2`
about `a`: there `‖s − b‖ ≥ ‖s − a‖/2` on the line. -/
theorem norm_twoPole_integrand_le {σ : ℝ} {a b : ℂ} (ha : a.re < σ)
    (hb : ‖b - a‖ ≤ (σ - a.re) / 2) {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ‖(X : ℂ) ^ ((σ : ℂ) + t * I) / ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))‖
      ≤ (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2)) * (1 / (1 + (t - a.im) ^ 2)) := by
  have hδ : 0 < σ - a.re := by linarith
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsa : σ - a.re ≤ ‖s - a‖ := by
    have : (s - a).re = σ - a.re := by simp [hs]
    rw [← this]; exact Complex.re_le_norm _
  have hsb : ‖s - a‖ / 2 ≤ ‖s - b‖ := by
    have h2 := norm_sub_norm_le (s - a) (s - b)
    rw [show s - a - (s - b) = b - a by ring] at h2
    linarith
  have hsa0 : 0 < ‖s - a‖ := by linarith
  have hsb0 : 0 < ‖s - b‖ := by linarith
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, show ((σ : ℂ) + t * I).re = σ by simp]
  have hsq := one_div_normSq_line_le ha t
  rw [← hs] at hsq
  calc X ^ σ / (‖s - a‖ * ‖s - b‖) ≤ X ^ σ / (‖s - a‖ * (‖s - a‖ / 2)) := by
        gcongr
    _ = X ^ σ * 2 * (1 / ‖s - a‖ ^ 2) := by field_simp
    _ ≤ X ^ σ * 2 * ((1 / min (σ - a.re) 1 ^ 2) * (1 / (1 + (t - a.im) ^ 2))) := by
        gcongr
    _ = (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2)) * (1 / (1 + (t - a.im) ^ 2)) := by ring

/-- **Perron integral of a double pole.**  For `Re a < σ` and `X > 1`,
`(1/2π) ∫ X^{σ+it}/(σ+it−a)² dt = X^a log X`, obtained from the two-pole formula as `b → a` by
dominated convergence. -/
theorem perron_doublePole {σ : ℝ} {a : ℂ} (ha : a.re < σ) {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) - a) ^ 2
      = (X : ℂ) ^ a * Complex.log X := by
  have hX0 : 0 < X := by linarith
  have hδ : 0 < σ - a.re := by linarith
  set F : ℂ → ℂ := fun b => (1 / (2 * Real.pi) : ℝ) •
    ∫ t : ℝ, (X : ℂ) ^ ((σ : ℂ) + t * I) / ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b)) with hF
  -- the two-pole values converge to the derivative of `b ↦ X^b` at `a`
  have hslope : Tendsto (fun b : ℂ => ((X : ℂ) ^ a - (X : ℂ) ^ b) / (a - b)) (𝓝[≠] a)
      (𝓝 ((X : ℂ) ^ a * Complex.log X)) := by
    have hd : HasDerivAt (fun b : ℂ => (X : ℂ) ^ b) ((X : ℂ) ^ a * Complex.log X * 1) a :=
      (hasDerivAt_id a).const_cpow (Or.inl (by exact_mod_cast hX0.ne'))
    rw [mul_one] at hd
    have := hasDerivAt_iff_tendsto_slope.mp hd
    refine this.congr fun b => ?_
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    rw [show (X : ℂ) ^ a - (X : ℂ) ^ b = -((X : ℂ) ^ b - (X : ℂ) ^ a) by ring,
      show a - b = -(b - a) by ring, neg_div_neg_eq, div_eq_inv_mul]
  have hFval : ∀ᶠ b in 𝓝[≠] a, F b = ((X : ℂ) ^ a - (X : ℂ) ^ b) / (a - b) := by
    have hball : Metric.ball a ((σ - a.re) / 2) ∈ 𝓝[≠] a :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds a (by positivity))
    filter_upwards [hball, self_mem_nhdsWithin] with b hb hba
    have hbre : b.re < σ := by
      have h1 : ‖b - a‖ < (σ - a.re) / 2 := by simpa [dist_eq_norm] using hb
      have h2 : |(b - a).re| ≤ ‖b - a‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      linarith [abs_le.mp h2 |>.2]
    rw [hF]
    simp only
    rw [perron_twoPole ha hbre (Ne.symm hba) hX0, if_pos hX]
  -- dominated convergence gives `F b → F a`
  have hFlim : Tendsto F (𝓝[≠] a) (𝓝 (F a)) := by
    rw [hF]
    simp only
    refine Tendsto.const_smul ?_ _
    have hball : Metric.closedBall a ((σ - a.re) / 2) ∈ 𝓝[≠] a :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds a (by positivity))
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2)) * (1 / (1 + (t - a.im) ^ 2))) ?_ ?_ ?_ ?_
    · filter_upwards [hball] with b hb
      have hbre : b.re < σ := by
        have h1 : ‖b - a‖ ≤ (σ - a.re) / 2 := by simpa [dist_eq_norm] using hb
        have h2 : |(b - a).re| ≤ ‖b - a‖ := Complex.abs_re_le_norm _
        rw [Complex.sub_re] at h2
        linarith [abs_le.mp h2 |>.2]
      have hne : ∀ (c : ℂ), c.re < σ → ∀ t : ℝ, (σ : ℂ) + t * I - c ≠ 0 := by
        intro c hc t h
        have := congrArg Complex.re h
        simp at this; linarith
      refine Continuous.aestronglyMeasurable ?_
      have hcp : Continuous (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I)) :=
        (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + t * I)).const_cpow
          (Or.inl (by exact_mod_cast hX0.ne'))
      apply Continuous.div hcp
      · fun_prop
      · intro t; exact mul_ne_zero (hne a ha t) (hne b hbre t)
    · filter_upwards [hball] with b hb
      refine Filter.Eventually.of_forall fun t => ?_
      exact norm_twoPole_integrand_le ha (by simpa [dist_eq_norm] using hb) hX0 t
    · have := (integrable_inv_one_add_sq.comp_sub_right a.im).const_mul
        (X ^ σ * 2 * (1 / min (σ - a.re) 1 ^ 2))
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [one_div]
    · refine Filter.Eventually.of_forall fun t => ?_
      have hne : (σ : ℂ) + t * I - a ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hca : ContinuousAt (fun b : ℂ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
          ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))) a := by
        refine ContinuousAt.div continuousAt_const
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) ?_
        exact mul_ne_zero hne hne
      exact hca.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto F (𝓝[≠] a) (𝓝 ((X : ℂ) ^ a * Complex.log X)) :=
    hslope.congr' (hFval.mono fun b hb => hb.symm)
  have := tendsto_nhds_unique hFlim hlim2
  rw [hF] at this
  simp only at this
  rw [← this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [sq]

/-- `‖X^{σ+it}‖ = X^σ` is constant on the line, so the two-pole integrand is integrable. -/
theorem integrable_cpow_div_twoPole {σ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I) /
      ((((σ : ℂ) + t * I) - a) * (((σ : ℂ) + t * I) - b))) := by
  have hv := verticalIntegrable_twoPole ha hb
  unfold VerticalIntegrable at hv
  have hcp : Continuous (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I)) :=
    (by fun_prop : Continuous (fun t : ℝ => (σ : ℂ) + t * I)).const_cpow
      (Or.inl (by exact_mod_cast hX.ne'))
  have hbdd : ∀ t : ℝ, ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ X ^ σ := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  have := hv.bdd_mul hcp.aestronglyMeasurable (Filter.Eventually.of_forall hbdd)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  exact mul_one_div _ _

theorem integrable_cpow_div_doublePole {σ : ℝ} {a : ℂ} (ha : a.re < σ) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ ((σ : ℂ) + t * I) / (((σ : ℂ) + t * I) - a) ^ 2) := by
  have := integrable_cpow_div_twoPole ha ha hX
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp [sq]

/-! ## The kernel `X^s/(s(s−1))` on the line `Re s = 2` -/

/-- The point `2 + it` of the line `Re s = 2`. -/
def lineTwo (t : ℝ) : ℂ := ((2 : ℝ) : ℂ) + t * I

theorem lineTwo_re (t : ℝ) : (lineTwo t).re = 2 := by simp [lineTwo]

theorem lineTwo_sub_ne_zero {a : ℂ} (ha : a.re < 2) (t : ℝ) : lineTwo t - a ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [Complex.sub_re, lineTwo_re, Complex.zero_re] at this
  linarith

theorem lineTwo_ne_zero (t : ℝ) : lineTwo t ≠ 0 := by
  simpa using lineTwo_sub_ne_zero (a := 0) (by norm_num) t

theorem lineTwo_sub_one_ne_zero (t : ℝ) : lineTwo t - 1 ≠ 0 :=
  lineTwo_sub_ne_zero (by norm_num) t

theorem integrable_lineTwo_shift {a : ℂ} (ha : a.re < 2) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / ((lineTwo t - a) * (lineTwo t - 1))) :=
  integrable_cpow_div_twoPole (σ := 2) (a := a) (b := 1) ha (by norm_num) hX

theorem integrable_lineTwo_basic {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))) := by
  have := integrable_lineTwo_shift (a := 0) (by norm_num) hX
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_zero]

theorem integrable_lineTwo_sq {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / lineTwo t ^ 2) := by
  have := integrable_cpow_div_doublePole (σ := 2) (a := 0) (by norm_num) hX
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_zero, lineTwo]

theorem integrable_lineTwo_sub_one_sq {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t - 1) ^ 2) :=
  integrable_cpow_div_doublePole (σ := 2) (a := 1) (by norm_num) hX

/-- `(1/2π)∫ X^s/((s−a)(s−1)) dt = (X^a − X)/(a−1)` for `X > 1` (and `0` for `X ≤ 1`). -/
theorem perron_lineTwo_shift {a : ℂ} (ha : a.re < 2) (ha1 : a ≠ 1) {X : ℝ} (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / ((lineTwo t - a) * (lineTwo t - 1))
      = if 1 < X then ((X : ℂ) ^ a - X) / (a - 1) else 0 := by
  have h := perron_twoPole (σ := 2) (a := a) (b := 1) ha (by norm_num) ha1 hX
  unfold lineTwo
  simpa only [Complex.cpow_one] using h

/-- `(1/2π)∫ X^s/(s(s−1)) dt = (X − 1)_+`. -/
theorem perron_lineTwo_basic {X : ℝ} (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))
      = if 1 < X then (X : ℂ) - 1 else 0 := by
  have h := perron_lineTwo_shift (a := 0) (by norm_num) zero_ne_one hX
  simp only [sub_zero, Complex.cpow_zero, zero_sub, div_neg, div_one, neg_sub] at h
  exact h

/-- `(1/2π)∫ X^s/(s²(s−1)) dt = X − 1 − log X` for `X > 1`. -/
theorem perron_lineTwo_sq {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t ^ 2 * (lineTwo t - 1))
      = (X : ℂ) - 1 - Complex.log X := by
  have hX0 : 0 < X := by linarith
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  have hd := perron_doublePole (σ := 2) (a := 0) (by norm_num) hX
  simp only [Complex.cpow_zero, one_mul, sub_zero] at hd
  have hsplit : ∀ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t ^ 2 * (lineTwo t - 1))
      = (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1)) - (X : ℂ) ^ lineTwo t / lineTwo t ^ 2 := by
    intro t
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    field_simp
    ring
  simp_rw [hsplit]
  rw [integral_sub (integrable_lineTwo_basic hX0) (integrable_lineTwo_sq hX0), smul_sub, hb]
  rw [show (fun t : ℝ => (X : ℂ) ^ lineTwo t / lineTwo t ^ 2)
      = fun t : ℝ => (X : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I) ^ 2 from rfl, hd]

/-- `(1/2π)∫ X^s/(s(s−1)²) dt = X log X − X + 1` for `X > 1`. -/
theorem perron_lineTwo_sub_one_sq {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2)
      = (X : ℂ) * Complex.log X - X + 1 := by
  have hX0 : 0 < X := by linarith
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  have hd := perron_doublePole (σ := 2) (a := 1) (by norm_num) hX
  simp only [Complex.cpow_one] at hd
  have hsplit : ∀ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1) ^ 2)
      = (X : ℂ) ^ lineTwo t / (lineTwo t - 1) ^ 2 - (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1)) := by
    intro t
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    field_simp
    ring
  simp_rw [hsplit]
  rw [integral_sub (integrable_lineTwo_sub_one_sq hX0) (integrable_lineTwo_basic hX0), smul_sub, hb]
  rw [show (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t - 1) ^ 2)
      = fun t : ℝ => (X : ℂ) ^ (((2 : ℝ) : ℂ) + t * I) / (((2 : ℝ) : ℂ) + t * I - 1) ^ 2 from rfl, hd]
  ring

/-- `(1/2π)∫ X^s/((s−a)s(s−1)) dt = (1/a)((X^a − X)/(a−1) − (X−1))` for `a ∉ {0,1}`, `Re a < 2`,
`X > 1`. -/
theorem perron_lineTwo_threePole {a : ℂ} (ha : a.re < 2) (ha0 : a ≠ 0) (ha1 : a ≠ 1) {X : ℝ}
    (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, (X : ℂ) ^ lineTwo t / ((lineTwo t - a) * lineTwo t * (lineTwo t - 1))
      = (1 / a) * (((X : ℂ) ^ a - X) / (a - 1) - (X - 1)) := by
  have hX0 : 0 < X := by linarith
  have hb := perron_lineTwo_basic hX0
  rw [if_pos hX] at hb
  have hs := perron_lineTwo_shift ha ha1 hX0
  rw [if_pos hX] at hs
  have hsplit : ∀ t : ℝ, (X : ℂ) ^ lineTwo t / ((lineTwo t - a) * lineTwo t * (lineTwo t - 1))
      = (1 / a) * ((X : ℂ) ^ lineTwo t / ((lineTwo t - a) * (lineTwo t - 1))
          - (X : ℂ) ^ lineTwo t / (lineTwo t * (lineTwo t - 1))) := by
    intro t
    have h0 := lineTwo_ne_zero t
    have h1 := lineTwo_sub_one_ne_zero t
    have h2 := lineTwo_sub_ne_zero ha t
    field_simp
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, integral_sub (integrable_lineTwo_shift ha hX0) (integrable_lineTwo_basic hX0),
    ← mul_smul_comm, smul_sub, hb, hs]

/-! ## The integrable majorant `(1 + t²)^{−3/4}` and the two-centre bound -/

theorem integrable_one_add_sq_rpow_neg_three_quarters :
    Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 4 : ℝ))) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2)
    (by rw [Module.finrank_self]; norm_num)
  refine this.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  norm_num

/-- `(1 + |t|)^{−3/2} ≤ (1 + t²)^{−3/4}`. -/
theorem one_add_abs_rpow_le (t : ℝ) :
    (1 + |t|) ^ (-(3 / 2 : ℝ)) ≤ (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have h2 : ((1 + |t|) ^ 2) ^ (-(3 / 4 : ℝ)) ≤ (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  rw [← Real.rpow_natCast_mul (by positivity)] at h2
  norm_num at h2
  exact h2

/-- **Two-centre majorant.**  For all real `γ, t`,
`1/((1+|t−γ|)(1+|t|)) ≤ √2 (1+|γ|)^{−1/2} ((1+t²)^{−3/4} + (1+(t−γ)²)^{−3/4})`. -/
theorem two_centre_majorant (γ t : ℝ) :
    1 / ((1 + |t - γ|) * (1 + |t|)) ≤ Real.sqrt 2 * (1 + |γ|) ^ (-(1 / 2 : ℝ)) *
      ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - γ) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  set u : ℝ := 1 + |t| with hu
  set v : ℝ := 1 + |t - γ| with hv
  set w : ℝ := 1 + |γ| with hw
  have hu1 : 1 ≤ u := by simp [hu]
  have hv1 : 1 ≤ v := by simp [hv]
  have hw1 : 1 ≤ w := by simp [hw]
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hw0 : 0 < w := by linarith
  have huv : w ≤ u + v := by
    have := abs_sub_abs_le_abs_sub t (t - γ)
    have h2 : |t - (t - γ)| = |γ| := by ring_nf
    have h3 : |γ| ≤ |t| + |t - γ| := by
      calc |γ| = |t - (t - γ)| := h2.symm
        _ ≤ |t| + |t - γ| := abs_sub _ _
    linarith
  -- core: 1/(uv) ≤ √2 w^{-1/2} (u^{-3/2} + v^{-3/2})
  have hcore : 1 / (u * v) ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) *
      (u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ))) := by
    -- reduce to m := min u v
    set m : ℝ := min u v with hm
    have hm0 : 0 < m := lt_min hu0 hv0
    have hmu : m ≤ u := min_le_left _ _
    have hmv : m ≤ v := min_le_right _ _
    have hmin : m ^ (-(3 / 2 : ℝ)) ≤ u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ)) := by
      rcases min_choice u v with h | h
      · rw [hm, h]; linarith [Real.rpow_nonneg hv0.le (-(3 / 2 : ℝ))]
      · rw [hm, h]; linarith [Real.rpow_nonneg hu0.le (-(3 / 2 : ℝ))]
    -- key: m^{3/2} w^{1/2} ≤ √2 u v, from m³ w ≤ 2 u² v²
    have hkey : m ^ (3 / 2 : ℝ) * w ^ (1 / 2 : ℝ) ≤ Real.sqrt 2 * (u * v) := by
      have hmw : m * w ≤ 2 * (u * v) := by
        rcases le_total u v with h | h
        · rw [hm, min_eq_left h]; nlinarith
        · rw [hm, min_eq_right h]; nlinarith
      have hm2 : m * m ≤ u * v := by nlinarith
      have hsq : (m ^ (3 / 2 : ℝ) * w ^ (1 / 2 : ℝ)) ^ 2 ≤ (Real.sqrt 2 * (u * v)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul hm0.le, ← Real.rpow_mul hw0.le]
        norm_num
        nlinarith [mul_le_mul hm2 hmw (by positivity) (by positivity)]
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at this
    have hpos : 0 < w ^ (1 / 2 : ℝ) * m ^ (3 / 2 : ℝ) := by positivity
    have h1 : 1 / (u * v) ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) * m ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hw0.le, Real.rpow_neg hm0.le, mul_assoc, ← mul_inv, ← div_eq_mul_inv,
        div_le_div_iff₀ (by positivity) hpos, one_mul, mul_comm (w ^ _)]
      exact hkey
    calc 1 / (u * v) ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) * m ^ (-(3 / 2 : ℝ)) := h1
      _ ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) * (u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ))) := by
          gcongr
  calc 1 / ((1 + |t - γ|) * (1 + |t|)) = 1 / (u * v) := by rw [mul_comm]
    _ ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) * (u ^ (-(3 / 2 : ℝ)) + v ^ (-(3 / 2 : ℝ))) := hcore
    _ ≤ Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - γ) ^ 2) ^ (-(3 / 4 : ℝ))) := by
        gcongr
        · exact one_add_abs_rpow_le t
        · exact one_add_abs_rpow_le (t - γ)

end

end GaloisForLFunctions.HTGeometry
