import GaloisForLFunctions.RHTower.FermiNymanHaarApproximationEquivalence
import GaloisForLFunctions.RHTower.FermiNymanBeurlingWitnessSignature

/-!
# Germ rigidity of Fermi witnesses and local completeness of the alternating generators

For the alternating Nyman–Beurling system `φ_a(t) = {1/(at)} − 2{1/(2at)}` (`a ≥ 1`) on `(0,1]`, a
witness is a square-integrable function orthogonal to every generator.  The Riemann hypothesis is
the statement that every witness is dyadically self-similar, equivalently that the dyadic Haar target
lies in the closed span of the generators.

This module isolates the part of that statement which holds unconditionally: **a witness is
determined by its germ at `t = 0`.**

* A continuous witness vanishing on `(0, δ]` is bounded, hence self-similar (Mellin exponent zero),
  hence zero: `w(t) = w(t/2^k)` with `t/2^k ≤ δ`.
* A measurable square-integrable witness vanishing a.e. on `(0, δ]` vanishes a.e.  Its dilation
  averages `w_η(t) = η⁻¹ t ∫_{t/(1+η)}^{t} w(u) u⁻² du` are continuous witnesses vanishing on `(0, δ]`,
  so they vanish identically; this forces `∫_s^t w(u) u⁻² du = 0` for all `0 < s < t ≤ 1`, and the
  Lebesgue differentiation theorem gives `w = 0` a.e.
* Self-similarity propagates from the germ: if `w(t/2) = w(t)` on `(0, δ]` then on `(0, 1]`, because
  `w − w(·/2)` is again a witness.
* **Local completeness.**  For every `δ ∈ (0,1)` the restrictions of the generators to `(δ, 1]` span
  a dense subspace of `L²(δ, 1]`: an element of the orthogonal complement, extended by zero, is a
  witness vanishing on `(0, δ]`.  Consequently every square-integrable function on `(0,1]` is, on
  `(δ, 1]`, an `L²`-limit of finite generator combinations.

Thus no obstruction to the Haar approximation (or to the approximation of any target) lives in the
bulk `(δ, 1]`; the whole content of the Riemann hypothesis in this system is the control of the
approximants near `t = 0`, equivalently the growth of witnesses at the origin.

The final section records the exact factorisation of the Haar target's Mellin transform,
`(1 − 2^{1−s})/s = I(s) · √2 (1 − 2^{−s})/s` with `I(s) = (1 − 2^{1−s})/(√2 (1 − 2^{−s}))` of modulus
one on the critical line: both sides of the alternating system carry the same unimodular dyadic
factor, and the generators' Mellin transforms are `−a^{−s} I(s) · √2(1 − 2^{−s}) ζ(s)/s`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

/-! ## Continuous witnesses: unique continuation from the origin -/

/-- Iterating the dyadic self-similarity: `w(t/2^k) = w(t)`. -/
theorem IsFermiNymanWitness.eq_comp_div_two_pow {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {M : ℝ} (hM : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (k : ℕ) :
    w (t / 2 ^ k) = w t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : t / 2 ^ k ∈ Ioc (0 : ℝ) 1 := by
      refine ⟨div_pos ht.1 (by positivity), ?_⟩
      rw [div_le_one (by positivity)]
      exact ht.2.trans (one_le_pow₀ (by norm_num))
    have h := hw.selfSimilar_of_bounded hM hmem
    rw [← ih, ← h, pow_succ, div_div]

/-- **Unique continuation from the origin.**  A continuous witness vanishing on `(0, δ]` vanishes
on all of `(0, 1]`. -/
theorem IsFermiNymanWitness.eq_zero_of_eqOn_zero {w : ℝ → ℂ} (hw : IsFermiNymanWitness w)
    {δ : ℝ} (hδ : 0 < δ) (h0 : ∀ t ∈ Ioc (0 : ℝ) δ, w t = 0) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w t = 0 := by
  -- the witness is bounded: zero below `δ`, continuous on the compact `[δ, 1]`
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn
    (hw.1.mono (fun x hx => ⟨lt_of_lt_of_le hδ hx.1, hx.2⟩))
  have hM : ∀ u ∈ Ioc (0 : ℝ) 1, ‖w u‖ ≤ max C 0 := by
    intro u hu
    by_cases hle : u ≤ δ
    · rw [h0 u ⟨hu.1, hle⟩, norm_zero]; exact le_max_right _ _
    · exact (hC u ⟨le_of_not_ge hle, hu.2⟩).trans (le_max_left _ _)
  -- choose `k` with `t / 2^k ≤ δ`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t / 2 ^ k ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := δ / t) (y := (1 / 2 : ℝ))
      (div_pos hδ ht.1) (by norm_num)
    refine ⟨n, ?_⟩
    have h1 : t / 2 ^ n = t * (1 / 2) ^ n := by rw [one_div_pow, mul_one_div]
    have h2 : t * (δ / t) = δ := mul_div_cancel₀ δ ht.1.ne'
    rw [h1, ← h2]
    exact mul_le_mul_of_nonneg_left hn.le ht.1.le
  rw [← hw.eq_comp_div_two_pow hM ht k]
  exact h0 _ ⟨div_pos ht.1 (by positivity), hk⟩

/-- **Propagation of self-similarity.**  If a witness is dyadically self-similar on `(0, δ]`, it is
self-similar on `(0, 1]`: the difference `w − w(·/2)` is a witness vanishing on `(0, δ]`. -/
theorem IsFermiNymanWitness.selfSimilar_of_selfSimilar_near_zero {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Ioc (0 : ℝ) δ, w (t / 2) = w t) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    w (t / 2) = w t := by
  have hv : IsFermiNymanWitness (fun u => w u + (-1 : ℂ) * w (u / 2)) :=
    hw.add_smul (hw.dilate (μ := 2) (by norm_num)) (-1)
  have h0 : ∀ u ∈ Ioc (0 : ℝ) δ, w u + (-1 : ℂ) * w (u / 2) = 0 := by
    intro u hu
    rw [h u hu]; ring
  have := hv.eq_zero_of_eqOn_zero hδ h0 ht
  linear_combination -this

/-! ## Measurable square-integrable witnesses -/

/-- The dilation average of a function vanishing a.e. on `(0, δ]` vanishes on `(0, δ]`. -/
theorem dilationAverage_eq_zero_of_ae_eq_zero {w : ℝ → ℂ} {δ η : ℝ} (hη : 0 < η)
    (h0 : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) δ)), w u = 0) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) δ) :
    dilationAverage η w t = 0 := by
  unfold dilationAverage
  rw [integral_Icc_comp_div_eq_primitive hη ht.1]
  have hsub : Ioc (t / (1 + η)) t ⊆ Ioc (0 : ℝ) δ := fun u hu =>
    ⟨lt_trans (div_pos ht.1 (by linarith)) hu.1, hu.2.trans ht.2⟩
  have hz : ∀ᵐ u ∂(volume.restrict (Ioc (t / (1 + η)) t)), w u / (u : ℂ) ^ 2 = 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h0] with u hu
    rw [hu, zero_div]
  rw [integral_eq_zero_of_ae hz, mul_zero, mul_zero]

/-- **Interval integrals of `w(u)/u²` vanish** for a square-integrable witness vanishing a.e. on
`(0, δ]`: every dilation average is a continuous witness vanishing on `(0, δ]`, hence zero. -/
theorem IsL2FermiWitness.setIntegral_div_sq_eq_zero {w : ℝ → ℂ} (hw : IsL2FermiWitness w)
    {δ : ℝ} (hδ : 0 < δ) (h0 : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) δ)), w u = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht1 : t ≤ 1) :
    ∫ u in Ioc s t, w u / (u : ℂ) ^ 2 = 0 := by
  set η : ℝ := t / s - 1 with hηdef
  have hη : 0 < η := by
    rw [hηdef, sub_pos, lt_div_iff₀ hs, one_mul]; exact hst
  have ht0 : t ≠ 0 := (lt_trans hs hst).ne'
  have hts : t / (1 + η) = s := by
    rw [hηdef, add_sub_cancel, div_div_eq_mul_div, mul_div_cancel_left₀ s ht0]
  have hwit := hw.dilationAverage_isFermiNymanWitness hη
  have hvan : ∀ u ∈ Ioc (0 : ℝ) δ, dilationAverage η w u = 0 := fun u hu =>
    dilationAverage_eq_zero_of_ae_eq_zero hη h0 hu
  have hzero := hwit.eq_zero_of_eqOn_zero hδ hvan (t := t) ⟨lt_trans hs hst, ht1⟩
  unfold dilationAverage at hzero
  rw [integral_Icc_comp_div_eq_primitive hη (lt_trans hs hst), hts] at hzero
  rcases mul_eq_zero.1 hzero with h | h
  · exfalso
    exact hη.ne' (by exact_mod_cast inv_eq_zero.1 h)
  rcases mul_eq_zero.1 h with h | h
  · exfalso
    have : (t : ℂ) ≠ 0 := by exact_mod_cast (lt_trans hs hst).ne'
    exact this h
  · exact h

/-- Lebesgue differentiation on `(η, 1]`: an integrable function on the line whose integrals over
all intervals `(s, t] ⊆ (η, 1]` vanish is zero a.e. on `(η, 1)`. -/
theorem ae_eq_zero_on_Ioo_of_forall_setIntegral_Ioc_eq_zero {g : ℝ → ℂ} (hg : Integrable g)
    {η : ℝ}
    (hint : ∀ s t : ℝ, η < s → s < t → t ≤ 1 → ∫ u in Ioc s t, g u = 0) :
    ∀ᵐ x ∂volume, x ∈ Ioo η 1 → g x = 0 := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ)
    hg.locallyIntegrable 1
  filter_upwards [hdiff] with x hx hxmem
  have hlim : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) (𝓝[>] 0) (𝓝 (g x)) :=
    hx (fun _ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact Metric.mem_closedBall_self (by rw [one_mul]; exact le_of_lt hr))
  have hev : (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos : 0 < min (x - η) (1 - x) := lt_min (by linarith [hxmem.1]) (by linarith [hxmem.2])
    have hIio : Iio (min (x - η) (1 - x)) ∈ 𝓝[>] (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpos)
    filter_upwards [self_mem_nhdsWithin, hIio] with r hr hrlt
    have hr0 : 0 < r := hr
    have hr1 : r < x - η := lt_of_lt_of_le hrlt (min_le_left _ _)
    have hr2 : r < 1 - x := lt_of_lt_of_le hrlt (min_le_right _ _)
    rw [setAverage_eq, Real.closedBall_eq_Icc, integral_Icc_eq_integral_Ioc,
      hint (x - r) (x + r) (by linarith) (by linarith) (by linarith), smul_zero]
  have hlim0 : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  exact tendsto_nhds_unique hlim hlim0

/-- **Unique continuation from the origin for square-integrable witnesses.**  A measurable
square-integrable witness vanishing a.e. on `(0, δ]` vanishes a.e. on `(0, 1]`. -/
theorem IsL2FermiWitness.ae_eq_zero_of_ae_eq_zero_near_zero {w : ℝ → ℂ} (hw : IsL2FermiWitness w)
    {δ : ℝ} (hδ : 0 < δ) (h0 : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) δ)), w u = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), w t = 0 := by
  have hwi : IntegrableOn w (Ioc 0 1) :=
    ((memLp_two_iff_integrable_sq_norm hw.measurable.aestronglyMeasurable).mpr hw.sq).integrable
      (by norm_num)
  -- on every `(η, 1)` with `η = 1/(n+2)`
  have hslice : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ Ioo (1 / ((n : ℝ) + 2)) 1 → w x = 0 := by
    intro n
    set η : ℝ := 1 / ((n : ℝ) + 2) with hηdef
    have hη : 0 < η := by positivity
    have hη1 : η < 1 := by
      rw [hηdef, div_lt_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    set g : ℝ → ℂ := (Ioc η 1).indicator (fun u => w u / (u : ℂ) ^ 2) with hgdef
    have hgint : Integrable g := by
      rw [hgdef, integrable_indicator_iff measurableSet_Ioc]
      have hmeas : Measurable (fun u : ℝ => w u / (u : ℂ) ^ 2) :=
        hw.measurable.div (Complex.measurable_ofReal.pow_const 2)
      refine ((hwi.mono_set (Ioc_subset_Ioc_left hη.le)).norm.const_mul (η ^ 2)⁻¹).mono'
        hmeas.aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun u hu => ?_
      have hu : η < u := hu.1
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        div_eq_mul_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact inv_anti₀ (by positivity) (by nlinarith)
    have hint : ∀ s t : ℝ, η < s → s < t → t ≤ 1 → ∫ u in Ioc s t, g u = 0 := by
      intro s t hs hst ht1
      have hsub : Ioc s t ⊆ Ioc η 1 := Ioc_subset_Ioc hs.le ht1
      rw [hgdef, setIntegral_indicator measurableSet_Ioc, inter_eq_left.mpr hsub]
      exact hw.setIntegral_div_sq_eq_zero hδ h0 (lt_trans hη hs) hst ht1
    filter_upwards [ae_eq_zero_on_Ioo_of_forall_setIntegral_Ioc_eq_zero hgint hint]
      with x hx hxmem
    have hgx := hx hxmem
    rw [hgdef, indicator_of_mem (show x ∈ Ioc η 1 from ⟨hxmem.1, hxmem.2.le⟩)] at hgx
    rcases div_eq_zero_iff.1 hgx with h | h
    · exact h
    · exfalso
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (lt_trans hη hxmem.1).ne'
      exact hx0 (pow_eq_zero_iff (by norm_num) |>.1 h)
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hall := ae_all_iff.2 hslice
  have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [hall, hne1] with x hx hx1 hxmem
  have hxlt : x < 1 := lt_of_le_of_ne hxmem.2 hx1
  -- pick `n` with `1/(n+2) < x`
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
  refine hx n ⟨?_, hxlt⟩
  rw [div_lt_iff₀ (by positivity)]
  have := (div_lt_iff₀ hxmem.1).1 hn
  nlinarith [hxmem.1]

/-! ## Local completeness of the generators on `(δ, 1]` -/

theorem memLp_fermiNymanGen_Ioc_restrict {δ : ℝ} (a : ℝ) :
    MemLp (fermiNymanGen a) 2 (volume.restrict (Ioc δ 1)) := by
  haveI : Fact (volume (Ioc δ 1) < ⊤) := ⟨measure_Ioc_lt_top⟩
  exact MemLp.of_bound (measurable_fermiNymanGen a).aestronglyMeasurable 3
    (Eventually.of_forall (norm_fermiNymanGen_le a))

/-- The generator `φ_a` restricted to `(δ, 1]`, as an element of `L²(δ, 1]`. -/
def fermiGenLpOn (δ a : ℝ) : Lp ℂ 2 (volume.restrict (Ioc δ 1)) :=
  MemLp.toLp (fermiNymanGen a) (memLp_fermiNymanGen_Ioc_restrict a)

/-- The span of the restricted generators `φ_a|_{(δ,1]}`, `a ≥ 1`. -/
def fermiGenSpanOn (δ : ℝ) : Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioc δ 1))) :=
  Submodule.span ℂ (fermiGenLpOn δ '' Ici 1)

/-- An element of the orthogonal complement of the restricted span, extended by zero to `(0,1]`,
is a square-integrable witness vanishing on `(0, δ]`. -/
theorem exists_isL2FermiWitness_of_mem_orthogonal_on {δ : ℝ} (hδ : 0 < δ)
    {u : Lp ℂ 2 (volume.restrict (Ioc δ 1))} (hu : u ∈ (fermiGenSpanOn δ)ᗮ) :
    ∃ w : ℝ → ℂ, IsL2FermiWitness w ∧ (∀ t ∈ Ioc (0 : ℝ) δ, w t = 0) ∧
      (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioc δ 1)] w := by
  set w' : ℝ → ℂ := (Lp.aestronglyMeasurable u).mk u with hw'def
  have hae : (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioc δ 1)] w' :=
    (Lp.aestronglyMeasurable u).ae_eq_mk
  have hmeas' : Measurable w' := (Lp.aestronglyMeasurable u).stronglyMeasurable_mk.measurable
  have hmem' : MemLp w' 2 (volume.restrict (Ioc δ 1)) := (Lp.memLp u).ae_eq hae
  have hsq' : IntegrableOn (fun t => ‖w' t‖ ^ 2) (Ioc δ 1) :=
    (memLp_two_iff_integrable_sq_norm hmeas'.aestronglyMeasurable).mp hmem'
  set w : ℝ → ℂ := (Ioc δ 1).indicator w' with hwdef
  have hsub : Ioc δ 1 ⊆ Ioc (0 : ℝ) 1 := Ioc_subset_Ioc_left hδ.le
  refine ⟨w, ⟨hmeas'.indicator measurableSet_Ioc, ?_, fun a ha => ?_⟩, fun t ht => ?_, ?_⟩
  · -- square integrability on `(0,1]`
    have hind : (fun t => ‖w t‖ ^ 2) = (Ioc δ 1).indicator (fun t => ‖w' t‖ ^ 2) := by
      funext t
      simp only [hwdef, indicator]
      split_ifs <;> simp
    rw [hind]
    exact ((integrable_indicator_iff measurableSet_Ioc).2 hsq').integrableOn
  · -- orthogonality to every generator
    have horth : inner ℂ (fermiGenLpOn δ a) u = 0 :=
      (Submodule.mem_orthogonal _ _).mp hu _ (Submodule.subset_span ⟨a, ha, rfl⟩)
    rw [L2.inner_def] at horth
    have hgen : (fermiGenLpOn δ a : ℝ → ℂ) =ᵐ[volume.restrict (Ioc δ 1)] fermiNymanGen a :=
      MemLp.coeFn_toLp _
    have hval : (∫ t, inner ℂ ((fermiGenLpOn δ a : ℝ → ℂ) t) ((u : ℝ → ℂ) t)
        ∂(volume.restrict (Ioc δ 1))) =
        ∫ t in Ioc δ 1, fermiNymanGen a t * w' t := by
      refine integral_congr_ae ?_
      filter_upwards [hgen, hae] with t h1 h2
      rw [RCLike.inner_apply, h1, h2, conj_fermiNymanGen, mul_comm]
    rw [hval] at horth
    have hpt : (fun t => fermiNymanGen a t * (starRingEnd ℂ) (w t)) =
        (Ioc δ 1).indicator (fun t => fermiNymanGen a t * (starRingEnd ℂ) (w' t)) := by
      funext t
      simp only [hwdef, indicator]
      split_ifs <;> simp
    rw [hpt, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]
    have hconj : (∫ t in Ioc δ 1, fermiNymanGen a t * (starRingEnd ℂ) (w' t)) =
        (starRingEnd ℂ) (∫ t in Ioc δ 1, fermiNymanGen a t * w' t) := by
      rw [← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [map_mul, conj_fermiNymanGen]
    rw [hconj, horth, map_zero]
  · -- vanishing on `(0, δ]`
    simp only [hwdef]
    exact indicator_of_notMem (fun h => lt_irrefl _ (lt_of_lt_of_le h.1 ht.2)) _
  · -- agreement with `u` on `(δ, 1]`
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    rw [h1, hwdef, indicator_of_mem h2]

/-- **Local completeness.**  For every `δ ∈ (0, 1)`, the restrictions of the alternating generators
to `(δ, 1]` span a dense subspace of `L²(δ, 1]` — unconditionally. -/
theorem fermiGenSpanOn_topologicalClosure_eq_top {δ : ℝ} (hδ : 0 < δ) :
    (fermiGenSpanOn δ).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  obtain ⟨w, hw, hvan, hae⟩ := exists_isL2FermiWitness_of_mem_orthogonal_on hδ hu
  have h0 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) δ)), w t = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hvan
  have hz := hw.ae_eq_zero_of_ae_eq_zero_near_zero hδ h0
  have hz' : ∀ᵐ t ∂(volume.restrict (Ioc δ 1)), w t = 0 :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_left hδ.le) hz
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae, hz'] with t h1 h2
  rw [h1, h2]; rfl

/-- A finite combination of restricted generators in `L²(δ,1]` is (a.e.) the pointwise combination. -/
theorem coeFn_sum_smul_fermiGenLpOn {δ : ℝ} {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ)
    (s : Finset (Fin n)) :
    ((∑ i ∈ s, c i • fermiGenLpOn δ (a i) : Lp ℂ 2 (volume.restrict (Ioc δ 1))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc δ 1)] fun t => ∑ i ∈ s, c i * fermiNymanGen (a i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (c j • fermiGenLpOn δ (a j)) (∑ i ∈ s, c i • fermiGenLpOn δ (a i)),
      Lp.coeFn_smul (c j) (fermiGenLpOn δ (a j)),
      MemLp.coeFn_toLp (memLp_fermiNymanGen_Ioc_restrict (δ := δ) (a j)), ih] with t h1 h2 h3 h4
    have h3' : (fermiGenLpOn δ (a j) : ℝ → ℂ) t = fermiNymanGen (a j) t := h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h4, Finset.sum_insert hj, smul_eq_mul, h3']

/-- **Every square-integrable function is approximable on `(δ, 1]` by finite generator
combinations**, for every `δ ∈ (0,1)`: no obstruction to the alternating approximation problem lives
in the bulk. -/
theorem exists_fermiNymanCombination_approx_on {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc δ 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
      (∫ t in Ioc δ 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  set F : Lp ℂ 2 (volume.restrict (Ioc δ 1)) := MemLp.toLp f hf with hFdef
  have hdense : F ∈ closure (fermiGenSpanOn δ : Set (Lp ℂ 2 (volume.restrict (Ioc δ 1)))) := by
    rw [← Submodule.topologicalClosure_coe, fermiGenSpanOn_topologicalClosure_eq_top hδ]
    exact Submodule.mem_top
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hdense (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hb
  choose a ha hga using fun i => (g i).2
  refine ⟨n, c, a, fun i => (ha i), ?_⟩
  have hb' : b = ∑ i ∈ Finset.univ, c i • fermiGenLpOn δ (a i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hga i]
  have hcomb : MemLp (fermiNymanCombination c a) 2 (volume.restrict (Ioc δ 1)) := by
    unfold fermiNymanCombination
    exact memLp_finsetSum Finset.univ (f := fun i => fun t => c i * fermiNymanGen (a i) t)
      (fun i _ => (memLp_fermiNymanGen_Ioc_restrict (a i)).const_mul (c i))
  have hdiff : MemLp (fun t => f t - fermiNymanCombination c a t) 2
      (volume.restrict (Ioc δ 1)) := hf.sub hcomb
  have hnorm : dist F b = (eLpNorm (fun t => f t - fermiNymanCombination c a t) 2
      (volume.restrict (Ioc δ 1))).toReal := by
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub F b, MemLp.coeFn_toLp hf,
      coeFn_sum_smul_fermiGenLpOn (δ := δ) c a Finset.univ] with t h1 h2 h3
    have h2' : (F : ℝ → ℂ) t = f t := h2
    rw [h1, Pi.sub_apply, h2', hb', h3]
    rfl
  rw [hnorm, hdiff.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)] at hdist
  have hint : 0 ≤ ∫ t in Ioc δ 1, ‖f t - fermiNymanCombination c a t‖ ^ 2 :=
    integral_nonneg fun t => by positivity
  have h2 : ((∫ t in Ioc δ 1, ‖f t - fermiNymanCombination c a t‖ ^
      (2 : ℝ≥0∞).toReal) ^ (2 : ℝ≥0∞).toReal⁻¹) =
      Real.sqrt (∫ t in Ioc δ 1, ‖f t - fermiNymanCombination c a t‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [h2, Real.sqrt_lt_sqrt_iff hint] at hdist
  exact hdist

/-- The Haar target in particular: for every `δ ∈ (0,1)` and `ε > 0` some finite generator
combination is `ε`-close to `h` in `L²(δ, 1]`.  (The raw Möbius combination is even exact there;
this instance records that no approximant needs arithmetic input away from the origin.) -/
theorem exists_fermiNymanCombination_dyadicHaar_approx_on {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ), (∀ j, 1 ≤ a j) ∧
      (∫ t in Ioc δ 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  haveI : Fact (volume (Ioc δ 1) < ⊤) := ⟨measure_Ioc_lt_top⟩
  exact exists_fermiNymanCombination_approx_on hδ
    (MemLp.of_bound measurable_dyadicHaar.aestronglyMeasurable 1
      (Eventually.of_forall fun t => (norm_dyadicHaar t).le)) hε

/-! ## The unimodular dyadic factor -/

/-- The dyadic factor `I(s) = (1 − 2^{1−s})/(√2 (1 − 2^{−s}))`: the inner part of the Haar target's
Mellin transform on `Re s > 1/2` (zeros at `1 + 2πik/log 2`, `k ∈ ℤ`). -/
def dyadicInnerFactor (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) / ((Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)))

theorem normSq_one_sub_eq (z : ℂ) : Complex.normSq (1 - z) = 1 + Complex.normSq z - 2 * z.re := by
  rw [Complex.normSq_sub, Complex.normSq_one, one_mul]
  simp [Complex.conj_re]

theorem normSq_two_cpow (z : ℂ) : Complex.normSq ((2 : ℂ) ^ z) = (2 : ℝ) ^ (2 * z.re) := by
  rw [Complex.normSq_eq_norm_sq, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul
    (by norm_num)]
  push_cast
  ring_nf

/-- **The dyadic factor has modulus one on the critical line.**  Both
`‖1 − 2^{1−s}‖²` and `2 ‖1 − 2^{−s}‖²` equal `3 − 2 Re 2^{1−s}` when `Re s = 1/2`. -/
theorem norm_dyadicInnerFactor_eq_one {s : ℂ} (hs : s.re = 1 / 2) :
    ‖dyadicInnerFactor s‖ = 1 := by
  have hnum : Complex.normSq (1 - (2 : ℂ) ^ (1 - s)) = 3 - 2 * ((2 : ℂ) ^ (1 - s)).re := by
    rw [normSq_one_sub_eq, normSq_two_cpow]
    have : (2 : ℝ) ^ (2 * (1 - s).re) = 2 := by
      rw [Complex.sub_re, Complex.one_re, hs]
      norm_num
    rw [this]; ring
  have hre : ((2 : ℂ) ^ (1 - s)).re = 2 * ((2 : ℂ) ^ (-s)).re := by
    rw [← two_mul_two_cpow_neg]
    simp [Complex.mul_re]
  have hden : Complex.normSq ((Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s))) =
      3 - 2 * ((2 : ℂ) ^ (1 - s)).re := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num),
      normSq_one_sub_eq, normSq_two_cpow, hre]
    have : (2 : ℝ) ^ (2 * (-s).re) = 1 / 2 := by
      rw [Complex.neg_re, hs]
      norm_num
    rw [this]; ring
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have h2s : (1 : ℂ) - (2 : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.1 h)
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re, hs] at hn
    have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  have hden0 : (Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)) ≠ 0 := mul_ne_zero hsqrt h2s
  have h1 : ‖1 - (2 : ℂ) ^ (1 - s)‖ = ‖(Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s))‖ := by
    have hsq : ‖1 - (2 : ℂ) ^ (1 - s)‖ ^ 2 = ‖(Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s))‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, hnum, hden]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  unfold dyadicInnerFactor
  rw [norm_div, h1, div_self (norm_ne_zero_iff.2 hden0)]

/-- **Exact factorisation of the Haar target's Mellin transform**:
`∫_0^1 h(t) t^{s−1} dt = I(s) · √2 (1 − 2^{−s})/s` for `Re s > 0`. -/
theorem integral_dyadicHaar_mul_cpow_factor {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (t : ℂ) ^ (s - 1)) =
      dyadicInnerFactor s * ((Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)) / s) := by
  rw [integral_dyadicHaar_mul_cpow hs]
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have h2s : (1 : ℂ) - (2 : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.1 h)
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re] at hn
    have : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  unfold dyadicInnerFactor
  field_simp

/-- **The generators carry the same unimodular dyadic factor**:
`M[φ_a](s) = −a^{−s} · I(s) · √2 (1 − 2^{−s}) ζ(s)/s` on the strip `0 < Re s < 1`. -/
theorem mellin_fermiNymanGen_factor {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ}
    (ha : 0 < a) :
    mellin (fermiNymanGen a) s =
      -(((a : ℝ) : ℂ) ^ (-s) * dyadicInnerFactor s *
        ((Real.sqrt 2 : ℂ) * (1 - (2 : ℂ) ^ (-s)) * riemannZeta s / s)) := by
  rw [mellin_fermiNymanGen hs0 hs1 ha]
  have hs0' : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have h2s : (1 : ℂ) - (2 : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.1 h)
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re] at hn
    have : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  unfold dyadicInnerFactor
  field_simp

end RHTower
