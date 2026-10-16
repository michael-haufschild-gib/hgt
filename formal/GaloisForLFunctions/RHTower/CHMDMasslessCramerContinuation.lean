import GaloisForLFunctions.RHTower.CHMDMasslessContinuationPieces

/-!
# CHMD: continuation of the massless zero-side wave across `Im v = 1`

The massless zero-side wave `Φ₀(v) = Σ_ρ m_ρ cos(v γ_ρ) sech²(γ_ρ/2)` is holomorphic on the time
strip `|Im v| < 1` and not beyond: its terms grow like `e^{(|Im v| − 1)|γ_ρ|}`.  This module continues
it across the line `Im v = 1` on each half-plane `Re v > a`, `0 < a ≤ 1/2`.

**Continuation formula** (`masslessContinuation a`).  On `Re v > a`, `−1/2 < Im v < 3/2`,

`F₀(v) = (2/cos²(1/4)) cosh(v/2) + γ(0) D(v) + ∫_0^a ω(x)(2D(v) − D(v+x) − D(v−x)) dx
        + ∫_a^∞ ω(x)(2D(v) − D(v+x)) dx − [ i ∫_0^{1/2} ω(a+iy) D(v−a−iy) dy
        + ∫_a^∞ ω(x + i/2) D(v − x − i/2) dx ] − Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v))`,

the translate form of the massless explicit formula with the archimedean path deformed into the
upper half-plane.  For real `v` it equals the massless Weil side (`masslessContinuation_ofReal`), so
by the identity theorem `Φ₀ = F₀` on `Re v > a`, `−1/2 < Im v < 1`
(`masslessZeroWave_eq_masslessContinuation`); the archimedean parts for different cutoffs agree
(`archContinuation_congr`).

**Prime points.**  `F₀` is holomorphic at every point of its domain except the points `log n + i`
with `Λ(n) ≠ 0` (`differentiableAt_masslessContinuation`), and there it has a simple pole with residue
`(2i/π) Λ(n)/√n` (`tendsto_masslessContinuation_residue`):

`(v − (log n + i)) F₀(v) → (2i/π) Λ(n)/√n`.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

/-- The archimedean part of the continuation, with cutoff `a`. -/
def archContinuation (a : ℝ) (v : ℂ) : ℂ :=
  EF.gammaBracket 0 * dAlembertKernel v + archNearC a v + archFarC a v -
    (I * contourVerticalC a v + contourHorizontalC a v)

/-- The continued massless wave, with cutoff `a`. -/
def masslessContinuation (a : ℝ) (v : ℂ) : ℂ :=
  2 / Real.cos (1 / 4 : ℝ) ^ 2 * Complex.cosh (v / 2) + archContinuation a v - primeWaveC v

/-! ## The real axis -/

theorem dAlembertReal_le_eight (v : ℝ) : dAlembertReal v ≤ 8 := by
  refine (dAlembertReal_le v).trans ?_
  have := one_add_mul_exp_neg_pi_le |v| (abs_nonneg v)
  nlinarith

theorem integrableOn_levy_mul_dAlembert {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 24) : IntegrableOn (fun x => archLevyDensity x * g x) (Ioi a) := by
  refine ((integrableOn_archLevyDensity_Ioi ha).mul_const 24).mono'
    (measurable_archLevyDensity.mul hg).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : a < x := hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos (by linarith))]
  exact mul_le_mul_of_nonneg_left (hb x) (archLevyDensity_pos (by linarith)).le

/-- **On the real axis the continuation is the massless Weil side.** -/
theorem masslessContinuation_ofReal {a : ℝ} (ha : 0 < a) (v : ℝ) :
    masslessContinuation a v = (masslessWeilSide v : ℂ) := by
  set g : ℝ → ℝ := fun x => archLevyDensity x *
    (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x)) with hg
  have hgi := integrableOn_levyTranslate v
  have hD8 : ∀ x, |dAlembertReal x| ≤ 8 := fun x => by
    rw [abs_of_pos (dAlembertReal_pos x)]; exact dAlembertReal_le_eight x
  have hcD : Continuous dAlembertReal := continuous_dAlembertReal
  have h1 : IntegrableOn (fun x => archLevyDensity x * (2 * dAlembertReal v - dAlembertReal (v + x)))
      (Ioi a) :=
    integrableOn_levy_mul_dAlembert ha (continuous_const.sub (hcD.comp (continuous_const.add
      continuous_id))).measurable fun x => by
      have := hD8 v; have := hD8 (v + x)
      rw [abs_le] at *; constructor <;> linarith
  have h2 : IntegrableOn (fun x => archLevyDensity x * dAlembertReal (v - x)) (Ioi a) :=
    integrableOn_levy_mul_dAlembert ha (hcD.comp (continuous_const.sub continuous_id)).measurable
      fun x => (hD8 _).trans (by norm_num)
  have hsplit : ∫ x in Ioi (0 : ℝ), g x = (∫ x in Ioc (0 : ℝ) a, g x) +
      ((∫ x in Ioi a, archLevyDensity x * (2 * dAlembertReal v - dAlembertReal (v + x))) -
        ∫ x in Ioi a, archLevyDensity x * dAlembertReal (v - x)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hgi.mono_set Set.Ioc_subset_Ioi_self) (hgi.mono_set (Set.Ioi_subset_Ioi ha.le)),
      ← integral_sub h1 h2]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    show archLevyDensity x * (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x)) = _
    ring
  have hnear : archNearC a v = ((∫ x in Ioc (0 : ℝ) a, g x : ℝ) : ℂ) := by
    unfold archNearC
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    show _ = ((archLevyDensity x *
      (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x)) : ℝ) : ℂ)
    rw [show (v : ℂ) + x = ((v + x : ℝ) : ℂ) by push_cast; ring,
      show (v : ℂ) - x = ((v - x : ℝ) : ℂ) by push_cast; ring,
      dAlembertKernel_ofReal, dAlembertKernel_ofReal, dAlembertKernel_ofReal]
    push_cast
    ring
  have hfar : archFarC a v = ((∫ x in Ioi a, archLevyDensity x *
      (2 * dAlembertReal v - dAlembertReal (v + x)) : ℝ) : ℂ) := by
    unfold archFarC
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show (v : ℂ) + x = ((v + x : ℝ) : ℂ) by push_cast; ring,
      dAlembertKernel_ofReal, dAlembertKernel_ofReal]
    push_cast
    ring
  have hcont : I * contourVerticalC a v + contourHorizontalC a v =
      ((∫ x in Ioi a, archLevyDensity x * dAlembertReal (v - x) : ℝ) : ℂ) := by
    rw [← integral_levy_mul_dAlembert_eq_contour ha, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show (v : ℂ) - x = ((v - x : ℝ) : ℂ) by push_cast; ring, dAlembertKernel_ofReal]
    push_cast
    ring
  have hcosh : Complex.cosh ((v : ℂ) / 2) = (Real.cosh (v / 2) : ℂ) := by
    rw [Complex.ofReal_cosh]; push_cast; ring_nf
  rw [masslessWeilSide_eq_levy, hsplit, masslessContinuation, archContinuation, hnear, hfar, hcont,
    primeWaveC_ofReal, hcosh, dAlembertKernel_ofReal]
  push_cast
  ring

/-! ## Holomorphy of the continuation -/

theorem primeWaveC_eq_tail_zero : primeWaveC = fun v => ∑' n : ℕ, if n = 0 then 0 else primeTermC n v := by
  funext v
  unfold primeWaveC
  refine tsum_congr fun n => ?_
  split_ifs with h
  · subst h
    rw [primeTermC_eq_zero_of_weight (chmdPrimeWeight_eq_zero_of_lt_two (by norm_num))]
  · rfl

theorem differentiableAt_archContinuation {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {v : ℂ}
    (hre : a < v.re) (h1 : -1 / 2 < v.im) (h2 : v.im < 3 / 2) :
    DifferentiableAt ℂ (archContinuation a) v := by
  have him : |v.im| < 3 / 2 := abs_lt.mpr ⟨by linarith, h2⟩
  unfold archContinuation
  exact ((((differentiableAt_dAlembertKernel_of_re_pos (by linarith)).const_mul _).add
    (differentiableAt_archNearC ha ha' hre)).add
      (differentiableAt_archFarC ha (by linarith) him)).sub
    (((differentiableAt_contourVerticalC ha hre him).const_mul I).add
      (differentiableAt_contourHorizontalC ha h1 h2))

/-- **Regularity off the prime points.** -/
theorem differentiableAt_masslessContinuation {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {v : ℂ}
    (hre : a < v.re) (h1 : -1 / 2 < v.im) (h2 : v.im < 3 / 2)
    (hpole : ∀ n, chmdPrimeWeight n ≠ 0 → v ≠ (Real.log n : ℂ) + I) :
    DifferentiableAt ℂ (masslessContinuation a) v := by
  have hprime : DifferentiableAt ℂ primeWaveC v := by
    rw [primeWaveC_eq_tail_zero]
    exact differentiableAt_primeTailC 0 (by linarith) h1 h2 fun n _ hw => hpole n hw
  unfold masslessContinuation
  exact (((by fun_prop : Differentiable ℂ fun v : ℂ =>
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Complex.cosh (v / 2)) v).add
    (differentiableAt_archContinuation ha ha' hre h1 h2)).sub hprime

/-! ## The identity theorem -/

theorem frequently_ofReal_nhdsNE_one (P : ℂ → Prop) (hP : ∀ t : ℝ, 1 < t → P t) :
    ∃ᶠ z in 𝓝[≠] ((1 : ℝ) : ℂ), P z := by
  have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  rw [add_zero] at h0
  have hu : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((1 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(continuous_ofReal.tendsto (1 : ℝ)).comp h0, Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := Complex.ofReal_injective h
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact hu.frequently (Eventually.of_forall fun n => hP _ (by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)).frequently

/-- **The archimedean part does not depend on the cutoff.** -/
theorem archContinuation_congr {a b : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) (hb : 0 < b)
    (hb' : b ≤ 1 / 2) {v : ℂ} (hva : a < v.re) (hvb : b < v.re) (h1 : -1 / 2 < v.im)
    (h2 : v.im < 3 / 2) : archContinuation a v = archContinuation b v := by
  set U : Set ℂ := {v | max a b < v.re} ∩ ({v | -1 / 2 < v.im} ∩ {v | v.im < 3 / 2})
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))).isPreconnected
  have hA : ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → c ≤ max a b → AnalyticOnNhd ℂ (archContinuation c) U :=
    fun c hc hc' hcm => DifferentiableOn.analyticOnNhd (fun w hw => by
      have hw' : max a b < w.re ∧ -1 / 2 < w.im ∧ w.im < 3 / 2 := hw
      exact (differentiableAt_archContinuation hc hc' (lt_of_le_of_lt hcm hw'.1) hw'.2.1
        hw'.2.2).differentiableWithinAt) hUo
  have hreal : ∀ c : ℝ, 0 < c → ∀ t : ℝ, archContinuation c t =
      masslessWeilSide t - 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (t / 2) +
        masslessPrimeWave t := by
    intro c hc t
    have h := masslessContinuation_ofReal hc t
    rw [masslessContinuation, primeWaveC_ofReal] at h
    have hcosh : Complex.cosh ((t : ℂ) / 2) = (Real.cosh (t / 2) : ℂ) := by
      rw [Complex.ofReal_cosh]; push_cast; ring_nf
    rw [hcosh] at h
    linear_combination h
  have h1U : ((1 : ℝ) : ℂ) ∈ U := ⟨by
      rw [Set.mem_setOf_eq, Complex.ofReal_re]; exact max_lt (by linarith) (by linarith),
    by simp; norm_num, by simp⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 : ℝ) : ℂ), archContinuation a z = archContinuation b z :=
    frequently_ofReal_nhdsNE_one _ fun t _ => by rw [hreal a ha, hreal b hb]
  exact (hA a ha ha' (le_max_left _ _)).eqOn_of_preconnected_of_frequently_eq
    (hA b hb hb' (le_max_right _ _)) hUc h1U hfreq ⟨max_lt hva hvb, h1, h2⟩

/-- **The continuation agrees with the zero-side wave** on `Re v > a`, `−1/2 < Im v < 1`. -/
theorem masslessZeroWave_eq_masslessContinuation {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {v : ℂ}
    (hre : a < v.re) (h1 : -1 / 2 < v.im) (h2 : v.im < 1) :
    masslessZeroWave v = masslessContinuation a v := by
  set U : Set ℂ := {v | a < v.re} ∩ ({v | -1 / 2 < v.im} ∩ {v | v.im < 1}) with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))).isPreconnected
  have hF : AnalyticOnNhd ℂ masslessZeroWave U := by
    refine (differentiableOn_masslessZeroWave.mono fun w hw => ?_).analyticOnNhd hUo
    have hw' : a < w.re ∧ -1 / 2 < w.im ∧ w.im < 1 := hw
    show |w.im| < 1
    exact abs_lt.mpr ⟨by linarith [hw'.2.1], hw'.2.2⟩
  have hG : AnalyticOnNhd ℂ (masslessContinuation a) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw' : a < w.re ∧ -1 / 2 < w.im ∧ w.im < 1 := hw
    refine (differentiableAt_masslessContinuation ha ha' hw'.1 hw'.2.1 (by linarith [hw'.2.2])
      fun n _ h => ?_).differentiableWithinAt
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add] at this
    linarith [hw'.2.2]
  have h1U : ((1 : ℝ) : ℂ) ∈ U := ⟨by simp; linarith, by simp; norm_num, by simp⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] ((1 : ℝ) : ℂ), masslessZeroWave z = masslessContinuation a z :=
    frequently_ofReal_nhdsNE_one _ fun t _ => by
      rw [masslessZeroWave_ofReal, masslessContinuation_ofReal ha]
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hUc h1U hfreq ⟨hre, h1, h2⟩

/-! ## The residues at the prime points -/

theorem two_le_of_chmdPrimeWeight_ne_zero {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) : 2 ≤ n := by
  by_contra h
  exact hw (chmdPrimeWeight_eq_zero_of_lt_two (not_le.mp h))

theorem half_lt_log_of_two_le {n : ℕ} (hn : 2 ≤ n) : 1 / 2 < Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  linarith [Real.log_two_gt_d9]

/-- The prime wave with the term `n₀` removed. -/
def primeTailC (n₀ : ℕ) (v : ℂ) : ℂ := ∑' n : ℕ, if n = n₀ then 0 else primeTermC n v

/-- The part of the continuation that is regular at `log n₀ + i`. -/
def masslessRegularPart (a : ℝ) (n₀ : ℕ) (v : ℂ) : ℂ :=
  2 / Real.cos (1 / 4 : ℝ) ^ 2 * Complex.cosh (v / 2) + archContinuation a v - primeTailC n₀ v -
    chmdPrimeWeight n₀ * dAlembertKernel ((Real.log n₀ : ℂ) + v)

/-- **Polar splitting**: `F₀ = (regular part) − (Λ(n₀)/√n₀) D(v − log n₀)`. -/
theorem masslessContinuation_eq_regular_sub_polar (a : ℝ) (n₀ : ℕ) {v : ℂ} (hv : 0 ≤ v.re) :
    masslessContinuation a v = masslessRegularPart a n₀ v -
      chmdPrimeWeight n₀ * dAlembertKernel (v - Real.log n₀) := by
  have hsum := (summable_primeTermC hv).tsum_eq_add_tsum_ite n₀
  unfold masslessContinuation masslessRegularPart primeWaveC primeTailC
  rw [hsum]
  simp only [primeTermC]
  rw [show (v - (Real.log n₀ : ℂ)) = -((Real.log n₀ : ℂ) - v) by ring, dAlembertKernel_neg]
  ring

theorem differentiableAt_masslessRegularPart {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {n₀ : ℕ}
    (hw : chmdPrimeWeight n₀ ≠ 0) :
    DifferentiableAt ℂ (masslessRegularPart a n₀) ((Real.log n₀ : ℂ) + I) := by
  set v₀ : ℂ := (Real.log n₀ : ℂ) + I with hv₀
  have hn₀ := two_le_of_chmdPrimeWeight_ne_zero hw
  have hlog := half_lt_log_of_two_le hn₀
  have hv₀re : v₀.re = Real.log n₀ := by
    rw [hv₀, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  have hv₀im : v₀.im = 1 := by
    rw [hv₀, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  have htd : DifferentiableAt ℂ (primeTailC n₀) v₀ := by
    refine differentiableAt_primeTailC n₀ (by linarith) (by rw [hv₀im]; norm_num)
      (by rw [hv₀im]; norm_num) fun n hn hwn h => hn ?_
    have h' := congrArg Complex.re h
    simp only [hv₀, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at h'
    have hn2 := two_le_of_chmdPrimeWeight_ne_zero hwn
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < n₀)))
      (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < n))) h'
    exact_mod_cast this.symm
  have hD2 : DifferentiableAt ℂ (fun v => dAlembertKernel ((Real.log n₀ : ℂ) + v)) v₀ :=
    (differentiableAt_dAlembertKernel_of_re_pos (by
      rw [Complex.add_re, Complex.ofReal_re, hv₀re]; linarith)).comp v₀
      (differentiableAt_id.const_add _)
  unfold masslessRegularPart
  exact ((((by fun_prop : Differentiable ℂ fun v : ℂ =>
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Complex.cosh (v / 2)) v₀).add
    (differentiableAt_archContinuation ha ha' (by rw [hv₀re]; linarith) (by rw [hv₀im]; norm_num)
      (by rw [hv₀im]; norm_num))).sub htd).sub (hD2.const_mul _)

/-- **The residue law**: at `log n + i` (`Λ(n) ≠ 0`) the continuation has a simple pole with
residue `(2i/π) Λ(n)/√n`. -/
theorem tendsto_masslessContinuation_residue {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {n₀ : ℕ}
    (hw : chmdPrimeWeight n₀ ≠ 0) :
    Tendsto (fun v => (v - ((Real.log n₀ : ℂ) + I)) * masslessContinuation a v)
      (𝓝[≠] ((Real.log n₀ : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n₀)) := by
  set v₀ : ℂ := (Real.log n₀ : ℂ) + I with hv₀
  have hn₀ := two_le_of_chmdPrimeWeight_ne_zero hw
  have hlog := half_lt_log_of_two_le hn₀
  have hv₀re : v₀.re = Real.log n₀ := by
    rw [hv₀, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  set w₀ : ℂ := (chmdPrimeWeight n₀ : ℂ)
  set H := masslessRegularPart a n₀
  have hHd : DifferentiableAt ℂ H v₀ := differentiableAt_masslessRegularPart ha ha' hw
  have hsplit : ∀ᶠ v in 𝓝[≠] v₀, masslessContinuation a v =
      H v - w₀ * dAlembertKernel (v - Real.log n₀) := by
    have hnhds : ∀ᶠ v in 𝓝 v₀, 0 ≤ v.re :=
      (continuous_re.tendsto v₀).eventually (lt_mem_nhds (by rw [hv₀re]; linarith))
        |>.mono fun v hv => hv.le
    filter_upwards [nhdsWithin_le_nhds hnhds] with v hv
    exact masslessContinuation_eq_regular_sub_polar a n₀ hv
  have hφ : Tendsto (fun v : ℂ => v - Real.log n₀) (𝓝[≠] v₀) (𝓝[≠] I) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_id.sub continuous_const).tendsto v₀ (f := fun v : ℂ => v - Real.log n₀))
      rw [show v₀ - (Real.log n₀ : ℂ) = I by rw [hv₀]; ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv ⊢
      intro h
      exact hv (by rw [hv₀]; linear_combination h)
  have hpolar := tendsto_sub_I_mul_dAlembertKernel.comp hφ
  have hzero : Tendsto (fun v => (v - v₀) * H v) (𝓝[≠] v₀) (𝓝 0) := by
    have h1 : Tendsto (fun v : ℂ => v - v₀) (𝓝[≠] v₀) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).tendsto v₀ (f := fun v : ℂ => v - v₀))
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := hHd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {v₀}ᶜ))
    simpa using h1.mul h2
  have hlim := hzero.sub (hpolar.const_mul w₀)
  rw [show (2 * I / π * chmdPrimeWeight n₀ : ℂ) = 0 - w₀ * (-2 * I / π) by
    simp only [w₀]; ring]
  refine hlim.congr' ?_
  filter_upwards [hsplit] with v hv
  rw [hv]
  simp only [Function.comp]
  rw [show v - Real.log n₀ - I = v - v₀ by rw [hv₀]; ring]
  ring

end RHTower.CHMDLightCone
