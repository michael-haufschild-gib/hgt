import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryRootMean

/-!
# The recovery equilibrium measure

With `H(a) = (I(a) - π/2)/π` (so `H(0) = 0`, `H(b) = 1`, `H' = h > 0`) and `ν_a` the arcsine law on
`[-a, a]`, the mixture

  `μ = ∫_0^b ν_a H'(a) da`

is a probability measure whose logarithmic potential satisfies the equilibrium conditions for the
field `Q(t) = -½ log(1 - |t|)`:

* `∫ log|x - y| dμ(y) = log C - ½ log(1 - |x|)` for `|x| ≤ b`, strictly less for `b < |x| < 1`;
* `U^μ + Q` is constant on `[-b, b]` and strictly increasing in `|x|` on `[b, 1)`, with derivative
  `1/(2(1-t)) - ∫_0^b H'(a)/√(t² - a²) da > 0` there.

The Abel identity `∫_0^x H'(a)/√(x² - a²) da = 1/(2(1-x))` holds for `0 < x < 1`, and
`∫ t² dμ = 1 - b/π - 3b²/4`, so `A = (1 - ∫ t² dμ)/4 = b/(4π) + 3b²/16`.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped Real Topology ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### The mass function -/

/-- **`I(a) = (π/2 + arcsin a)/√(1 - a²)`** for `-1 < a < 1`. -/
theorem recoveryI_eq_arcsin {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1) :
    recoveryI a = (π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2) := by
  have h := recoveryI_cos (θ := Real.arccos a) (Real.arccos_pos.mpr ha.2)
    (Real.arccos_lt_pi.mpr ha.1)
  rw [Real.cos_arccos ha.1.le ha.2.le, Real.sin_arccos, Real.arccos_eq_pi_div_two_sub_arcsin] at h
  rw [h]; ring_nf

theorem hasDerivAt_recoveryMass {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt recoveryMass (recoveryDensity x) x := by
  set c := (1 + |x|) / 2 with hc
  have hxc : |x| < c := by rw [hc]; linarith [abs_lt.mpr ⟨hx.1, hx.2⟩]
  have hc1 : c < 1 := by rw [hc]; linarith [abs_lt.mpr ⟨hx.1, hx.2⟩]
  have hcont := continuousOn_recoveryDensity (by positivity : 0 ≤ c) hc1
  have hIoo : Ioo (-c) c ∈ 𝓝 x := Ioo_mem_nhds (by linarith [neg_abs_le x]) (by
    linarith [le_abs_self x])
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · refine ContinuousOn.intervalIntegrable (hcont.mono (uIcc_subset_Icc ?_ ?_))
    · constructor <;> linarith [abs_nonneg x]
    · constructor <;> linarith [neg_abs_le x, le_abs_self x]
  · exact (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x
      (by constructor <;> linarith [neg_abs_le x, le_abs_self x])
  · exact (hcont.mono Ioo_subset_Icc_self).continuousAt hIoo

theorem recoveryMass_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    recoveryMass a = ((π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2) - π / 2) / π := by
  rw [recoveryMass, integral_recoveryDensity ha0 ha1, recoveryI_eq_arcsin ⟨by linarith, ha1⟩]

/-! ### The Abel identity in derivative form -/

/-- **`∫_0^x H'(a)/√(x² - a²) da = 1/(2(1-x))`** for `0 < x < 1`, via `a = x sin u`:
`∫_0^{π/2} h(x sin u) du = Σ c_n x^n J_n = Σ x^n/2`. -/
theorem recoveryDensity_div_sqrt_abel {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    IntervalIntegrable (fun a => recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2)) volume 0 x ∧
    ∫ a in (0 : ℝ)..x, recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2) = 1 / (2 * (1 - x)) := by
  -- the angular form
  have hang : ∫ u in (0 : ℝ)..π / 2, recoveryDensity (x * Real.sin u) = 1 / (2 * (1 - x)) := by
    have hval : ∀ n : ℕ, ∫ u in (0 : ℝ)..π / 2, recoveryDensityCoeff n * (x * Real.sin u) ^ n =
        x ^ n / 2 := fun n => by
      simp_rw [mul_pow]
      rw [show (fun u => recoveryDensityCoeff n * (x ^ n * Real.sin u ^ n)) =
          fun u => (recoveryDensityCoeff n * x ^ n) * Real.sin u ^ n by funext u; ring,
        intervalIntegral.integral_const_mul, ← wallisJ_eq_sin, recoveryDensityCoeff]
      have hw := wallisJ_mul n
      have hπ := Real.pi_pos.ne'
      field_simp
      linear_combination 2 * hw
    have hnorm : ∀ n : ℕ, ∫ u in (0 : ℝ)..π / 2, ‖recoveryDensityCoeff n * (x * Real.sin u) ^ n‖ =
        x ^ n / 2 := fun n => by
      rw [← hval]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le (by positivity)] at hu
      have hs : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu.1
        (by linarith [hu.2, Real.pi_pos])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (recoveryDensityCoeff_nonneg n)
        (pow_nonneg (mul_nonneg hx0.le hs) n))]
    have hgeom : HasSum (fun n : ℕ => x ^ n / 2) (1 / (2 * (1 - x))) := by
      have := (hasSum_geometric_of_lt_one hx0.le hx1).div_const 2
      rwa [show (1 - x)⁻¹ / 2 = 1 / (2 * (1 - x)) by rw [one_div, mul_inv]; ring] at this
    have h := hasSum_intervalIntegral_of_summable_norm
      (f := fun n u => recoveryDensityCoeff n * (x * Real.sin u) ^ n) (a := 0) (b := π / 2)
      (by positivity)
      (fun n => (by fun_prop : Continuous fun u => recoveryDensityCoeff n * (x * Real.sin u) ^ n)
        |>.intervalIntegrable _ _) (by simpa only [hnorm] using hgeom.summable)
    simp only [hval] at h
    have e : ∫ u in (0 : ℝ)..π / 2, ∑' n, recoveryDensityCoeff n * (x * Real.sin u) ^ n =
        ∫ u in (0 : ℝ)..π / 2, recoveryDensity (x * Real.sin u) := rfl
    rw [e] at h
    exact h.unique hgeom
  -- the primitive `P(a) = ∫_0^{arcsin(a/x)} h(x sin u) du`
  have hhc : Continuous fun u => recoveryDensity (x * Real.sin u) :=
    (continuousOn_recoveryDensity hx0.le hx1).comp_continuous (by fun_prop) fun v => by
      constructor <;> nlinarith [Real.neg_one_le_sin v, Real.sin_le_one v]
  set P : ℝ → ℝ := fun a => ∫ u in (0 : ℝ)..Real.arcsin (a / x), recoveryDensity (x * Real.sin u)
    with hP
  have hPd : ∀ a ∈ Ioo (0 : ℝ) x, HasDerivAt P (recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2)) a := by
    intro a ha
    have hax : a / x < 1 := by rw [div_lt_one hx0]; exact ha.2
    have hax' : -1 < a / x := by
      have : 0 < a / x := div_pos ha.1 hx0
      linarith
    have harc : HasDerivAt (fun a => Real.arcsin (a / x)) (1 / Real.sqrt (1 - (a / x) ^ 2) * (1 / x))
        a := by
      have := (Real.hasDerivAt_arcsin hax'.ne' hax.ne).comp a ((hasDerivAt_id a).div_const x)
      simpa [Function.comp_def] using this
    have hprim := (hhc.integral_hasStrictDerivAt 0 (Real.arcsin (a / x))).hasDerivAt.comp a harc
    refine hprim.congr_deriv ?_
    rw [Real.sin_arcsin hax'.le hax.le, mul_div_cancel₀ _ hx0.ne']
    have hsq : Real.sqrt (x ^ 2 - a ^ 2) = x * Real.sqrt (1 - (a / x) ^ 2) := by
      rw [show x ^ 2 - a ^ 2 = x ^ 2 * (1 - (a / x) ^ 2) by field_simp,
        Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le]
    rw [hsq]
    field_simp
  have hPc : ContinuousOn P (Icc 0 x) := by
    have hprimc : Continuous fun v => ∫ u in (0 : ℝ)..v, recoveryDensity (x * Real.sin u) :=
      continuous_iff_continuousAt.2 fun v => (hhc.integral_hasStrictDerivAt 0 v).hasDerivAt
        |>.continuousAt
    exact (hprimc.comp (Real.continuous_arcsin.comp (continuous_id.div_const x))).continuousOn
  have hnn : ∀ a ∈ Ioo (0 : ℝ) x, 0 ≤ recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2) := fun a ha =>
    div_nonneg (recoveryDensity_pos ha.1.le (ha.2.trans hx1)).le (Real.sqrt_nonneg _)
  obtain ⟨hi, hint⟩ := intervalIntegrable_and_integral_eq_of_deriv_nonneg hx0.le hPc hPd hnn
  refine ⟨hi, ?_⟩
  rw [hint, hP]
  simp only [div_self hx0.ne', Real.arcsin_one, zero_div, Real.arcsin_zero,
    intervalIntegral.integral_same, sub_zero]
  exact hang

theorem integral_recoveryDensity_div_sqrt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ a in (0 : ℝ)..x, recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2) = 1 / (2 * (1 - x)) :=
  (recoveryDensity_div_sqrt_abel hx0 hx1).2

/-! ### The second moment -/

/-- `∫_0^b a I(a) da = b - (1 - b²) I(b) + π/2`, from the primitive
`a - √(1-a²)(π/2 + arcsin a)`. -/
theorem integral_mul_recoveryI {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∫ a in (0 : ℝ)..b, a * recoveryI a = b - (1 - b ^ 2) * recoveryI b + π / 2 := by
  have hG : ∀ a ∈ uIcc (0 : ℝ) b, HasDerivAt
      (fun a => a - Real.sqrt (1 - a ^ 2) * (π / 2 + Real.arcsin a))
      (a * ((π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2))) a := by
    intro a ha
    rw [uIcc_of_le hb.1.le] at ha
    have h1 : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2, hb.2]
    have hs := Real.sqrt_pos.mpr h1
    have hs2 := Real.sq_sqrt h1.le
    have hsq : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2)) (-a / Real.sqrt (1 - a ^ 2)) a := by
      have := ((hasDerivAt_pow 2 a).const_sub 1).sqrt h1.ne'
      refine this.congr_deriv ?_
      field_simp; norm_num
    have harc : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - a ^ 2)) a :=
      Real.hasDerivAt_arcsin (by nlinarith [ha.1]) (by nlinarith [ha.2, hb.2])
    have := (hasDerivAt_id a).sub (hsq.mul ((hasDerivAt_const a (π / 2)).add harc))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, zero_add]
    field_simp
    ring
  have hcont : ContinuousOn (fun a => a * ((π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2)))
      (uIcc 0 b) := by
    rw [uIcc_of_le hb.1.le]
    refine continuousOn_id.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_)
    exact (Real.sqrt_pos.mpr (by nlinarith [ha.1, ha.2, hb.2])).ne'
  have h := integral_eq_sub_of_hasDerivAt hG hcont.intervalIntegrable
  have e : ∫ a in (0 : ℝ)..b, a * recoveryI a =
      ∫ a in (0 : ℝ)..b, a * ((π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2)) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le hb.1.le] at ha
    rw [recoveryI_eq_arcsin ⟨by linarith [ha.1], by linarith [ha.2, hb.2]⟩]
  rw [e, h, recoveryI_eq_arcsin ⟨by linarith [hb.1], hb.2⟩]
  have h1 : 0 < 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
  have h0 : Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [h0, Real.arcsin_zero]
  set s := Real.sqrt (1 - b ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 - b ^ 2 := Real.sq_sqrt h1.le
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  rw [← hs2]
  field_simp
  ring

/-- **`∫_0^b a² h(a) da = 2 - 2b/π - 3b²/2`** at the recovery edge. -/
theorem integral_sq_mul_recoveryDensity :
    ∫ a in (0 : ℝ)..recoveryEdge, a ^ 2 * recoveryDensity a =
      2 - 2 * recoveryEdge / π - 3 * recoveryEdge ^ 2 / 2 := by
  have hb := recoveryEdge_mem
  set b := recoveryEdge with hbdef
  have hu : ∀ x ∈ uIcc (0 : ℝ) b, HasDerivAt (fun a : ℝ => a ^ 2) (2 * x) x := fun x _ => by
    simpa using hasDerivAt_pow 2 x
  have hv : ∀ x ∈ uIcc (0 : ℝ) b, HasDerivAt recoveryMass (recoveryDensity x) x := fun x hx => by
    rw [uIcc_of_le hb.1.le] at hx
    exact hasDerivAt_recoveryMass ⟨by linarith [hx.1], by linarith [hx.2, hb.2]⟩
  have hv' : IntervalIntegrable recoveryDensity volume 0 b :=
    intervalIntegrable_recoveryDensity ⟨le_rfl, hb.1.le⟩ ⟨hb.1.le, le_rfl⟩
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun x : ℝ => 2 * x).intervalIntegrable _ _) hv']
  rw [recoveryMass_edge, recoveryMass_zero]
  -- `∫_0^b 2a H(a) da = (2/π)(∫ a I(a) - π b²/4)`
  have hH : ∫ a in (0 : ℝ)..b, 2 * a * recoveryMass a =
      2 / π * ((∫ a in (0 : ℝ)..b, a * recoveryI a) - π * b ^ 2 / 4) := by
    have e : ∫ a in (0 : ℝ)..b, 2 * a * recoveryMass a =
        ∫ a in (0 : ℝ)..b, 2 / π * (a * recoveryI a) - 2 / π * (π / 2 * a) := by
      refine intervalIntegral.integral_congr fun a ha => ?_
      rw [uIcc_of_le hb.1.le] at ha
      rw [recoveryMass, integral_recoveryDensity ha.1 (ha.2.trans_lt hb.2)]
      have := Real.pi_pos.ne'
      field_simp
    have hcI : ContinuousOn (fun a => a * recoveryI a) (uIcc 0 b) := by
      have : EqOn (fun a => a * ((π / 2 + Real.arcsin a) / Real.sqrt (1 - a ^ 2)))
          (fun a => a * recoveryI a) (uIcc 0 b) := fun a ha => by
        rw [uIcc_of_le hb.1.le] at ha
        beta_reduce
        rw [recoveryI_eq_arcsin ⟨by linarith [ha.1], by linarith [ha.2, hb.2]⟩]
      refine ContinuousOn.congr ?_ this.symm
      rw [uIcc_of_le hb.1.le]
      refine continuousOn_id.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => ?_)
      exact (Real.sqrt_pos.mpr (by nlinarith [ha.1, ha.2, hb.2])).ne'
    rw [e, integral_sub (hcI.intervalIntegrable.const_mul _)
      ((by fun_prop : Continuous fun a : ℝ => 2 / π * (π / 2 * a)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hH, integral_mul_recoveryI hb, recoveryI_edge]
  have := Real.pi_pos.ne'
  field_simp
  ring

/-! ### The mixture measure -/

/-- The mixing law `h(a)/π da` on `(0, b]`. -/
def recoveryMixingLaw : Measure ℝ :=
  (volume.restrict (Ioc 0 recoveryEdge)).withDensity fun a =>
    ((recoveryDensity a / π).toNNReal : ℝ≥0∞)

/-- **The equilibrium measure** `μ = ∫_0^b ν_a h(a) da`: the image of `h(a)/π da ⊗ dθ` on
`(0, b] × (0, π]` under `(a, θ) ↦ a cos θ` (the arcsine law `ν_a` is the image of `dθ/π` under
`θ ↦ a cos θ`). -/
def recoveryEquilibriumMeasure : Measure ℝ :=
  (recoveryMixingLaw.prod (volume.restrict (Ioc 0 π))).map fun p => p.1 * Real.cos p.2

theorem measurable_mul_cos : Measurable fun p : ℝ × ℝ => p.1 * Real.cos p.2 :=
  (continuous_fst.mul (Real.continuous_cos.comp continuous_snd)).measurable

theorem continuousOn_recoveryDensity_edge :
    ContinuousOn recoveryDensity (Icc 0 recoveryEdge) :=
  (continuousOn_recoveryDensity recoveryEdge_mem.1.le recoveryEdge_mem.2).mono fun a ha =>
    ⟨by linarith [ha.1, recoveryEdge_mem.1], ha.2⟩

theorem recoveryDensity_div_pi_nonneg {a : ℝ} (ha : a ∈ Ioc 0 recoveryEdge) :
    0 ≤ recoveryDensity a / π :=
  div_nonneg (recoveryDensity_pos ha.1.le (ha.2.trans_lt recoveryEdge_mem.2)).le Real.pi_pos.le

theorem aemeasurable_recoveryMixingDensity :
    AEMeasurable (fun a => (recoveryDensity a / π).toNNReal)
      (volume.restrict (Ioc 0 recoveryEdge)) :=
  (continuous_real_toNNReal.comp_continuousOn
    ((continuousOn_recoveryDensity_edge.mono Ioc_subset_Icc_self).div_const π)).aemeasurable
    measurableSet_Ioc

theorem integral_recoveryMixingLaw (g : ℝ → ℝ) :
    ∫ a, g a ∂recoveryMixingLaw =
      ∫ a in (0 : ℝ)..recoveryEdge, recoveryDensity a / π * g a := by
  rw [recoveryMixingLaw, integral_withDensity_eq_integral_smul₀
    aemeasurable_recoveryMixingDensity g, intervalIntegral.integral_of_le recoveryEdge_mem.1.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun a ha => ?_
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (recoveryDensity_div_pi_nonneg ha)]

theorem integrable_recoveryMixingLaw_iff {g : ℝ → ℝ} :
    Integrable g recoveryMixingLaw ↔
      IntegrableOn (fun a => recoveryDensity a / π * g a) (Ioc 0 recoveryEdge) := by
  rw [recoveryMixingLaw, integrable_withDensity_iff_integrable_smul₀
    aemeasurable_recoveryMixingDensity]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (recoveryDensity_div_pi_nonneg ha)]

theorem recoveryMixingLaw_univ : recoveryMixingLaw univ = ENNReal.ofReal (1 / π) := by
  have hint : IntegrableOn (fun a => recoveryDensity a / π) (Ioc 0 recoveryEdge) :=
    ((continuousOn_recoveryDensity_edge.div_const π).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [recoveryMixingLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ a in Ioc 0 recoveryEdge, ENNReal.ofReal (recoveryDensity a / π) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioc).mono fun a ha => recoveryDensity_div_pi_nonneg ha),
    ← intervalIntegral.integral_of_le recoveryEdge_mem.1.le, intervalIntegral.integral_div,
    integral_recoveryDensity_edge]

instance : IsFiniteMeasure recoveryMixingLaw :=
  ⟨by rw [recoveryMixingLaw_univ]; exact ENNReal.ofReal_lt_top⟩

instance : IsProbabilityMeasure recoveryEquilibriumMeasure := by
  refine ⟨?_⟩
  rw [recoveryEquilibriumMeasure, Measure.map_apply measurable_mul_cos MeasurableSet.univ,
    preimage_univ, ← univ_prod_univ, Measure.prod_prod, recoveryMixingLaw_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero,
    ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ Real.pi_pos.ne',
    ENNReal.ofReal_one]

/-- **Integration against `μ`.** -/
theorem integral_recoveryEquilibriumMeasure {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hint : Integrable (fun p : ℝ × ℝ => φ (p.1 * Real.cos p.2))
      (recoveryMixingLaw.prod (volume.restrict (Ioc 0 π)))) :
    ∫ y, φ y ∂recoveryEquilibriumMeasure =
      ∫ a in (0 : ℝ)..recoveryEdge, recoveryDensity a / π *
        ∫ θ in (0 : ℝ)..π, φ (a * Real.cos θ) := by
  rw [recoveryEquilibriumMeasure, integral_map measurable_mul_cos.aemeasurable
    hφ.aestronglyMeasurable, integral_prod _ hint, integral_recoveryMixingLaw]
  refine intervalIntegral.integral_congr fun a _ => ?_
  simp only
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]

/-- An integrability criterion on the product: integrable sections and an integrable majorant
of the section norms. -/
theorem integrable_recoveryMixture {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hsec : ∀ a, IntervalIntegrable (fun θ => φ (a * Real.cos θ)) volume 0 π) {g : ℝ → ℝ}
    (hg : IntegrableOn (fun a => recoveryDensity a / π * g a) (Ioc 0 recoveryEdge))
    (hbound : ∀ a ∈ Ioc 0 recoveryEdge, ∫ θ in (0 : ℝ)..π, |φ (a * Real.cos θ)| ≤ g a) :
    Integrable (fun p : ℝ × ℝ => φ (p.1 * Real.cos p.2))
      (recoveryMixingLaw.prod (volume.restrict (Ioc 0 π))) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => φ (p.1 * Real.cos p.2))
      (recoveryMixingLaw.prod (volume.restrict (Ioc 0 π))) :=
    (hφ.comp measurable_mul_cos).aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨Eventually.of_forall fun a => ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp (hsec a)
  · refine Integrable.mono' (integrable_recoveryMixingLaw_iff.mpr hg)
      hmeas.norm.integral_prod_right' ?_
    have hae : ∀ᵐ a ∂recoveryMixingLaw, a ∈ Ioc 0 recoveryEdge :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hae] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
    simpa only [Real.norm_eq_abs] using hbound a ha

/-! ### The second moment -/

/-- **`∫ t² dμ = 1 - b/π - 3b²/4`.** -/
theorem integral_sq_recoveryEquilibriumMeasure :
    ∫ y, y ^ 2 ∂recoveryEquilibriumMeasure =
      1 - recoveryEdge / π - 3 * recoveryEdge ^ 2 / 4 := by
  have hcos : ∀ a : ℝ, ∫ θ in (0 : ℝ)..π, (a * Real.cos θ) ^ 2 = a ^ 2 * (π / 2) := fun a => by
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_cos_sq]
    simp
  have habs : ∀ a : ℝ, ∫ θ in (0 : ℝ)..π, |(a * Real.cos θ) ^ 2| = a ^ 2 * (π / 2) := fun a => by
    have e : ∀ θ, |(a * Real.cos θ) ^ 2| = (a * Real.cos θ) ^ 2 := fun θ =>
      abs_of_nonneg (sq_nonneg _)
    simp_rw [e]; exact hcos a
  have hint := integrable_recoveryMixture (φ := fun y => y ^ 2) (by fun_prop)
    (fun a => (by fun_prop : Continuous fun θ => (a * Real.cos θ) ^ 2).intervalIntegrable _ _)
    (g := fun a => a ^ 2 * (π / 2))
    (((continuousOn_recoveryDensity_edge.div_const π).mul
      (by fun_prop : Continuous fun a : ℝ => a ^ 2 * (π / 2)).continuousOn).integrableOn_Icc
        |>.mono_set Ioc_subset_Icc_self)
    (fun a _ => (habs a).le)
  rw [integral_recoveryEquilibriumMeasure (by fun_prop) hint]
  simp_rw [hcos]
  have e : ∀ a, recoveryDensity a / π * (a ^ 2 * (π / 2)) = (1 / 2) * (a ^ 2 * recoveryDensity a) :=
    fun a => by have := Real.pi_pos.ne'; field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_sq_mul_recoveryDensity]
  ring

/-- **The mean root location constant** `A = (1 - ∫ t² dμ)/4 = b/(4π) + 3b²/16`. -/
theorem recoveryRootMean_eq :
    (1 - ∫ y, y ^ 2 ∂recoveryEquilibriumMeasure) / 4 =
      recoveryEdge / (4 * π) + 3 * recoveryEdge ^ 2 / 16 := by
  rw [integral_sq_recoveryEquilibriumMeasure]
  have := Real.pi_pos.ne'
  field_simp
  ring

/-! ### The logarithmic potential -/

theorem measurable_log_abs_sub (x : ℝ) : Measurable fun y : ℝ => Real.log |x - y| :=
  Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_const.sub measurable_id))

theorem log_abs_sub_mul_cos (x a θ : ℝ) :
    Real.log |x - a * Real.cos θ| = Real.log (a * Real.cos θ - x) := by
  rw [Real.log_abs, ← Real.log_neg_eq_log, neg_sub]

theorem intervalIntegrable_log_abs_sub_mul_cos (x a : ℝ) :
    IntervalIntegrable (fun θ => Real.log |x - a * Real.cos θ|) volume 0 π := by
  simp_rw [log_abs_sub_mul_cos]
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have h := intervalIntegrable_log_mul_cos_sub (neg_pos.mpr ha) (-x)
    refine h.congr fun θ _ => ?_
    rw [show -a * Real.cos θ - -x = -(a * Real.cos θ - x) by ring, Real.log_neg_eq_log]
  · simp only [zero_mul, zero_sub]; exact intervalIntegrable_const
  · exact intervalIntegrable_log_mul_cos_sub ha x

/-- The arcsine potential in gauge form: `∫_0^π log|x - a cos θ| dθ = π log g(a, |x|)`, `a > 0`. -/
theorem integral_log_abs_sub_mul_cos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.log |x - a * Real.cos θ| = π * Real.log (arcsineGauge a |x|) := by
  simp_rw [log_abs_sub_mul_cos]
  rcases le_or_gt |x| a with hxa | hax
  · rw [integral_log_mul_cos_sub_of_abs_le ha hxa, arcsineGauge_of_le hxa (abs_nonneg x)]
  · rw [integral_log_mul_cos_sub_of_lt_abs ha hax, arcsineGauge, max_eq_right hax.le, sq_abs]

/-- `|log z| ≤ 2 log 2 - log z` for `0 ≤ z ≤ 2`. -/
theorem abs_log_le_of_le_two {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2) :
    |Real.log z| ≤ 2 * Real.log 2 - Real.log z := by
  rcases eq_or_lt_of_le hz0 with rfl | hz
  · simp only [Real.log_zero, abs_zero, sub_zero]; positivity
  have hl2 : Real.log z ≤ Real.log 2 := Real.log_le_log hz hz2
  rcases le_or_gt 1 z with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]; linarith
  · rw [abs_of_neg (Real.log_neg hz h1)]; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem integral_abs_log_abs_sub_mul_cos_le {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : |x| ≤ 1) :
    ∫ θ in (0 : ℝ)..π, |Real.log (|x - a * Real.cos θ|)| ≤
      3 * π * Real.log 2 - π * Real.log a := by
  have hi := intervalIntegrable_log_abs_sub_mul_cos x a
  have hle : ∫ θ in (0 : ℝ)..π, |Real.log (|x - a * Real.cos θ|)| ≤
      ∫ θ in (0 : ℝ)..π, (2 * Real.log 2 - Real.log |x - a * Real.cos θ|) := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le hi.abs
      (intervalIntegrable_const.sub hi) fun θ _ => abs_log_le_of_le_two (abs_nonneg _) ?_
    have h1 := abs_sub x (a * Real.cos θ)
    have h2 : a * |Real.cos θ| ≤ 1 * 1 :=
      mul_le_mul ha1 (Real.abs_cos_le_one θ) (abs_nonneg _) zero_le_one
    rw [abs_mul, abs_of_pos ha] at h1
    linarith
  rw [integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero] at hle
  have hge : π * Real.log (a / 2) ≤ ∫ θ in (0 : ℝ)..π, Real.log |x - a * Real.cos θ| := by
    simp_rw [log_abs_sub_mul_cos]; exact integral_log_mul_cos_sub_ge ha x
  rw [Real.log_div ha.ne' two_ne_zero] at hge
  linarith

theorem integrable_log_abs_sub_recoveryMixture {x : ℝ} (hx : |x| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => Real.log |x - p.1 * Real.cos p.2|)
      (recoveryMixingLaw.prod (volume.restrict (Ioc 0 π))) := by
  have hb := recoveryEdge_mem
  refine integrable_recoveryMixture (measurable_log_abs_sub x)
    (fun a => intervalIntegrable_log_abs_sub_mul_cos x a)
    (g := fun a => 3 * π * Real.log 2 - π * Real.log a) ?_
    (fun a ha => integral_abs_log_abs_sub_mul_cos_le ha.1 (ha.2.trans hb.2.le) hx)
  have hi : IntervalIntegrable (fun a => recoveryDensity a / π *
      (3 * π * Real.log 2 - π * Real.log a)) volume 0 recoveryEdge := by
    refine (intervalIntegrable_const.sub (intervalIntegrable_log'.const_mul π)).continuousOn_mul
      ?_
    rw [uIcc_of_le hb.1.le]
    exact continuousOn_recoveryDensity_edge.div_const π
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.1.le).mp hi

/-- **The potential of `μ`** `∫ log|x - y| dμ(y) = ∫_0^b h(a) log g(a, |x|) da` for `|x| ≤ 1`. -/
theorem integral_log_abs_sub_recoveryEquilibriumMeasure {x : ℝ} (hx : |x| ≤ 1) :
    ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure =
      ∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a |x|) * recoveryDensity a := by
  rw [integral_recoveryEquilibriumMeasure (measurable_log_abs_sub x)
    (integrable_log_abs_sub_recoveryMixture hx)]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun a ha => ?_)
  rw [uIoc_of_le recoveryEdge_mem.1.le] at ha
  rw [integral_log_abs_sub_mul_cos ha.1 x]
  have := Real.pi_pos.ne'
  field_simp

/-- **Equilibrium on the support**: `∫ log|x - y| dμ(y) = log C - ½ log(1 - |x|)`, `|x| ≤ b`. -/
theorem recoveryEquilibrium_potential_eq {x : ℝ} (hx : |x| ≤ recoveryEdge) :
    ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure =
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - |x|) / 2 := by
  have hb := recoveryEdge_mem
  rw [integral_log_abs_sub_recoveryEquilibriumMeasure (hx.trans hb.2.le)]
  rcases eq_or_lt_of_le (abs_nonneg x) with h0 | hpos
  · rw [← h0, sub_zero, Real.log_one, zero_div, sub_zero,
      ← integral_log_half_mul_recoveryDensity_edge]
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [uIcc_of_le hb.1.le] at ha
    rw [arcsineGauge_of_le ha.1 le_rfl]
  · exact recoveryMixturePotential_eq hpos hx

/-- **Strict inequality off the support**, `b < |x| < 1`. -/
theorem recoveryEquilibrium_potential_lt {x : ℝ} (hbx : recoveryEdge < |x|) (hx1 : |x| < 1) :
    ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure <
      Real.log (recoveryCapacity recoveryEdge) - Real.log (1 - |x|) / 2 := by
  rw [integral_log_abs_sub_recoveryEquilibriumMeasure hx1.le]
  exact recoveryMixturePotential_lt hbx hx1

/-- The weighted potential `V(x) = U^μ(x) + Q(x) = -∫ log|x - y| dμ(y) - ½ log(1 - |x|)`. -/
def recoveryWeightedPotential (x : ℝ) : ℝ :=
  -∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure - Real.log (1 - |x|) / 2

theorem recoveryWeightedPotential_eq {x : ℝ} (hx : |x| ≤ recoveryEdge) :
    recoveryWeightedPotential x = -Real.log (recoveryCapacity recoveryEdge) := by
  rw [recoveryWeightedPotential, recoveryEquilibrium_potential_eq hx]; ring

theorem recoveryWeightedPotential_gt {x : ℝ} (hbx : recoveryEdge < |x|) (hx1 : |x| < 1) :
    -Real.log (recoveryCapacity recoveryEdge) < recoveryWeightedPotential x := by
  have := recoveryEquilibrium_potential_lt hbx hx1
  rw [recoveryWeightedPotential]; linarith

theorem arcsineExcess_mono {a s t : ℝ} (ha : 0 < a) (has : a ≤ s) (hst : s ≤ t) :
    arcsineExcess a s ≤ arcsineExcess a t := by
  unfold arcsineExcess
  rw [max_eq_right has, max_eq_right (has.trans hst)]
  have h1 : Real.sqrt (s ^ 2 - a ^ 2) ≤ Real.sqrt (t ^ 2 - a ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have := Real.log_le_log (by linarith [Real.sqrt_nonneg (s ^ 2 - a ^ 2)])
    (by linarith : s + Real.sqrt (s ^ 2 - a ^ 2) ≤ t + Real.sqrt (t ^ 2 - a ^ 2))
  linarith

/-- Off the support, `V(t) = -log C + ∫_b^t A(a,t) h(a) da`. -/
theorem recoveryWeightedPotential_eq_excess {t : ℝ} (hbt : recoveryEdge ≤ t) (ht1 : t < 1) :
    recoveryWeightedPotential t = -Real.log (recoveryCapacity recoveryEdge) +
      ∫ a in recoveryEdge..t, arcsineExcess a t * recoveryDensity a := by
  have hb := recoveryEdge_mem
  have ht0 : 0 < t := hb.1.trans_le hbt
  rw [recoveryWeightedPotential, abs_of_pos ht0,
    integral_log_abs_sub_recoveryEquilibriumMeasure (by rw [abs_of_pos ht0]; exact ht1.le),
    abs_of_pos ht0, integral_log_arcsineGauge_mul_recoveryDensity hb ht0,
    integral_log_half_mul_recoveryDensity_edge]
  have hA := integral_arcsineExcess_mul_recoveryDensity ht0 ht1
  have hsplit := integral_add_adjacent_intervals (b := recoveryEdge)
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 hb.1.le hb.2)
    ((intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 hb.1.le hb.2).symm.trans
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht0 ht0.le ht1))
  linarith

theorem arcsineExcess_pos {a t : ℝ} (ha : 0 < a) (hat : a < t) : 0 < arcsineExcess a t := by
  unfold arcsineExcess
  rw [max_eq_right hat.le, sub_pos]
  exact Real.log_lt_log ha (lt_of_lt_of_le hat (le_add_of_nonneg_right (Real.sqrt_nonneg _)))

theorem intervalIntegrable_arcsineExcess_mul_recoveryDensity' {t c d : ℝ} (ht : 0 < t)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    IntervalIntegrable (fun a => arcsineExcess a t * recoveryDensity a) volume c d :=
  (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht hc0 hc1).symm.trans
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity ht hd0 hd1)

/-- **`V` is strictly increasing on `[b, 1)`.** -/
theorem recoveryWeightedPotential_strictMonoOn :
    StrictMonoOn recoveryWeightedPotential (Ico recoveryEdge 1) := by
  have hb := recoveryEdge_mem
  intro s hs t ht hst
  rw [recoveryWeightedPotential_eq_excess hs.1 hs.2, recoveryWeightedPotential_eq_excess ht.1 ht.2]
  have ht0 : 0 < t := hb.1.trans_le ht.1
  have hs0 : 0 < s := hb.1.trans_le hs.1
  have h1 : ∫ a in recoveryEdge..s, arcsineExcess a s * recoveryDensity a ≤
      ∫ a in recoveryEdge..s, arcsineExcess a t * recoveryDensity a :=
    intervalIntegral.integral_mono_on hs.1
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity' hs0 hb.1.le hb.2 hs0.le hs.2)
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity' ht0 hb.1.le hb.2 hs0.le hs.2)
      fun a ha => mul_le_mul_of_nonneg_right
        (arcsineExcess_mono (hb.1.trans_le ha.1) ha.2 hst.le)
        (recoveryDensity_pos (hb.1.le.trans ha.1) (ha.2.trans_lt hs.2)).le
  have h2 := integral_add_adjacent_intervals
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity' ht0 hb.1.le hb.2 hs0.le hs.2)
    (intervalIntegrable_arcsineExcess_mul_recoveryDensity' ht0 hs0.le hs.2 ht0.le ht.2)
  have h3 : 0 < ∫ a in s..t, arcsineExcess a t * recoveryDensity a :=
    intervalIntegral_pos_of_pos_on
      (intervalIntegrable_arcsineExcess_mul_recoveryDensity' ht0 hs0.le hs.2 ht0.le ht.2)
      (fun a ha => mul_pos (arcsineExcess_pos (hs0.trans ha.1) ha.2)
        (recoveryDensity_pos (hs0.trans ha.1).le (ha.2.trans ht.2))) hst
  linarith

/-! ### The derivative of the weighted potential -/

/-- **Zero derivative on the support**: `V' = 0` on `(-b, b)`. -/
theorem hasDerivAt_recoveryWeightedPotential_of_lt {t : ℝ} (ht : |t| < recoveryEdge) :
    HasDerivAt recoveryWeightedPotential 0 t := by
  refine (hasDerivAt_const t (-Real.log (recoveryCapacity recoveryEdge))).congr_of_eventuallyEq ?_
  have hmem : Ioo (-recoveryEdge) recoveryEdge ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
  filter_upwards [hmem] with y hy
  exact recoveryWeightedPotential_eq (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)

/-- The derivative of `a ↦ log g(a, y)` in `y` off the support: `1/√(y² - a²)` for `0 ≤ a < y`. -/
theorem hasDerivAt_log_arcsineGauge {a y : ℝ} (ha : 0 ≤ a) (hay : a < y) :
    HasDerivAt (fun y => Real.log (arcsineGauge a y)) (1 / Real.sqrt (y ^ 2 - a ^ 2)) y := by
  have hy0 : 0 < y := ha.trans_lt hay
  have h1 : 0 < y ^ 2 - a ^ 2 := by nlinarith
  set σ := Real.sqrt (y ^ 2 - a ^ 2) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr h1
  have hsq : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - a ^ 2)) (y / σ) y := by
    have := ((hasDerivAt_pow 2 y).sub_const (a ^ 2)).sqrt h1.ne'
    refine this.congr_deriv ?_
    rw [← hσ]; field_simp; norm_num
  have hg : HasDerivAt (fun y : ℝ => (y + Real.sqrt (y ^ 2 - a ^ 2)) / 2) ((1 + y / σ) / 2) y :=
    ((hasDerivAt_id y).add hsq).div_const 2
  have hpos : 0 < (y + Real.sqrt (y ^ 2 - a ^ 2)) / 2 := by positivity
  have hlog := hg.log hpos.ne'
  have heq : (fun y => Real.log (arcsineGauge a y)) =ᶠ[𝓝 y]
      fun y => Real.log ((y + Real.sqrt (y ^ 2 - a ^ 2)) / 2) := by
    filter_upwards [Ioi_mem_nhds hay] with z hz
    rw [arcsineGauge, max_eq_right (le_of_lt hz)]
  refine (hlog.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [← hσ]
  field_simp
  ring

/-- **The derivative off the support**: for `b < t < 1`,
`V'(t) = 1/(2(1-t)) - ∫_0^b h(a)/√(t² - a²) da`. -/
theorem hasDerivAt_recoveryWeightedPotential {t : ℝ} (hbt : recoveryEdge < t) (ht1 : t < 1) :
    HasDerivAt recoveryWeightedPotential
      (1 / (2 * (1 - t)) - ∫ a in (0 : ℝ)..recoveryEdge,
        recoveryDensity a / Real.sqrt (t ^ 2 - a ^ 2)) t := by
  have hb := recoveryEdge_mem
  have ht0 : 0 < t := hb.1.trans hbt
  set c := (recoveryEdge + t) / 2 with hc
  have hbc : recoveryEdge < c := by rw [hc]; linarith
  have hct : c < t := by rw [hc]; linarith
  have hmS : Ioo c 1 ∈ 𝓝 t := Ioo_mem_nhds hct ht1
  have hcb : 0 < c ^ 2 - recoveryEdge ^ 2 := by nlinarith [hb.1]
  set M := Real.sqrt (c ^ 2 - recoveryEdge ^ 2) with hM
  have hM0 : 0 < M := Real.sqrt_pos.mpr hcb
  have hhc := continuousOn_recoveryDensity_edge
  have huIoc : uIoc 0 recoveryEdge ⊆ Icc 0 recoveryEdge := by
    rw [uIoc_of_le hb.1.le]; exact Ioc_subset_Icc_self
  -- differentiation under the integral sign
  have hdiff := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := recoveryEdge) (x₀ := t) (s := Ioo c 1)
    (F := fun x a => Real.log (arcsineGauge a x) * recoveryDensity a)
    (F' := fun x a => recoveryDensity a / Real.sqrt (x ^ 2 - a ^ 2))
    (bound := fun a => recoveryDensity a / M) hmS
    (by
      filter_upwards [Ioi_mem_nhds ht0] with x hx
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      exact (((continuous_arcsineGauge x).log fun _ => (arcsineGauge_pos hx).ne').continuousOn.mul
        hhc).mono huIoc)
    (intervalIntegrable_log_arcsineGauge_mul_recoveryDensity ht0 hb.1.le hb.2)
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine (hhc.div (by fun_prop) fun a ha => ?_).mono huIoc
      exact (Real.sqrt_pos.mpr (by nlinarith [ha.1, ha.2])).ne')
    (by
      refine Eventually.of_forall fun a ha x hx => ?_
      rw [uIoc_of_le hb.1.le] at ha
      have hh := (recoveryDensity_pos ha.1.le (ha.2.trans_lt hb.2)).le
      have hxa : c ^ 2 - recoveryEdge ^ 2 ≤ x ^ 2 - a ^ 2 := by
        nlinarith [hx.1, ha.1, ha.2, hb.1]
      have hsq : M ≤ Real.sqrt (x ^ 2 - a ^ 2) := Real.sqrt_le_sqrt hxa
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hh (Real.sqrt_nonneg _))]
      exact div_le_div_of_nonneg_left hh hM0 hsq)
    ((hhc.div_const M).intervalIntegrable_of_Icc hb.1.le)
    (by
      refine Eventually.of_forall fun a ha x hx => ?_
      rw [uIoc_of_le hb.1.le] at ha
      have hax : a < x := by linarith [ha.2, hx.1]
      have := (hasDerivAt_log_arcsineGauge ha.1.le hax).mul_const (recoveryDensity a)
      refine this.congr_deriv ?_
      ring)
  -- the potential near `t`
  have heq : recoveryWeightedPotential =ᶠ[𝓝 t] fun x =>
      -(∫ a in (0 : ℝ)..recoveryEdge, Real.log (arcsineGauge a x) * recoveryDensity a) -
        Real.log (1 - x) / 2 := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with x hx
    rw [recoveryWeightedPotential, abs_of_pos hx.1,
      integral_log_abs_sub_recoveryEquilibriumMeasure (by rw [abs_of_pos hx.1]; exact hx.2.le),
      abs_of_pos hx.1]
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x) / 2) (-1 / (1 - t) / 2) t :=
    (((hasDerivAt_id t).const_sub 1).log (sub_ne_zero.mpr (ne_of_gt ht1))).div_const 2
      |>.congr_deriv (by simp)
  refine ((hdiff.2.neg.sub hlog).congr_of_eventuallyEq heq).congr_deriv ?_
  have : (1 : ℝ) - t ≠ 0 := by linarith
  field_simp
  ring

/-- **The derivative is positive off the support**: `∫_0^b h(a)/√(t² - a²) da < 1/(2(1-t))` for
`b < t < 1`, since the Abel integral over `[0, t]` equals `1/(2(1-t))`. -/
theorem integral_recoveryDensity_div_sqrt_lt {t : ℝ} (hbt : recoveryEdge < t) (ht1 : t < 1) :
    ∫ a in (0 : ℝ)..recoveryEdge, recoveryDensity a / Real.sqrt (t ^ 2 - a ^ 2) <
      1 / (2 * (1 - t)) := by
  have hb := recoveryEdge_mem
  have ht0 : 0 < t := hb.1.trans hbt
  obtain ⟨hi, hval⟩ := recoveryDensity_div_sqrt_abel ht0 ht1
  have hbmem : recoveryEdge ∈ uIcc 0 t := by
    rw [uIcc_of_le ht0.le]; exact ⟨hb.1.le, hbt.le⟩
  have hi1 := hi.mono_set (uIcc_subset_uIcc_left hbmem)
  have hi2 := hi.mono_set (uIcc_subset_uIcc_right hbmem)
  rw [← hval, ← integral_add_adjacent_intervals hi1 hi2]
  have hpos : 0 < ∫ a in recoveryEdge..t, recoveryDensity a / Real.sqrt (t ^ 2 - a ^ 2) :=
    intervalIntegral_pos_of_pos_on hi2 (fun a ha => div_pos
      (recoveryDensity_pos (hb.1.le.trans ha.1.le) (ha.2.trans ht1))
      (Real.sqrt_pos.mpr (by nlinarith [ha.1, ha.2, hb.1]))) hbt
  linarith

theorem deriv_recoveryWeightedPotential_pos {t : ℝ} (hbt : recoveryEdge < t) (ht1 : t < 1) :
    0 < 1 / (2 * (1 - t)) - ∫ a in (0 : ℝ)..recoveryEdge,
      recoveryDensity a / Real.sqrt (t ^ 2 - a ^ 2) := by
  have := integral_recoveryDensity_div_sqrt_lt hbt ht1
  linarith

/-! ### Continuity of the potential -/

theorem arcsineGauge_le_one {a t : ℝ} (ha1 : a ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    arcsineGauge a t ≤ 1 := by
  unfold arcsineGauge
  have h1 : max a t ≤ 1 := max_le ha1 ht1
  have h2 : Real.sqrt (t ^ 2 - a ^ 2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg a])
  linarith

theorem half_le_arcsineGauge_left (a t : ℝ) : a / 2 ≤ arcsineGauge a t := by
  unfold arcsineGauge
  have := le_max_left a t
  have := Real.sqrt_nonneg (t ^ 2 - a ^ 2)
  linarith

/-- **The potential of `μ` is continuous on `[-1, 1]`**, by dominated convergence with the
majorant `(|log a| + log 2) h(a)`. -/
theorem continuousOn_potential_recoveryEquilibriumMeasure :
    ContinuousOn (fun x => ∫ y, Real.log |x - y| ∂recoveryEquilibriumMeasure) (Icc (-1) 1) := by
  have hb := recoveryEdge_mem
  set F : ℝ → ℝ → ℝ := fun x a => Real.log (arcsineGauge a (min |x| 1)) * recoveryDensity a
    with hF
  have hcont : Continuous fun x => ∫ a in (0 : ℝ)..recoveryEdge, F x a := by
    refine intervalIntegral.continuous_of_dominated_interval
      (bound := fun a => (|Real.log a| + Real.log 2) * recoveryDensity a) ?_ ?_ ?_ ?_
    · intro x
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      rw [uIoc_of_le hb.1.le]
      refine ContinuousOn.mul ?_ (continuousOn_recoveryDensity_edge.mono Ioc_subset_Icc_self)
      refine ContinuousOn.log (by
        unfold arcsineGauge; fun_prop) fun a ha => ?_
      exact (lt_of_lt_of_le (by linarith [ha.1]) (half_le_arcsineGauge_left a _)).ne'
    · intro x
      refine Eventually.of_forall fun a ha => ?_
      rw [uIoc_of_le hb.1.le] at ha
      have hh := (recoveryDensity_pos ha.1.le (ha.2.trans_lt hb.2)).le
      have ht0 : 0 ≤ min |x| 1 := le_min (abs_nonneg x) zero_le_one
      have hg1 := arcsineGauge_le_one (ha.2.trans hb.2.le) ht0 (min_le_right _ _)
      have hg0 := half_le_arcsineGauge_left a (min |x| 1)
      have hlow : Real.log (a / 2) ≤ Real.log (arcsineGauge a (min |x| 1)) :=
        Real.log_le_log (by linarith [ha.1]) hg0
      have hup : Real.log (arcsineGauge a (min |x| 1)) ≤ 0 :=
        Real.log_nonpos (by linarith [ha.1]) hg1
      rw [Real.log_div ha.1.ne' two_ne_zero] at hlow
      rw [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh]
      refine mul_le_mul_of_nonneg_right ?_ hh
      rw [abs_of_nonpos hup]
      have := neg_abs_le (Real.log a)
      linarith
    · refine (IntervalIntegrable.add intervalIntegrable_log'.abs intervalIntegrable_const)
        |>.mul_continuousOn ?_
      rw [uIcc_of_le hb.1.le]; exact continuousOn_recoveryDensity_edge
    · refine Eventually.of_forall fun a ha => ?_
      rw [uIoc_of_le hb.1.le] at ha
      refine Continuous.mul (Continuous.log (by unfold arcsineGauge; fun_prop) fun x => ?_)
        continuous_const
      exact (lt_of_lt_of_le (by linarith [ha.1]) (half_le_arcsineGauge_left a _)).ne'
  refine hcont.continuousOn.congr fun x hx => ?_
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  rw [integral_log_abs_sub_recoveryEquilibriumMeasure hx1]
  simp only [hF, min_eq_left hx1]

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
