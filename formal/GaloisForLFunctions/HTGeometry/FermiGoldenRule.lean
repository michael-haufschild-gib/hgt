import GaloisForLFunctions.HTGeometry.FermiGoldenRuleModel

/-!
# Fermi's golden rule: a fully discharged instance

`FermiGoldenRuleModel` proves Fermi's golden rule for an arbitrary Friedrichs model.  This file
builds one such model explicitly, so that every hypothesis of that theorem is discharged and the
golden rule appears with no side conditions beyond the data of the physical problem: a band
`(a, b)` of continuum states, an unperturbed level `E₀` inside the band, and a continuous form
factor `v`.

The label space is `ℝ` and the label measure is

```text
μ = δ_{b+1} + Lebesgue|_(a,b) ,
```

one atom carrying the bound state, placed outside the band, plus the band itself.  The energy
function is the identity on the band and `E₀` at the atom, so the spectral measure of the form
factor is literally `‖v‖² dE` on the band and the density of states at `E₀` is `‖v E₀‖²`.
-/

open MeasureTheory Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace BandModel

/-! ## The label measure -/

/-- The label measure: an atom carrying the bound state, plus Lebesgue measure on the band. -/
def bandMeasure (a b : ℝ) : Measure ℝ := Measure.dirac (b + 1) + volume.restrict (Ioo a b)

instance instIsFiniteMeasure (a b : ℝ) : IsFiniteMeasure (bandMeasure a b) := by
  refine ⟨?_⟩
  rw [bandMeasure, Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ, Real.volume_Ioo,
    MeasureTheory.measure_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩

theorem integrable_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {f : ℝ → E} (hf : AEStronglyMeasurable f (bandMeasure a b)) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (bandMeasure a b) :=
  memLp_one_iff_integrable.mp (MemLp.of_bound hf C (Filter.Eventually.of_forall hC))

theorem integral_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : ℝ → E} (hf : Integrable f (bandMeasure a b)) :
    ∫ x, f x ∂(bandMeasure a b) = f (b + 1) + ∫ x in Ioo a b, f x := by
  rw [bandMeasure] at hf ⊢
  rw [integral_add_measure hf.left_of_add_measure hf.right_of_add_measure, integral_dirac]

/-! ## The energy function -/

/-- The energy function: the identity on the band, and `E₀` at the bound-state label. -/
def bandEnergy (a b E₀ : ℝ) : ℝ → ℝ := fun x => if x = b + 1 then E₀ else max a (min b x)

theorem measurable_bandEnergy (a b E₀ : ℝ) : Measurable (bandEnergy a b E₀) := by
  unfold bandEnergy
  refine Measurable.ite (measurableSet_singleton (b + 1)) measurable_const ?_
  fun_prop

theorem bandEnergy_le {a b : ℝ} (hab : a ≤ b) (E₀ : ℝ) (x : ℝ) :
    |bandEnergy a b E₀ x| ≤ |a| + |b| + |E₀| := by
  unfold bandEnergy
  have h0a : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h0b : (0 : ℝ) ≤ |b| := abs_nonneg b
  have h0E : (0 : ℝ) ≤ |E₀| := abs_nonneg E₀
  split_ifs with h
  · linarith
  · have h1 : a ≤ max a (min b x) := le_max_left _ _
    have h2 : max a (min b x) ≤ b := max_le hab (min_le_left _ _)
    have h3 : -|a| ≤ a := neg_abs_le a
    have h4 : b ≤ |b| := le_abs_self b
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

theorem bandEnergy_of_mem {a b E₀ : ℝ} {x : ℝ} (hx : x ∈ Ioo a b) : bandEnergy a b E₀ x = x := by
  have hne : x ≠ b + 1 := by
    intro hc
    have h := hx.2
    rw [hc] at h
    linarith
  rw [bandEnergy, if_neg hne, min_eq_right hx.2.le, max_eq_right hx.1.le]

@[simp] theorem bandEnergy_site (a b E₀ : ℝ) : bandEnergy a b E₀ (b + 1) = E₀ := by
  rw [bandEnergy, if_pos rfl]

/-! ## The bound state and the form factor -/

/-- The bound state: the indicator of the atom. -/
def boundFun (b : ℝ) : ℝ → ℂ := ({b + 1} : Set ℝ).indicator (fun _ => (1 : ℂ))

/-- The form factor: the band restriction of `v`. -/
def formFun (a b : ℝ) (v : ℝ → ℂ) : ℝ → ℂ := (Ioo a b).indicator v

@[simp] theorem boundFun_site (b : ℝ) : boundFun b (b + 1) = 1 :=
  Set.indicator_of_mem (by simp) _

theorem boundFun_of_mem {a b : ℝ} {x : ℝ} (hx : x ∈ Ioo a b) : boundFun b x = 0 := by
  refine Set.indicator_of_notMem ?_ _
  intro hc
  have h := hx.2
  rw [Set.mem_singleton_iff.mp hc] at h
  linarith

@[simp] theorem formFun_site (a b : ℝ) (v : ℝ → ℂ) : formFun a b v (b + 1) = 0 := by
  refine Set.indicator_of_notMem ?_ _
  intro hc
  have h := hc.2
  linarith

theorem formFun_of_mem {a b : ℝ} {x : ℝ} (v : ℝ → ℂ) (hx : x ∈ Ioo a b) :
    formFun a b v x = v x := Set.indicator_of_mem hx v

theorem norm_boundFun_le (b : ℝ) (x : ℝ) : ‖boundFun b x‖ ≤ 1 := by
  rw [boundFun]
  by_cases hx : x ∈ ({b + 1} : Set ℝ)
  · rw [Set.indicator_of_mem hx]; simp
  · rw [Set.indicator_of_notMem hx]; simp

theorem measurable_boundFun (b : ℝ) : Measurable (boundFun b) :=
  measurable_const.indicator (measurableSet_singleton _)

theorem measurable_formFun {a b : ℝ} {v : ℝ → ℂ} (hv : Continuous v) :
    Measurable (formFun a b v) := hv.measurable.indicator measurableSet_Ioo

theorem exists_bound_formFun (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) :
    ∃ C : ℝ, ∀ x, ‖formFun a b v x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hv.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Ioo a b
  · rw [formFun_of_mem v hx]
    exact le_trans (hC x (Ioo_subset_Icc_self hx)) (le_max_left _ _)
  · rw [formFun, Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

theorem memLp_boundFun (a b : ℝ) : MemLp (boundFun b) 2 (bandMeasure a b) :=
  MemLp.of_bound (measurable_boundFun b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_boundFun_le b))

theorem memLp_formFun (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) :
    MemLp (formFun a b v) 2 (bandMeasure a b) := by
  obtain ⟨C, hC⟩ := exists_bound_formFun a b hv
  exact MemLp.of_bound (measurable_formFun hv).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-! ## The `L²` vectors -/

/-- The bound state as an `L²` class. -/
def boundVec (a b : ℝ) : Lp ℂ 2 (bandMeasure a b) := (memLp_boundFun a b).toLp _

/-- The form factor as an `L²` class. -/
def formVec (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) : Lp ℂ 2 (bandMeasure a b) :=
  (memLp_formFun a b hv).toLp _

theorem coeFn_boundVec (a b : ℝ) :
    ((boundVec a b : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) =ᵐ[bandMeasure a b] boundFun b :=
  (memLp_boundFun a b).coeFn_toLp

theorem coeFn_formVec (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) :
    ((formVec a b hv : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) =ᵐ[bandMeasure a b] formFun a b v :=
  (memLp_formFun a b hv).coeFn_toLp

theorem norm_boundVec (a b : ℝ) : ‖boundVec a b‖ = 1 := by
  have hint : Integrable (fun x : ℝ => ‖boundFun b x‖ ^ 2) (bandMeasure a b) := by
    refine integrable_of_bound ((measurable_boundFun b).norm.pow_const 2).aestronglyMeasurable
      (C := 1) fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [norm_boundFun_le b x, norm_nonneg (boundFun b x)]
  have hsq : ‖boundVec a b‖ ^ 2 = 1 := by
    rw [lpTwo_norm_sq_eq_integral]
    have hcong : (∫ x, ‖((boundVec a b : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) x‖ ^ 2
          ∂(bandMeasure a b))
        = ∫ x, ‖boundFun b x‖ ^ 2 ∂(bandMeasure a b) := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_boundVec a b] with x hx
      rw [hx]
    have hband : (∫ x in Ioo a b, ‖boundFun b x‖ ^ 2) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ : ℝ => (0 : ℝ))
        fun x hx => by rw [boundFun_of_mem hx]; simp]
      simp
    rw [hcong, integral_band hint, boundFun_site, hband]
    simp
  calc ‖boundVec a b‖ = Real.sqrt (‖boundVec a b‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

theorem inner_boundVec_formVec (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) :
    (inner ℂ (boundVec a b) (formVec a b hv) : ℂ) = 0 := by
  obtain ⟨C, hC⟩ := exists_bound_formFun a b hv
  have hconj : Measurable fun x : ℝ => (starRingEnd ℂ) (boundFun b x) :=
    Complex.continuous_conj.measurable.comp (measurable_boundFun b)
  have hint : Integrable
      (fun x : ℝ => (starRingEnd ℂ) (boundFun b x) * formFun a b v x) (bandMeasure a b) := by
    refine integrable_of_bound (C := 1 * |C|)
      ((hconj.mul (measurable_formFun hv)).aestronglyMeasurable) fun x => ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (norm_boundFun_le b x) (le_trans (hC x) (le_abs_self C))
      (norm_nonneg _) zero_le_one
  have hcong : (∫ x, (inner ℂ (((boundVec a b : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) x)
        (((formVec a b hv : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) x) : ℂ) ∂(bandMeasure a b))
      = ∫ x, (starRingEnd ℂ) (boundFun b x) * formFun a b v x ∂(bandMeasure a b) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_boundVec a b, coeFn_formVec a b hv] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
    ring
  have hband : (∫ x in Ioo a b, (starRingEnd ℂ) (boundFun b x) * formFun a b v x) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ : ℝ => (0 : ℂ))
      fun x hx => by rw [boundFun_of_mem hx]; simp]
    simp
  rw [L2.inner_def, hcong, integral_band hint, formFun_site, hband]
  simp

/-! ## The model -/

/-- **The concrete Friedrichs model** attached to a band `(a, b)`, a level `E₀`, and a continuous
form factor `v`. -/
def bandModel (a b E₀ : ℝ) (hab : a < b) {v : ℝ → ℂ} (hv : Continuous v) :
    FriedrichsModel ℝ (bandMeasure a b) where
  energy := bandEnergy a b E₀
  measurable_energy := measurable_bandEnergy a b E₀
  cutoff := |a| + |b| + |E₀|
  cutoff_nonneg := by positivity
  energy_le := bandEnergy_le hab.le E₀
  level := E₀
  bound := boundVec a b
  form := formVec a b hv
  norm_bound := norm_boundVec a b
  eigen := by
    filter_upwards [coeFn_boundVec a b] with x hx
    rw [hx]
    by_cases hxs : x = b + 1
    · rw [hxs, bandEnergy_site]
    · rw [boundFun, Set.indicator_of_notMem (by simpa using hxs)]
      ring
  ortho := inner_boundVec_formVec a b hv

/-! ## The density of states -/

/-- The density of states of the band model: `‖v‖²` on the band, zero outside. -/
def bandDensity (a b : ℝ) (v : ℝ → ℂ) : ℝ → ℝ := (Ioo a b).indicator fun E => ‖v E‖ ^ 2

theorem integrable_bandDensity (a b : ℝ) {v : ℝ → ℂ} (hv : Continuous v) :
    Integrable (bandDensity a b v) (volume : Measure ℝ) := by
  rw [bandDensity, integrable_indicator_iff measurableSet_Ioo]
  refine IntegrableOn.mono_set ?_ Ioo_subset_Icc_self
  exact ((hv.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc

theorem continuousAt_bandDensity {a b E₀ : ℝ} (ha : a < E₀) (hb : E₀ < b) {v : ℝ → ℂ}
    (hv : Continuous v) : ContinuousAt (bandDensity a b v) E₀ := by
  have hnb : Ioo a b ∈ nhds E₀ := Ioo_mem_nhds ha hb
  have heq : (fun E : ℝ => ‖v E‖ ^ 2) =ᶠ[nhds E₀] bandDensity a b v := by
    filter_upwards [hnb] with x hx
    rw [bandDensity, Set.indicator_of_mem hx]
  exact ContinuousAt.congr (by fun_prop) heq

theorem bandDensity_apply {a b E₀ : ℝ} (ha : a < E₀) (hb : E₀ < b) (v : ℝ → ℂ) :
    bandDensity a b v E₀ = ‖v E₀‖ ^ 2 := by
  rw [bandDensity, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ha, hb⟩)]

/-- **The spectral measure of the form factor is `‖v‖² dE` on the band.** -/
theorem bandModel_density (a b E₀ : ℝ) {v : ℝ → ℂ} (hv : Continuous v) (t : ℝ) :
    (∫ x, goldenRuleKernel t (bandEnergy a b E₀ x - E₀)
        * ‖((formVec a b hv : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) x‖ ^ 2 ∂(bandMeasure a b))
      = ∫ E : ℝ, goldenRuleKernel t (E - E₀) * bandDensity a b v E := by
  obtain ⟨C, hC⟩ := exists_bound_formFun a b hv
  have hint : Integrable
      (fun x : ℝ => goldenRuleKernel t (bandEnergy a b E₀ x - E₀) * ‖formFun a b v x‖ ^ 2)
      (bandMeasure a b) := by
    refine integrable_of_bound (C := |t ^ 2| * |C| ^ 2) ?_ fun x => ?_
    · exact (((continuous_goldenRuleKernel t).measurable.comp
        ((measurable_bandEnergy a b E₀).sub measurable_const)).mul
        ((measurable_formFun hv).norm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (goldenRuleKernel_nonneg _ _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖formFun a b v x‖ ^ 2)]
      have h1 : goldenRuleKernel t (bandEnergy a b E₀ x - E₀) ≤ |t ^ 2| :=
        le_trans (goldenRuleKernel_le_sq _ _) (le_abs_self _)
      have h2 : ‖formFun a b v x‖ ^ 2 ≤ |C| ^ 2 := by
        have h3 := le_trans (hC x) (le_abs_self C)
        nlinarith [norm_nonneg (formFun a b v x), abs_nonneg C]
      exact mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
  have hcong : (∫ x, goldenRuleKernel t (bandEnergy a b E₀ x - E₀)
        * ‖((formVec a b hv : Lp ℂ 2 (bandMeasure a b)) : ℝ → ℂ) x‖ ^ 2 ∂(bandMeasure a b))
      = ∫ x, goldenRuleKernel t (bandEnergy a b E₀ x - E₀) * ‖formFun a b v x‖ ^ 2
        ∂(bandMeasure a b) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_formVec a b hv] with x hx
    rw [hx]
  have hband : (∫ x in Ioo a b, goldenRuleKernel t (bandEnergy a b E₀ x - E₀)
        * ‖formFun a b v x‖ ^ 2)
      = ∫ x in Ioo a b, goldenRuleKernel t (x - E₀) * ‖v x‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [bandEnergy_of_mem hx, formFun_of_mem v hx]
  have hlast : (∫ E : ℝ, goldenRuleKernel t (E - E₀) * bandDensity a b v E)
      = ∫ x in Ioo a b, goldenRuleKernel t (x - E₀) * ‖v x‖ ^ 2 := by
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [bandDensity, Set.indicator_apply]
    split_ifs with hx
    · rfl
    · rw [mul_zero]
  rw [hcong, integral_band hint, bandEnergy_site, formFun_site, hband, hlast]
  simp

/-! ## Fermi's golden rule -/

/-- **Fermi's golden rule.**  In the band Friedrichs model with continuous form factor `v` and
unperturbed level `E₀` strictly inside the band `(a, b)`, the first-order transition probability out
of the bound state grows linearly in time with rate `2 π λ² ‖v E₀‖²`. -/
theorem tendsto_bandModel_firstOrder (a b E₀ : ℝ) (hab : a < b) (ha : a < E₀) (hb : E₀ < b)
    {v : ℝ → ℂ} (hv : Continuous v) (lam : ℝ) :
    Filter.Tendsto (fun t : ℝ => ‖(bandModel a b E₀ hab hv).firstOrder lam t‖ ^ 2 / t)
      Filter.atTop (nhds (2 * Real.pi * lam ^ 2 * ‖v E₀‖ ^ 2)) := by
  have h := (bandModel a b E₀ hab hv).tendsto_normSq_firstOrder lam
    (integrable_bandDensity a b hv) (continuousAt_bandDensity ha hb hv)
    (bandModel_density a b E₀ hv)
  have h2 : bandDensity a b v (bandModel a b E₀ hab hv).level = ‖v E₀‖ ^ 2 :=
    bandDensity_apply ha hb v
  rwa [h2] at h

/-- **Fermi's golden rule with its error control.**  The rate statement together with the
second-order bound tying the first-order Dyson term to the exact Schrödinger evolution. -/
theorem fermi_golden_rule (a b E₀ : ℝ) (hab : a < b) (ha : a < E₀) (hb : E₀ < b)
    {v : ℝ → ℂ} (hv : Continuous v) (lam : ℝ) :
    Filter.Tendsto (fun t : ℝ => ‖(bandModel a b E₀ hab hv).firstOrder lam t‖ ^ 2 / t)
        Filter.atTop (nhds (2 * Real.pi * lam ^ 2 * ‖v E₀‖ ^ 2))
      ∧ ∀ t : ℝ, 0 ≤ t →
        ‖(bandModel a b E₀ hab hv).evol lam t (bandModel a b E₀ hab hv).bound
            - (bandModel a b E₀ hab hv).freeProp t (bandModel a b E₀ hab hv).bound
            - (bandModel a b E₀ hab hv).firstOrder lam t‖
          ≤ lam ^ 2 * ‖(bandModel a b E₀ hab hv).coupling‖ ^ 2 * t ^ 2 :=
  ⟨tendsto_bandModel_firstOrder a b E₀ hab ha hb hv lam,
    fun _ ht => (bandModel a b E₀ hab hv).norm_sub_firstOrder_le lam ht⟩

end BandModel

end GaloisForLFunctions.HTGeometry
