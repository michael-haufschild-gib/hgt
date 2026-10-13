import GaloisForLFunctions.RHTower.CosDilationPeriodicMultiplierUnfolding

/-!
# Logarithmic primitive energy identity and half-line autocorrelation sign rigidity

Let `f : ℝ → ℝ` be continuous and supported in `[α, β]` (`0 < α ≤ β`), with dilation
autocorrelation `A_f(r) = ∫_0^∞ f(y) f(ry) dy` (`dilationAutocorr`), cosine–dilation kernel
`Ψ_f = Cf ⋆ f` (`cosDilationKernel`), and primitive core `F(y) = ∫_0^y f(t) dt` (`primCore`).

* **Exact half-interval primitive energy identity** (`intervalIntegral_zero_one_dilationAutocorr_eq`):
  without assuming blindness or zero mean,
  `∫ r in 0..1, A_f(r) dr = F(β)² / (2β) + ½ ∫ y in α..β, (F(y) / y)² dy`.
* **Universal half-interval positivity and rigidity on `[0, 1]`**
  (`intervalIntegral_zero_one_dilationAutocorr_nonneg`,
  `eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos`,
  `eq_zero_of_dilationAutocorr_nonpos_on_Ioo_zero_one`):
  for every continuous core `f` supported in `[α, β] ⊂ (0, ∞)`, `∫_0^1 A_f(r) dr ≥ 0`, with
  `∫_0^1 A_f(r) dr ≤ 0` (and in particular `A_f ≤ 0` on `(0, 1)`) if and only if `f = 0`.
* **Upper half-line anti-positivity and sign rigidity on `(1, ∞)`**
  (`integral_Ioi_one_dilationAutocorr_eq_neg`,
  `integral_Ioi_one_dilationAutocorr_nonpos`,
  `eq_zero_of_integral_Ioi_one_dilationAutocorr_nonneg`,
  `eq_zero_of_dilationAutocorr_nonneg_on_Ioi_one`):
  when `Ψ_f(0) = 0`, `F(β) = ∫_0^∞ f = 0` and `∫_0^∞ A_f(r) dr = ½ Ψ_f(0) = 0`, so
  `∫_{r > 1} A_f(r) dr = −∫_0^1 A_f(r) dr = −½ ∫ y in α..β, (F(y) / y)² dy ≤ 0`.
  Consequently, if `∫_{r > 1} A_f(r) dr ≥ 0` (and in particular if `A_f(r) ≥ 0` for all `r > 1`),
  then `f = 0` (without requiring smoothness or blindness of `f`).
-/

open MeasureTheory Set Real Filter

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### The primitive core `F(y) = ∫_0^y f(t) dt` -/

/-- The primitive core `F(y) = ∫ t in 0..y, f(t) dt`. -/
def primCore (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, f t

theorem hasDerivAt_primCore (hf : Continuous f) (y : ℝ) :
    HasDerivAt (primCore f) (f y) y :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 y)
    (hf.stronglyMeasurableAtFilter volume (nhds y)) hf.continuousAt

theorem continuous_primCore (hf : Continuous f) : Continuous (primCore f) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_primCore hf y).continuousAt

/-- If `f` is supported in `[α, β]` (`0 < α`), then `primCore f y = 0` for all `y ≤ α`. -/
theorem primCore_eq_zero_of_le {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y : ℝ} (hy : y ≤ α) :
    primCore f y = 0 := by
  unfold primCore
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) y → f t = (0 : ℝ) := by
    filter_upwards [Measure.ae_ne volume α] with t ht_ne ht_mem
    rw [uIoc] at ht_mem
    have hle : t ≤ max 0 y := ht_mem.2
    have hmax : max 0 y ≤ α := max_le hα.le hy
    have hlt : t < α := lt_of_le_of_ne (hle.trans hmax) ht_ne
    by_contra h
    exact not_le.mpr hlt (hsupp t h).1
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`), then `primCore f y = primCore f β`
for all `y ≥ β`. -/
theorem primCore_eq_primCore_beta_of_ge (hf : Continuous f) {α β : ℝ}
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y : ℝ} (hy : β ≤ y) :
    primCore f y = primCore f β := by
  unfold primCore
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 β) (hf.intervalIntegrable β y)]
  have hzero : ∫ t in β..y, f t = 0 := by
    rw [intervalIntegral.integral_of_le hy]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    rw [mem_Ioc] at ht
    by_contra h
    exact not_le.mpr ht.1 (hsupp t h).2
  linarith

/-- For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`),
`primCore f β = ∫_{y > 0} f(y) dy`. -/
theorem primCore_beta_eq_integral_Ioi {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    primCore f β = ∫ y in Ioi (0 : ℝ), f y := by
  have hβ0 : 0 ≤ β := (lt_of_lt_of_le hα hαβ).le
  unfold primCore
  rw [intervalIntegral.integral_of_le hβ0]
  have h1 : ∫ y in Ioc (0 : ℝ) β, f y = ∫ y, f y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    by_contra h
    obtain ⟨hy1, hy2⟩ := hsupp y h
    rcases hy with hy | hy
    · linarith
    · linarith
  have h2 : ∫ y in Ioi (0 : ℝ), f y = ∫ y, f y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra h
    exact hy (lt_of_lt_of_le hα (hsupp y h).1)
  rw [h1, h2]

/-- For `y > 0`, `∫ r in 0..1, f(ry) dr = primCore f y / y`. -/
theorem intervalIntegral_zero_one_mul_right {y : ℝ} (hy : 0 < y) :
    ∫ r in (0 : ℝ)..1, f (r * y) = primCore f y / y := by
  have h := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) f hy.ne'
  simp only [zero_mul, one_mul, smul_eq_mul] at h
  rw [h, primCore, inv_mul_eq_div]

/-! ### Exact half-interval primitive energy identity for `∫_0^1 A_f(r) dr` -/

/-- For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`),
`A_f(r) = ∫ y in α..β, f(y) f(ry) dy`. -/
theorem dilationAutocorr_eq_intervalIntegral (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (r : ℝ) :
    dilationAutocorr f r = ∫ y in α..β, f y * f (r * y) := by
  have hfα : f α = 0 := by
    have hcl : IsClosed {z | f z = 0} := isClosed_eq hf continuous_const
    have hsub : Iio α ⊆ {z | f z = 0} := fun z hz => by
      by_contra h
      exact not_le.mpr hz (hsupp z h).1
    have hc := hcl.closure_subset_iff.mpr hsub
    rw [closure_Iio] at hc
    exact hc (mem_Iic.mpr le_rfl)
  unfold dilationAutocorr
  rw [intervalIntegral.integral_of_le hαβ]
  have h1 : ∫ y in Ioi (0 : ℝ), f y * f (r * y) = ∫ y, f y * f (r * y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    have : f y = 0 := by
      by_contra h
      exact hy (lt_of_lt_of_le hα (hsupp y h).1)
    simp [this]
  have h2 : ∫ y in Ioc α β, f y * f (r * y) = ∫ y, f y * f (r * y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    have : f y = 0 := by
      by_contra h
      obtain ⟨hy1, hy2⟩ := hsupp y h
      rcases eq_or_lt_of_le hy1 with rfl | hy1'
      · exact h hfα
      · exact hy ⟨hy1', hy2⟩
    simp [this]
  rw [h1, h2]

/-- Fubini swap on `[0, 1] × [α, β]`:
`∫ r in 0..1, A_f(r) dr = ∫ y in α..β, f(y) * (primCore f y / y) dy`. -/
theorem intervalIntegral_zero_one_dilationAutocorr_eq_integral_mul_primCore (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ r in (0 : ℝ)..1, dilationAutocorr f r =
      ∫ y in α..β, f y * (primCore f y / y) := by
  simp_rw [dilationAutocorr_eq_intervalIntegral hf hα hαβ hsupp]
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp_rw [intervalIntegral.integral_of_le hαβ]
  have hint : Integrable (Function.uncurry fun r y : ℝ => f y * f (r * y))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc α β))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hcont : Continuous (Function.uncurry fun r y : ℝ => f y * f (r * y)) := by
      unfold Function.uncurry
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hy0 : 0 < y := lt_trans hα hy.1
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, intervalIntegral_zero_one_mul_right hy0]

/-- **Exact half-interval primitive energy identity (`[0, 1]`).**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`),
`∫ r in 0..1, A_f(r) dr = (primCore f β)² / (2β) + ½ ∫ y in α..β, (primCore f y / y)² dy`. -/
theorem intervalIntegral_zero_one_dilationAutocorr_eq (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ r in (0 : ℝ)..1, dilationAutocorr f r =
      (primCore f β) ^ 2 / (2 * β) + 1 / 2 * ∫ y in α..β, (primCore f y / y) ^ 2 := by
  rw [intervalIntegral_zero_one_dilationAutocorr_eq_integral_mul_primCore hf hα hαβ hsupp]
  set H : ℝ → ℝ := fun y => primCore f y * primCore f y / (2 * y) with hH
  set g1 : ℝ → ℝ := fun y => f y * (primCore f y / y) with hg1
  set g2 : ℝ → ℝ := fun y => 1 / 2 * (primCore f y / y) ^ 2 with hg2
  have hF_cont : Continuous (primCore f) := continuous_primCore hf
  have hy_pos : ∀ y ∈ uIcc α β, 0 < y := by
    intro y hy
    rw [uIcc_of_le hαβ] at hy
    exact lt_of_lt_of_le hα hy.1
  have hy_ne : ∀ y ∈ uIcc α β, y ≠ 0 := fun y hy => (hy_pos y hy).ne'
  have hg1_cont : ContinuousOn g1 (uIcc α β) := by
    refine hf.continuousOn.mul (hF_cont.continuousOn.div continuousOn_id hy_ne)
  have hg2_cont : ContinuousOn g2 (uIcc α β) := by
    refine continuousOn_const.mul ((hF_cont.continuousOn.div continuousOn_id hy_ne).pow 2)
  have hderiv : ∀ y ∈ uIcc α β, HasDerivAt H (g1 y - g2 y) y := by
    intro y hy
    have hy0 : 0 < y := hy_pos y hy
    have hdF : HasDerivAt (primCore f) (f y) y := hasDerivAt_primCore hf y
    have hdy : HasDerivAt (fun z : ℝ => 2 * z) (2 * 1) y := (hasDerivAt_id y).const_mul 2
    have hdH := (hdF.mul hdF).div hdy (by positivity : (2 * y : ℝ) ≠ 0)
    have h_eq : g1 y - g2 y =
        ((f y * primCore f y + primCore f y * f y) * (2 * y) -
          primCore f y * primCore f y * (2 * 1)) / (2 * y) ^ 2 := by
      have : y ≠ 0 := hy0.ne'
      change f y * (primCore f y / y) - 1 / 2 * (primCore f y / y) ^ 2 = _
      field_simp
      ring
    rwa [h_eq]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hg1_cont.sub hg2_cont).intervalIntegrable
  rw [intervalIntegral.integral_sub hg1_cont.intervalIntegrable hg2_cont.intervalIntegrable] at hFTC
  have hHα : H α = 0 := by
    simp only [hH, primCore_eq_zero_of_le hα hsupp le_rfl, zero_mul, zero_div]
  have hHβ : H β = (primCore f β) ^ 2 / (2 * β) := by
    simp only [hH, sq]
  have h_int_g2 : ∫ y in α..β, g2 y = 1 / 2 * ∫ y in α..β, (primCore f y / y) ^ 2 := by
    simp only [hg2, intervalIntegral.integral_const_mul]
  linarith

/-! ### Universal half-interval positivity and rigidity on `[0, 1]` -/

/-- **Universal half-interval autocorrelation positivity.**
For every continuous core `f` supported in `[α, β]` (`0 < α ≤ β`),
`0 ≤ ∫ r in 0..1, A_f(r) dr`. -/
theorem intervalIntegral_zero_one_dilationAutocorr_nonneg (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    0 ≤ ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  rw [intervalIntegral_zero_one_dilationAutocorr_eq hf hα hαβ hsupp]
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h1 : 0 ≤ (primCore f β) ^ 2 / (2 * β) := by positivity
  have h2 : 0 ≤ ∫ y in α..β, (primCore f y / y) ^ 2 :=
    intervalIntegral.integral_nonneg hαβ fun y _ => sq_nonneg _
  linarith

/-- **Universal half-interval autocorrelation rigidity on `[0, 1]`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) and `∫ r in 0..1, A_f(r) dr ≤ 0`,
then `f = 0` everywhere (without assuming blindness or zero mean). -/
theorem eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hnonpos : ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ 0) (y : ℝ) :
    f y = 0 := by
  have hEq := intervalIntegral_zero_one_dilationAutocorr_eq hf hα hαβ hsupp
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h1 : 0 ≤ (primCore f β) ^ 2 / (2 * β) := by positivity
  have h2 : 0 ≤ ∫ z in α..β, (primCore f z / z) ^ 2 :=
    intervalIntegral.integral_nonneg hαβ fun z _ => sq_nonneg _
  have hFβ_sq : (primCore f β) ^ 2 / (2 * β) = 0 := by linarith
  have hFβ : primCore f β = 0 := by
    have h0 : (primCore f β) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hFβ_sq).resolve_right (by positivity)
    exact sq_eq_zero_iff.mp h0
  have h_int_zero : ∫ z in α..β, (primCore f z / z) ^ 2 = 0 := by linarith
  have hF_cont : Continuous (primCore f) := continuous_primCore hf
  have hF_supp : ∀ z ∉ Ioc α β, primCore f z = 0 := by
    intro z hz
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hz
    rcases hz with hz | hz
    · exact primCore_eq_zero_of_le hα hsupp hz
    · rw [primCore_eq_primCore_beta_of_ge hf hsupp hz.le, hFβ]
  have hF_compact : HasCompactSupport (primCore f) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun z hz => ?_
    exact hF_supp z fun h => hz ⟨h.1.le, h.2⟩
  have hF2_int : Integrable fun z => (primCore f z) ^ 2 :=
    (hF_cont.pow 2).integrable_of_hasCompactSupport (by
      refine HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun z hz => ?_
      have := hF_supp z fun h => hz ⟨h.1.le, h.2⟩
      simp [this])
  have hF2_eq : ∫ z, (primCore f z) ^ 2 = ∫ z in α..β, (primCore f z) ^ 2 := by
    rw [intervalIntegral.integral_of_le hαβ]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    simp [hF_supp z hz]
  have h_div_int : IntervalIntegrable (fun z => (primCore f z / z) ^ 2) volume α β := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hαβ]
    refine (hF_cont.continuousOn.div continuousOn_id fun z hz => ?_).pow 2
    exact (lt_of_lt_of_le hα hz.1).ne'
  have hF2_le : ∫ z in α..β, (primCore f z / β) ^ 2 ≤ ∫ z in α..β, (primCore f z / z) ^ 2 := by
    refine intervalIntegral.integral_mono_on hαβ (((hF_cont.div_const β).pow 2).intervalIntegrable α β)
      h_div_int fun z hz => ?_
    have hz0 : 0 < z := lt_of_lt_of_le hα hz.1
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz0 2)
      (pow_le_pow_left₀ hz0.le hz.2 2)
  have hF2_zero : ∫ z, (primCore f z) ^ 2 = 0 := by
    have h0 : 0 ≤ ∫ z, (primCore f z) ^ 2 := integral_nonneg fun z => sq_nonneg _
    have h_scale : ∫ z in α..β, (primCore f z / β) ^ 2 =
        (1 / β ^ 2) * ∫ z in α..β, (primCore f z) ^ 2 := by
      have h_eq : (fun z => (primCore f z / β) ^ 2) =
          fun z => (1 / β ^ 2) * (primCore f z) ^ 2 := by
        funext z; ring
      rw [h_eq, intervalIntegral.integral_const_mul]
    rw [h_int_zero, h_scale, ← hF2_eq] at hF2_le
    have h_nonpos : ∫ z, (primCore f z) ^ 2 ≤ 0 := by
      by_contra hpos
      have hgt : 0 < ∫ z, (primCore f z) ^ 2 := not_le.mp hpos
      have : 0 < (1 / β ^ 2) * ∫ z, (primCore f z) ^ 2 := by positivity
      linarith
    linarith
  have hae : (fun z => (primCore f z) ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hF2_int).mp hF2_zero
  have heq := (Continuous.ae_eq_iff_eq volume (hF_cont.pow 2) continuous_const).mp hae
  have hF_zero : ∀ z, primCore f z = 0 := fun z => sq_eq_zero_iff.mp (congrFun heq z)
  have hd1 : HasDerivAt (primCore f) (f y) y := hasDerivAt_primCore hf y
  have hd2 : HasDerivAt (primCore f) 0 y := by
    have h_eq : primCore f = fun _ => (0 : ℝ) := funext hF_zero
    rw [h_eq]
    exact hasDerivAt_const y 0
  exact hd1.unique hd2

/-- If `A_f(r) ≤ 0` for all `r ∈ (0, 1)`, then `f = 0` everywhere. -/
theorem eq_zero_of_dilationAutocorr_nonpos_on_Ioo_zero_one (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hnonpos : ∀ r ∈ Ioo (0 : ℝ) 1, dilationAutocorr f r ≤ 0) (y : ℝ) :
    f y = 0 := by
  have hA : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hIcc : ∀ r ∈ Icc (0 : ℝ) 1, dilationAutocorr f r ≤ 0 := by
    have hcl : IsClosed {r | dilationAutocorr f r ≤ 0} := isClosed_le hA continuous_const
    have hc := hcl.closure_subset_iff.mpr hnonpos
    rwa [closure_Ioo zero_ne_one] at hc
  have hint_nonpos : ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ 0 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_nonpos measurableSet_Ioc fun r hr => hIcc r ⟨hr.1.le, hr.2⟩
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos
    hf hα hαβ hsupp hint_nonpos y

/-! ### Upper half-line anti-positivity and sign rigidity on `(1, ∞)` -/

/-- For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`),
`∫_{r > 0} A_f(r) dr = ½ Ψ_f(0)`. -/
theorem integral_Ioi_dilationAutocorr_eq_half_cosDilationKernel_zero (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ r in Ioi (0 : ℝ), dilationAutocorr f r = 1 / 2 * cosDilationKernel f 0 := by
  have h := cosDilationKernel_eq hf hα hαβ hsupp 0
  simp only [ zero_mul, mul_zero, Real.cos_zero, mul_one] at h
  linarith

/-- Splitting `∫_{r > 0} A_f(r) dr` at `r = 1`:
`∫ r in 0..1, A_f(r) dr + ∫_{r > 1} A_f(r) dr = ½ Ψ_f(0)`. -/
theorem intervalIntegral_zero_one_add_integral_Ioi_one_dilationAutocorr (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    (∫ r in (0 : ℝ)..1, dilationAutocorr f r) + (∫ r in Ioi (1 : ℝ), dilationAutocorr f r) =
      1 / 2 * cosDilationKernel f 0 := by
  rw [← integral_Ioi_dilationAutocorr_eq_half_cosDilationKernel_zero hf hα hαβ hsupp,
    intervalIntegral.integral_of_le zero_le_one]
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hA_supp : HasCompactSupport (dilationAutocorr f) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := α / β) (b := β / α)) fun r hr => ?_
    exact dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp hr
  have hA_int : Integrable (dilationAutocorr f) :=
    hA_cont.integrable_of_hasCompactSupport hA_supp
  have h_union : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi zero_le_one
  have h_disj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    disjoint_iff_inf_le.mpr fun r hr => not_lt.mpr hr.1.2 hr.2
  rw [← setIntegral_union h_disj measurableSet_Ioi hA_int.integrableOn hA_int.integrableOn,
    h_union]

/-- **Upper half-line primitive energy identity (`(1, ∞)`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0`, then
`∫_{r > 1} A_f(r) dr = −∫ r in 0..1, A_f(r) dr = −½ ∫ y in α..β, (primCore f y / y)² dy`. -/
theorem integral_Ioi_one_dilationAutocorr_eq_neg (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0) :
    ∫ r in Ioi (1 : ℝ), dilationAutocorr f r =
      -∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  have h := intervalIntegral_zero_one_add_integral_Ioi_one_dilationAutocorr hf hα hαβ hsupp
  rw [h0, mul_zero] at h
  linarith

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0`, then
`∫_{r > 1} A_f(r) dr ≤ 0`. -/
theorem integral_Ioi_one_dilationAutocorr_nonpos (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0) :
    ∫ r in Ioi (1 : ℝ), dilationAutocorr f r ≤ 0 := by
  rw [integral_Ioi_one_dilationAutocorr_eq_neg hf hα hαβ hsupp h0]
  linarith [intervalIntegral_zero_one_dilationAutocorr_nonneg hf hα hαβ hsupp]

/-- **Upper half-line autocorrelation rigidity.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and
`0 ≤ ∫_{r > 1} A_f(r) dr`, then `f = 0` everywhere (without assuming blindness or smoothness). -/
theorem eq_zero_of_integral_Ioi_one_dilationAutocorr_nonneg (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hnonneg : 0 ≤ ∫ r in Ioi (1 : ℝ), dilationAutocorr f r) (y : ℝ) :
    f y = 0 := by
  have h := integral_Ioi_one_dilationAutocorr_eq_neg hf hα hαβ hsupp h0
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos
    hf hα hαβ hsupp (by linarith) y

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and
`A_f(r) ≥ 0` for all `r > 1`, then `f = 0` everywhere. -/
theorem eq_zero_of_dilationAutocorr_nonneg_on_Ioi_one (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hnonneg : ∀ r > (1 : ℝ), 0 ≤ dilationAutocorr f r) (y : ℝ) :
    f y = 0 := by
  have hint_nonneg : 0 ≤ ∫ r in Ioi (1 : ℝ), dilationAutocorr f r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr => hnonneg r hr
  exact eq_zero_of_integral_Ioi_one_dilationAutocorr_nonneg hf hα hαβ hsupp h0 hint_nonneg y

end

end RHTower
