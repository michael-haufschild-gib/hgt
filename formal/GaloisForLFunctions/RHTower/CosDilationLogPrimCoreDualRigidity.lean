import GaloisForLFunctions.RHTower.CosDilationPrimitiveEnergyRigidity

/-!
# Logarithmic primitive core and inversion-dual cumulative autocorrelation rigidity

Let `f : ℝ → ℝ` be continuous and supported in `[α, β]` (`0 < α ≤ β`) with zero mean
`∫_{y > 0} f(y) dy = 0`, and let `F(y) = ∫_0^y f(t) dt` (`primCore f y`). Define the
**logarithmic primitive core**
`g(y) = F(y) / y` (`logPrimCore f y`).

* **Regularity, support, and energy of `logPrimCore`**
  (`continuous_logPrimCore`, `logPrimCore_support`,
  `dilationAutocorr_logPrimCore_one_eq`):
  `logPrimCore f` is continuous on all of `ℝ`, supported in the exact same interval `[α, β]` as `f`,
  and its self-autocorrelation at `r = 1` satisfies
  `A_{logPrimCore f}(1) = 2 ∫ r in 0..1, A_f(r) dr`.
* **Inversion-dual cumulative autocorrelation identity**
  (`intervalIntegral_dilationAutocorr_add_inv_eq`):
  for every `s > 0`,
  `(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr) = s * A_{logPrimCore f}(s)`.
* **Global and disjoint-preimage cumulative autocorrelation bounds**
  (`abs_intervalIntegral_dilationAutocorr_add_inv_le`,
  `abs_intervalIntegral_dilationAutocorr_add_inv_le_of_le_sq_mul`,
  `abs_intervalIntegral_dilationAutocorr_add_inv_le_of_sq_mul_le`):
  - for all `s > 0`,
    `|(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr)| ≤ 2 √s ∫ r in 0..1, A_f(r) dr`;
  - whenever `β ≤ s² α` (or `s² β ≤ α`), the bound sharpens by a factor of `½`:
    `|(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr)| ≤ √s ∫ r in 0..1, A_f(r) dr`.
-/

open MeasureTheory Set Real Filter

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### The logarithmic primitive core `g(y) = (∫_0^y f(t) dt) / y` -/

/-- The logarithmic primitive core `g(y) = primCore f y / y = (∫_0^y f(t) dt) / y`. -/
def logPrimCore (f : ℝ → ℝ) (y : ℝ) : ℝ := primCore f y / y

/-- If `f` is supported in `[α, β]` (`0 < α`), then `logPrimCore f y = 0` for all `y ≤ α`. -/
theorem logPrimCore_eq_zero_of_le {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y : ℝ} (hy : y ≤ α) :
    logPrimCore f y = 0 := by
  simp only [logPrimCore, primCore_eq_zero_of_le hα hsupp hy, zero_div]

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
then `primCore f y = 0` for all `y ≥ β`. -/
theorem primCore_eq_zero_of_ge (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    {y : ℝ} (hy : β ≤ y) :
    primCore f y = 0 := by
  rw [primCore_eq_primCore_beta_of_ge hf hsupp hy,
    primCore_beta_eq_integral_Ioi hα hαβ hsupp, hmean]

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
then `logPrimCore f y = 0` for all `y ≥ β`. -/
theorem logPrimCore_eq_zero_of_ge (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    {y : ℝ} (hy : β ≤ y) :
    logPrimCore f y = 0 := by
  simp only [logPrimCore, primCore_eq_zero_of_ge hf hα hαβ hsupp hmean hy, zero_div]

/-- If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
then `logPrimCore f` is supported in `[α, β]`. -/
theorem logPrimCore_support (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (y : ℝ) (hy : logPrimCore f y ≠ 0) :
    α ≤ y ∧ y ≤ β := by
  constructor
  · by_contra hlt
    exact hy (logPrimCore_eq_zero_of_le hα hsupp (le_of_not_ge hlt))
  · by_contra hgt
    exact hy (logPrimCore_eq_zero_of_ge hf hα hαβ hsupp hmean (le_of_not_ge hgt))

/-- If `f` is continuous and supported in `[α, β]` (`0 < α`), then `logPrimCore f` is continuous on
all of `ℝ`. -/
theorem continuous_logPrimCore (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Continuous (logPrimCore f) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_or_ge 0 y with hy | hy
  ·exact ((continuous_primCore hf).continuousAt.div continuousAt_id hy.ne')
  · have h_ev : logPrimCore f =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt hy hα)] with z hz
      exact logPrimCore_eq_zero_of_le hα hsupp hz.le
    exact continuousAt_const.congr h_ev.symm

/-- **Energy identity for `logPrimCore` at `r = 1`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`, then
`A_{logPrimCore f}(1) = 2 ∫ r in 0..1, A_f(r) dr`. -/
theorem dilationAutocorr_logPrimCore_one_eq (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) :
    dilationAutocorr (logPrimCore f) 1 =
      2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  rw [dilationAutocorr_eq_intervalIntegral hg_cont hα hαβ hg_supp 1,
    intervalIntegral_zero_one_dilationAutocorr_eq hf hα hαβ hsupp,
    primCore_beta_eq_integral_Ioi hα hαβ hsupp, hmean]
  have h_congr : ∀ y : ℝ, logPrimCore f y * logPrimCore f (1 * y) = (primCore f y / y) ^ 2 := by
    intro y
    simp only [logPrimCore, one_mul, sq]
  simp_rw [h_congr]
  ring

/-! ### General cumulative autocorrelation integral `∫_0^s A_f(r) dr` -/

/-- For `y > 0` and any `s ∈ ℝ`, `∫ r in 0..s, f(ry) dr = primCore f (s * y) / y`. -/
theorem intervalIntegral_zero_mul_right {y : ℝ} (hy : 0 < y) (s : ℝ) :
    ∫ r in (0 : ℝ)..s, f (r * y) = primCore f (s * y) / y := by
  have h := intervalIntegral.integral_comp_mul_right (a := 0) (b := s) f hy.ne'
  simp only [zero_mul, smul_eq_mul] at h
  rw [h, primCore, inv_mul_eq_div]

/-- Fubini representation of `∫ r in 0..s, A_f(r) dr` for `s ≥ 0`:
`∫ r in 0..s, A_f(r) dr = ∫ y in α..β, f(y) * (primCore f (s * y) / y) dy`. -/
theorem intervalIntegral_zero_dilationAutocorr_eq_integral_mul_primCore (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ r in (0 : ℝ)..s, dilationAutocorr f r =
      ∫ y in α..β, f y * (primCore f (s * y) / y) := by
  simp_rw [dilationAutocorr_eq_intervalIntegral hf hα hαβ hsupp]
  rw [intervalIntegral.integral_of_le hs]
  simp_rw [intervalIntegral.integral_of_le hαβ]
  have hint : Integrable (Function.uncurry fun r y : ℝ => f y * f (r * y))
      ((volume.restrict (Ioc (0 : ℝ) s)).prod (volume.restrict (Ioc α β))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hcont : Continuous (Function.uncurry fun r y : ℝ => f y * f (r * y)) := by
      unfold Function.uncurry
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hy0 : 0 < y := lt_trans hα hy.1
  rw [← intervalIntegral.integral_of_le hs,
    intervalIntegral.integral_const_mul, intervalIntegral_zero_mul_right hy0 s]

/-- Extending an interval integral over `α..β` to any wider interval `a..b` (`a ≤ α`, `β ≤ b`)
when the integrand vanishes outside `[α, β]`. -/
private lemma intervalIntegral_eq_of_support_subset {g : ℝ → ℝ} (hg : Continuous g)
    {α β a b : ℝ} (ha : a ≤ α) (hb : β ≤ b)
    (hsupp : ∀ y, g y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ y in a..b, g y = ∫ y in α..β, g y := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable a α : IntervalIntegrable g volume a α)
    (hg.intervalIntegrable α b : IntervalIntegrable g volume α b)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable α β : IntervalIntegrable g volume α β)
    (hg.intervalIntegrable β b : IntervalIntegrable g volume β b)
  have hz1 : ∫ y in a..α, g y = 0 := by
    rw [intervalIntegral.integral_of_le ha]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    rw [mem_Ioc] at hy
    have hae : ∀ z < α, g z = 0 := fun z hz => by
      by_contra h
      exact not_le.mpr hz (hsupp z h).1
    have hcl : IsClosed {z | g z = 0} := isClosed_eq hg continuous_const
    have hc := hcl.closure_subset_iff.mpr (fun z (hz : z ∈ Iio α) => hae z hz)
    rw [closure_Iio] at hc
    exact hc (mem_Iic.mpr hy.2)
  have hz2 : ∫ y in β..b, g y = 0 := by
    rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    rw [mem_Ioc] at hy
    by_contra h
    exact not_le.mpr hy.1 (hsupp y h).2
  linarith

/-! ### Inversion-dual cumulative autocorrelation law -/

/-- **Inversion-dual cumulative autocorrelation identity.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `s > 0`,
`(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr) = s * A_{logPrimCore f}(s)`. -/
theorem intervalIntegral_dilationAutocorr_add_inv_eq (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) :
    (∫ r in (0 : ℝ)..s, dilationAutocorr f r) +
      s * (∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r) =
      s * dilationAutocorr (logPrimCore f) s := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hsinv : 0 < s⁻¹ := inv_pos.mpr hs
  have hF_cont : Continuous (primCore f) := continuous_primCore hf
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  set a : ℝ := min α (α / s) with ha_def
  set b : ℝ := max β (β / s) with hb_def
  have ha_pos : 0 < a := lt_min hα (div_pos hα hs)
  have ha_le_α : a ≤ α := min_le_left _ _
  have hα_le_b : β ≤ b := le_max_left _ _
  have hab : a ≤ b := (ha_le_α.trans hαβ).trans hα_le_b
  have hsa_le_α : s * a ≤ α := by
    calc s * a ≤ s * (α / s) := mul_le_mul_of_nonneg_left (min_le_right _ _) hs.le
      _ = α := mul_div_cancel₀ α hs.ne'
  have hβ_le_sb : β ≤ s * b := by
    calc β = s * (β / s) := (mul_div_cancel₀ β hs.ne').symm
      _ ≤ s * b := mul_le_mul_of_nonneg_left (le_max_right _ _) hs.le
  -- Term 1: `∫ r in 0..s, A_f(r) dr = ∫ y in a..b, f y * logPrimCore f (s * y) * s`
  have hTerm1 : ∫ r in (0 : ℝ)..s, dilationAutocorr f r =
      ∫ y in a..b, f y * (primCore f (s * y) / y) := by
    rw [intervalIntegral_zero_dilationAutocorr_eq_integral_mul_primCore hf hα hαβ hsupp hs.le]
    have hcont1 : Continuous fun y => f y * (primCore f (s * y) / y) := by
      have h_eq : (fun y => f y * (primCore f (s * y) / y)) =
          fun y => f y * (s * logPrimCore f (s * y)) := by
        funext y
        simp only [logPrimCore]
        have : s ≠ 0 := hs.ne'
        field_simp
      rw [h_eq]
      exact hf.mul (continuous_const.mul (hg_cont.comp (continuous_const.mul continuous_id)))
    symm
    exact intervalIntegral_eq_of_support_subset hcont1 ha_le_α hα_le_b fun y hy =>
      hsupp y fun hfy => hy (by simp [hfy])
  -- Term 2: `s * ∫ r in 0..s⁻¹, A_f(r) dr = ∫ y in a..b, s * f (s * y) * logPrimCore f y`
  have hTerm2 : s * ∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r =
      ∫ y in a..b, s * (f (s * y) * logPrimCore f y) := by
    rw [intervalIntegral_zero_dilationAutocorr_eq_integral_mul_primCore hf hα hαβ hsupp hsinv.le]
    have hcont2 : Continuous fun z => f z * (primCore f (s⁻¹ * z) / z) := by
      have h_eq : (fun z => f z * (primCore f (s⁻¹ * z) / z)) =
          fun z => f z * (s⁻¹ * logPrimCore f (s⁻¹ * z)) := by
        funext z
        simp only [logPrimCore]
        have : s⁻¹ ≠ 0 := hsinv.ne'
        field_simp
      rw [h_eq]
      exact hf.mul (continuous_const.mul (hg_cont.comp (continuous_const.mul continuous_id)))
    have h_ext := intervalIntegral_eq_of_support_subset hcont2 hsa_le_α hβ_le_sb fun z hz =>
      hsupp z fun hfz => hz (by simp [hfz])
    rw [← h_ext]
    have h_comp := intervalIntegral.integral_comp_mul_left (a := a) (b := b)
      (fun z => f z * (primCore f (s⁻¹ * z) / z)) hs.ne'
    simp only [smul_eq_mul] at h_comp
    have h_int_eq : ∫ y in a..b, s * (f (s * y) * (primCore f (s⁻¹ * (s * y)) / (s * y))) =
        ∫ y in a..b, f (s * y) * logPrimCore f y := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [logPrimCore, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
      have : s ≠ 0 := hs.ne'
      field_simp
    have h_haar : ∫ z in s * a..s * b, f z * (primCore f (s⁻¹ * z) / z) =
        ∫ y in a..b, f (s * y) * logPrimCore f y := by
      rw [← h_int_eq, intervalIntegral.integral_const_mul, h_comp,
        ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    rw [h_haar, intervalIntegral.integral_const_mul]
  -- Term 3: `s * A_{logPrimCore f}(s) = ∫ y in a..b, s * (logPrimCore f y * logPrimCore f (s * y))`
  have hTerm3 : s * dilationAutocorr (logPrimCore f) s =
      ∫ y in a..b, s * (logPrimCore f y * logPrimCore f (s * y)) := by
    rw [dilationAutocorr_eq_intervalIntegral hg_cont hα hαβ hg_supp s]
    have hcont3 : Continuous fun y => logPrimCore f y * logPrimCore f (s * y) :=
      hg_cont.mul (hg_cont.comp (continuous_const.mul continuous_id))
    have h_ext := intervalIntegral_eq_of_support_subset hcont3 ha_le_α hα_le_b fun y hy =>
      hg_supp y fun hgy => hy (by simp [hgy])
    rw [← h_ext, intervalIntegral.integral_const_mul]
  -- Fundamental Theorem of Calculus on `H(y) = primCore f y * primCore f (s * y) / y` over `a..b`
  rw [hTerm1, hTerm2, hTerm3]
  set H : ℝ → ℝ := fun y => primCore f y * primCore f (s * y) / y with hH
  set k1 : ℝ → ℝ := fun y => f y * (primCore f (s * y) / y) with hk1
  set k2 : ℝ → ℝ := fun y => s * (f (s * y) * logPrimCore f y) with hk2
  set k3 : ℝ → ℝ := fun y => s * (logPrimCore f y * logPrimCore f (s * y)) with hk3
  have hy_pos : ∀ y ∈ uIcc a b, 0 < y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha_pos hy.1
  have hy_ne : ∀ y ∈ uIcc a b, y ≠ 0 := fun y hy => (hy_pos y hy).ne'
  have hk1_cont : ContinuousOn k1 (uIcc a b) :=
    hf.continuousOn.mul (((hF_cont.comp (continuous_const.mul continuous_id)).continuousOn).div
      continuousOn_id hy_ne)
  have hk2_cont : ContinuousOn k2 (uIcc a b) :=
    continuousOn_const.mul ((hf.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hg_cont.continuousOn)
  have hk3_cont : ContinuousOn k3 (uIcc a b) :=
    continuousOn_const.mul (hg_cont.continuousOn.mul
      (hg_cont.comp (continuous_const.mul continuous_id)).continuousOn)
  have hi1 : IntervalIntegrable k1 volume a b := hk1_cont.intervalIntegrable
  have hi2 : IntervalIntegrable k2 volume a b := hk2_cont.intervalIntegrable
  have hi3 : IntervalIntegrable k3 volume a b := hk3_cont.intervalIntegrable
  have hderiv : ∀ y ∈ uIcc a b, HasDerivAt H (k1 y + k2 y - k3 y) y := by
    intro y hy
    have hy0 : 0 < y := hy_pos y hy
    have hdF1 : HasDerivAt (primCore f) (f y) y := hasDerivAt_primCore hf y
    have hd_sy : HasDerivAt (fun z : ℝ => s * z) (s * 1) y := (hasDerivAt_id y).const_mul s
    have hdF2 : HasDerivAt (fun z : ℝ => primCore f (s * z)) (f (s * y) * (s * 1)) y :=
      (hasDerivAt_primCore hf (s * y)).comp y hd_sy
    have hdH := (hdF1.mul hdF2).div (hasDerivAt_id y) hy0.ne'
    have h_eq : k1 y + k2 y - k3 y =
        ((f y * primCore f (s * y) + primCore f y * (f (s * y) * (s * 1))) * y -
          primCore f y * primCore f (s * y) * 1) / y ^ 2 := by
      have : y ≠ 0 := hy0.ne'
      have : s ≠ 0 := hs.ne'
      change f y * (primCore f (s * y) / y) + s * (f (s * y) * (primCore f y / y)) -
        s * ((primCore f y / y) * (primCore f (s * y) / (s * y))) = _
      field_simp
    rwa [h_eq]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((hi1.add hi2).sub hi3)
  rw [intervalIntegral.integral_sub (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2] at hFTC
  have hHa : H a = 0 := by
    simp only [hH, primCore_eq_zero_of_le hα hsupp ha_le_α, zero_mul, zero_div]
  have hHb : H b = 0 := by
    simp only [hH, primCore_eq_zero_of_ge hf hα hαβ hsupp hmean hα_le_b, zero_mul, zero_div]
  linarith

/-! ### Global and disjoint-preimage bounds on cumulative autocorrelations -/

/-- **Global cumulative autocorrelation bound.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`
and any `s > 0`,
`|(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr)| ≤ 2 √s ∫ r in 0..1, A_f(r) dr`. -/
theorem abs_intervalIntegral_dilationAutocorr_add_inv_le (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) :
    |(∫ r in (0 : ℝ)..s, dilationAutocorr f r) +
      s * (∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r)| ≤
      2 * Real.sqrt s * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  rw [intervalIntegral_dilationAutocorr_add_inv_eq hf hα hαβ hsupp hmean hs,
    abs_mul, abs_of_pos hs]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hCS := sqrt_mul_abs_dilationAutocorr_le hg_cont hα hg_supp hs
  rw [dilationAutocorr_logPrimCore_one_eq hf hα hαβ hsupp hmean] at hCS
  have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h_mul := mul_le_mul_of_nonneg_left hCS hsqrt_pos.le
  have h_sq : Real.sqrt s * (Real.sqrt s * |dilationAutocorr (logPrimCore f) s|) =
      s * |dilationAutocorr (logPrimCore f) s| := by
    rw [← mul_assoc, Real.mul_self_sqrt hs.le]
  linarith

/-- **Disjoint-preimage cumulative autocorrelation halving bound (`β ≤ s² α`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
and `s > 0` satisfies `β ≤ s² α`, then
`|(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr)| ≤ √s ∫ r in 0..1, A_f(r) dr`. -/
theorem abs_intervalIntegral_dilationAutocorr_add_inv_le_of_le_sq_mul (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) (hβ : β ≤ s ^ 2 * α) :
    |(∫ r in (0 : ℝ)..s, dilationAutocorr f r) +
      s * (∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r)| ≤
      Real.sqrt s * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  rw [intervalIntegral_dilationAutocorr_add_inv_eq hf hα hαβ hsupp hmean hs,
    abs_mul, abs_of_pos hs]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hCS := sqrt_mul_abs_dilationAutocorr_le_half_of_le_sq_mul hg_cont hα hg_supp hs hβ
  rw [dilationAutocorr_logPrimCore_one_eq hf hα hαβ hsupp hmean] at hCS
  have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h_mul := mul_le_mul_of_nonneg_left hCS hsqrt_pos.le
  have h_sq : Real.sqrt s * (Real.sqrt s * |dilationAutocorr (logPrimCore f) s|) =
      s * |dilationAutocorr (logPrimCore f) s| := by
    rw [← mul_assoc, Real.mul_self_sqrt hs.le]
  linarith

/-- **Symmetric disjoint-preimage cumulative autocorrelation halving bound (`s² β ≤ α`).**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
and `s > 0` satisfies `s² β ≤ α`, then
`|(∫ r in 0..s, A_f(r) dr) + s * (∫ r in 0..s⁻¹, A_f(r) dr)| ≤ √s ∫ r in 0..1, A_f(r) dr`. -/
theorem abs_intervalIntegral_dilationAutocorr_add_inv_le_of_sq_mul_le (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℝ} (hs : 0 < s) (hβ : s ^ 2 * β ≤ α) :
    |(∫ r in (0 : ℝ)..s, dilationAutocorr f r) +
      s * (∫ r in (0 : ℝ)..s⁻¹, dilationAutocorr f r)| ≤
      Real.sqrt s * ∫ r in (0 : ℝ)..1, dilationAutocorr f r := by
  rw [intervalIntegral_dilationAutocorr_add_inv_eq hf hα hαβ hsupp hmean hs,
    abs_mul, abs_of_pos hs]
  have hg_cont : Continuous (logPrimCore f) := continuous_logPrimCore hf hα hsupp
  have hg_supp := logPrimCore_support hf hα hαβ hsupp hmean
  have hCS := sqrt_mul_abs_dilationAutocorr_le_half_of_sq_mul_le hg_cont hα hg_supp hs hβ
  rw [dilationAutocorr_logPrimCore_one_eq hf hα hαβ hsupp hmean] at hCS
  have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h_mul := mul_le_mul_of_nonneg_left hCS hsqrt_pos.le
  have h_sq : Real.sqrt s * (Real.sqrt s * |dilationAutocorr (logPrimCore f) s|) =
      s * |dilationAutocorr (logPrimCore f) s| := by
    rw [← mul_assoc, Real.mul_self_sqrt hs.le]
  linarith

end

end RHTower
