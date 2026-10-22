import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCenteredEnergy
import GaloisForLFunctions.RHTower.PMDilationMellin
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping

/-!
# Centering and stable inversion of an arithmetic Fermi source

An absolutely convergent arithmetic mean determines the boundary condition for
dyadic inversion. The inverse has norm at most `1 + sqrt 2`; this transfers
critical admission without taking absolute values of the arithmetic coefficients.
-/

open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

namespace RHTower

/-- The finite floor response, expressed as a total sum. -/
def dilationFloorSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' d : ℕ, a d * (⌊x / (d : ℝ)⌋₊ : ℂ)

/-- The arithmetic mean is removed before the critical norm is taken. -/
def dilationCenteredSource (a : ℕ → ℂ) (m : ℂ) (t : ℝ) : ℂ :=
  dilationFloorSum a (1 / t) - m / (t : ℂ)

/-- The alternating dilation response of an arithmetic row. -/
def dilationFermiSource (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  -pmWeightedDilationSource a (fermiNymanGen 1) t

theorem measurable_dilationFloorSum (a : ℕ → ℂ) : Measurable (dilationFloorSum a) := by
  apply Measurable.tsum
  intro d
  fun_prop

theorem measurable_dilationCenteredSource (a : ℕ → ℂ) (m : ℂ) :
    Measurable (dilationCenteredSource a m) := by
  exact ((measurable_dilationFloorSum a).comp (measurable_const.div measurable_id)).sub
    (measurable_const.div Complex.measurable_ofReal)

theorem measurable_dilationFermiSource (a : ℕ → ℂ) : Measurable (dilationFermiSource a) := by
  apply Measurable.neg
  exact Measurable.tsum fun n => measurable_const.mul
    ((measurable_fermiNymanGen 1).comp (measurable_const.mul measurable_id))

theorem dilationFloorTerm_eq_zero_of_not_mem_range (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    {d : ℕ} (hd : d ∉ Finset.range (⌊x⌋₊ + 1)) : a d * (⌊x / (d : ℝ)⌋₊ : ℂ) = 0 := by
  have hgt : ⌊x⌋₊ < d := by
    simp only [Finset.mem_range, not_lt] at hd
    omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hxd : x / (d : ℝ) < 1 := (div_lt_one hd0).mpr ((Nat.floor_lt hx).mp hgt)
  simp [Nat.floor_eq_zero.mpr hxd]

theorem summable_dilationFloorTerm (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun d : ℕ => a d * (⌊x / (d : ℝ)⌋₊ : ℂ)) :=
  summable_of_ne_finset_zero fun _ hd => dilationFloorTerm_eq_zero_of_not_mem_range a hx hd

theorem dilationFloorSum_eq_sum (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    dilationFloorSum a x = ∑ d ∈ Finset.range (⌊x⌋₊ + 1), a d * (⌊x / (d : ℝ)⌋₊ : ℂ) :=
  tsum_eq_sum fun _ hd => dilationFloorTerm_eq_zero_of_not_mem_range a hx hd

/-- The normalized floor response converges to its absolutely convergent mean. -/
theorem tendsto_dilationFloorSum_div {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ))) :
    Tendsto (fun x : ℝ => dilationFloorSum a x / (x : ℂ)) atTop
      (𝓝 (∑' d : ℕ, a d / (d : ℂ))) := by
  let F := fun (x : ℝ) (d : ℕ) => a d *
    ((((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x : ℝ) : ℂ)
  let b := fun d : ℕ => a d / (d : ℂ)
  have hlim (d : ℕ) : Tendsto (fun x => F x d) atTop (𝓝 (b d)) := by
    have he (x : ℝ) : (1 / (d : ℝ)) * x = x / (d : ℝ) := by ring
    have hfloor : Tendsto (fun x : ℝ => ((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) atTop
        (𝓝 (1 / (d : ℝ))) := by
      simpa only [he] using tendsto_nat_floor_mul_div_atTop (a := 1 / (d : ℝ)) (by positivity)
    have h := ((Complex.continuous_ofReal.tendsto (1 / (d : ℝ))).comp hfloor).const_mul (a d)
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, mul_one_div, F, b] using h
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ d : ℕ, ‖F x d‖ ≤ ‖b d‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [F, b]
    · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have hn0 : 0 ≤ (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) := by positivity
      have hn1 : (((⌊x / (d : ℝ)⌋₊ : ℕ) : ℝ) / x) ≤ 1 / (d : ℝ) := by
        rw [div_le_iff₀ hx, show (1 / (d : ℝ)) * x = x / (d : ℝ) by ring]
        exact Nat.floor_le (div_nonneg hx.le hdpos.le)
      dsimp only [F, b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0,
        norm_div, Complex.norm_natCast]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hn1 (norm_nonneg (a d))
  have h := tendsto_tsum_of_dominated_convergence ha.norm hlim hbound
  convert h using 1
  funext x
  rw [dilationFloorSum, ← tsum_div_const]
  apply tsum_congr
  intro d
  dsimp only [F]
  push_cast
  ring

/-- Mean centering cancels exactly in the dyadic Fermi difference. -/
theorem dilationFermiSource_eq_centered_difference (a : ℕ → ℂ) (m : ℂ)
    {t : ℝ} (ht : 0 < t) :
    dilationFermiSource a t = dilationCenteredSource a m t -
      2 * dilationCenteredSource a m (2 * t) := by
  have hterm (d : ℕ) : -(a d * fermiNymanGen 1 ((d : ℝ) * t)) =
      a d * (⌊(1 / t) / (d : ℝ)⌋₊ : ℂ) -
        2 * (a d * (⌊(1 / (2 * t)) / (d : ℝ)⌋₊ : ℂ)) := by
    rw [← pm_fermiNymanGen_dilate, fermiNymanGen_eq_floor_difference]
    rw [← Int.natCast_floor_eq_floor (by positivity : 0 ≤ (1 / (2 * t)) / (d : ℝ)),
      ← Int.natCast_floor_eq_floor (by positivity : 0 ≤ (1 / t) / (d : ℝ))]
    push_cast
    ring
  have hs := summable_dilationFloorTerm a (by positivity : 0 ≤ 1 / t)
  have hs2 := summable_dilationFloorTerm a (by positivity : 0 ≤ 1 / (2 * t))
  rw [dilationFermiSource, pmWeightedDilationSource, ← tsum_neg, tsum_congr hterm,
    hs.tsum_sub (hs2.mul_left 2), tsum_mul_left]
  dsimp only [dilationCenteredSource, dilationFloorSum]
  push_cast
  ring

/-- The arithmetic mean supplies the vanishing boundary term for backward inversion. -/
theorem tendsto_dilationCenteredSource_dyadic_boundary {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ))) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ))
      (t / (2 : ℝ) ^ N) / (2 : ℂ) ^ N) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ => (2 : ℝ) ^ N / t) atTop atTop :=
    (tendsto_div_const_atTop_of_pos ht).mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h := (((tendsto_dilationFloorSum_div ha).sub_const
    (∑' d : ℕ, a d / (d : ℂ))).comp hx).div_const (t : ℂ)
  simp only [sub_self, zero_div] at h
  convert h using 1
  funext N
  dsimp only [Function.comp_def, dilationCenteredSource]
  rw [one_div_div]
  push_cast
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  field_simp

theorem dilationCenteredSource_dyadic_telescope (a : ℕ → ℂ) (m : ℂ)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    dilationCenteredSource a m t = dilationCenteredSource a m (t / (2 : ℝ) ^ N) /
      (2 : ℂ) ^ N - ∑ k ∈ Finset.range N,
        dilationFermiSource a (t / (2 : ℝ) ^ (k + 1)) / (2 : ℂ) ^ (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep := dilationFermiSource_eq_centered_difference a m
      (div_pos ht (by positivity : (0 : ℝ) < 2 ^ (N + 1)))
    have harg : 2 * (t / (2 : ℝ) ^ (N + 1)) = t / (2 : ℝ) ^ N := by
      rw [pow_succ]
      field_simp
    rw [harg] at hstep
    rw [Finset.sum_range_succ, ih, hstep, pow_succ]
    field_simp
    ring

theorem tendsto_dilationCenteredSource_dyadic_sum {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ))) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmBackwardDyadicPrefix (dilationFermiSource a) N t) atTop
      (𝓝 (dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ)) t)) := by
  have hc : Tendsto (fun _ : ℕ => dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ)) t)
      atTop (𝓝 (dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ)) t)) := tendsto_const_nhds
  have h := hc.sub (tendsto_dilationCenteredSource_dyadic_boundary ha ht)
  simp only [sub_zero] at h
  convert h using 1
  funext N
  rw [dilationCenteredSource_dyadic_telescope a _ ht N]
  simp only [pmBackwardDyadicPrefix, pmBackwardDilation, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- Stable inversion transfers the physical Fermi budget to the mean-centered source. -/
theorem dilationCenteredSource_norm_le {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ)))
    (hf : MemLp (dilationFermiSource a) 2 (volume.restrict (Ioi 0))) :
    eLpNorm (dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ))) 2
      (volume.restrict (Ioi 0)) ≤
        ENNReal.ofReal ((1 + Real.sqrt 2) * lpNorm (dilationFermiSource a) 2
          (volume.restrict (Ioi 0))) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ))
    (Eventually.of_forall fun N => pmBackwardDyadicPrefix_norm_le
      (measurable_dilationFermiSource a) hf N)
    (fun N => (memLp_pmBackwardDyadicPrefix (measurable_dilationFermiSource a) hf N
      ).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tendsto_dilationCenteredSource_dyadic_sum ha ht

theorem memLp_dilationCenteredSource {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ)))
    (hf : MemLp (dilationFermiSource a) 2 (volume.restrict (Ioi 0))) :
    MemLp (dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ))) 2
      (volume.restrict (Ioi 0)) :=
  ⟨(measurable_dilationCenteredSource a _).aestronglyMeasurable,
    (dilationCenteredSource_norm_le ha hf).trans_lt ENNReal.ofReal_lt_top⟩

/-- The square-mass form of stable backward inversion. -/
theorem dilationCenteredSource_mass_le {a : ℕ → ℂ}
    (ha : Summable (fun d : ℕ => a d / (d : ℂ)))
    (hf : MemLp (dilationFermiSource a) 2 (volume.restrict (Ioi 0))) :
    (∫ t in Ioi (0 : ℝ), ‖dilationCenteredSource a (∑' d : ℕ, a d / (d : ℂ)) t‖ ^ 2) ≤
      (1 + Real.sqrt 2) ^ 2 * ∫ t in Ioi (0 : ℝ), ‖dilationFermiSource a t‖ ^ 2 := by
  have hc := memLp_dilationCenteredSource ha hf
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (dilationCenteredSource_norm_le ha hf)
  rw [toReal_eLpNorm hc.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by positivity)] at hn
  rw [pm_integral_norm_sq_toLp hc, pm_integral_norm_sq_toLp hf,
    Lp.norm_toLp, Lp.norm_toLp, toReal_eLpNorm hc.aestronglyMeasurable,
    toReal_eLpNorm hf.aestronglyMeasurable]
  calc
    _ ≤ ((1 + Real.sqrt 2) * lpNorm (dilationFermiSource a) 2
        (volume.restrict (Ioi 0))) ^ 2 := by gcongr
    _ = _ := by ring

theorem dilationFloorSum_eq_zero_of_lt_one (a : ℕ → ℂ) {x : ℝ} (hx : x < 1) :
    dilationFloorSum a x = 0 := by
  rw [dilationFloorSum]
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro d
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        simp only [Nat.floor_eq_zero.mpr ((div_lt_one hd0).mpr (hx.trans_le hd1)),
          Nat.cast_zero, mul_zero]
    _ = 0 := tsum_zero

/-- The arithmetic mean is visible as the exact tail of the centered source. -/
theorem dilationCenteredSource_eq_neg_mean_div (a : ℕ → ℂ) (m : ℂ)
    {t : ℝ} (ht : 1 < t) : dilationCenteredSource a m t = -m / (t : ℂ) := by
  rw [dilationCenteredSource, dilationFloorSum_eq_zero_of_lt_one a
    ((div_lt_one (zero_lt_one.trans ht)).mpr ht), zero_sub, neg_div]

/-! ## Integer cells and the centering correction -/

theorem dilationFloorSum_ofReal (c : ℕ → ℝ) (x : ℝ) :
    dilationFloorSum (fun d => (c d : ℂ)) x =
      ((∑ j ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ j.divisors, c d : ℝ) : ℂ) := by
  rw [dilationFloorSum, sum_Icc_sum_divisors_eq_floor]
  push_cast
  simp_rw [Nat.floor_div_natCast]
  apply tsum_eq_sum
  intro d hd
  have hd' : d = 0 ∨ ⌊x⌋₊ < d := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hd
    omega
  rcases hd' with rfl | hd'
  · simp
  · simp [Nat.div_eq_of_lt hd']

/-- The fractional-part term is the exact difference between real and integer centering. -/
theorem dilationCenteredSource_ofReal (c : ℕ → ℝ) (m : ℝ) {t : ℝ} (ht : 0 < t) :
    dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ) t =
      (weightCenteredPrefix c m ⌊1 / t⌋₊ : ℂ) -
        (m : ℂ) * ((Int.fract (1 / t) : ℝ) : ℂ) := by
  have hfract : (⌊1 / t⌋₊ : ℝ) + Int.fract (1 / t) = 1 / t := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor (by positivity : 0 ≤ 1 / t)]
    push_cast
    ring
  have hfractC := congrArg (fun y : ℝ => (y : ℂ)) hfract
  push_cast at hfractC
  rw [dilationCenteredSource, dilationFloorSum_ofReal, weightCenteredPrefix]
  push_cast
  rw [show (m : ℂ) / (t : ℂ) = (m : ℂ) * (1 / (t : ℂ)) by ring, ← hfractC]
  ring

/-- Reciprocal transport sends the centered source to the pronic step function,
with its bounded fractional-part correction retained. -/
theorem stepFun_eq_centeredSource_add_fract (c : ℕ → ℝ) (m : ℝ)
    {x : ℝ} (hx : 0 < x) :
    stepFun (weightCenteredPrefix c m) x =
      dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ) (1 / x) / (x : ℂ) +
        (m : ℂ) * (((Int.fract x : ℝ) : ℂ) / (x : ℂ)) := by
  rw [dilationCenteredSource_ofReal c m (one_div_pos.mpr hx), one_div_one_div, stepFun]
  ring

/-- Reciprocal half-density preserves the full square mass. -/
theorem integral_norm_sq_reciprocal_halfDensity (f : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), ‖f (1 / x) / (x : ℂ)‖ ^ (2 : ℕ)) =
      ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ (2 : ℕ) := by
  simp_rw [pm_norm_div_real_sq]
  have h := pm_integral_normSq_reciprocal (fun x => f (1 / x))
  simpa only [one_div_one_div] using h.symm

theorem memLp_reciprocal_halfDensity {f : ℝ → ℂ} (hm : Measurable f)
    (hf : MemLp f 2 (volume.restrict (Ioi 0))) :
    MemLp (fun x => f (1 / x) / (x : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  have hm' : Measurable (fun x => f (1 / x) / (x : ℂ)) :=
    (hm.comp (measurable_const.div measurable_id)).div Complex.measurable_ofReal
  rw [memLp_two_iff_integrable_sq_norm hm'.aestronglyMeasurable]
  have hbase : IntegrableOn (fun t => ‖(fun x => f (1 / x)) (1 / t)‖ ^ (2 : ℕ)) (Ioi 0) := by
    simpa only [one_div_one_div] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have h := (pm_integrable_normSq_reciprocal_iff (fun x => f (1 / x))).mp hbase
  simpa only [pm_norm_div_real_sq] using h

/-- The mean occupies exactly the unit reciprocal-square tail. -/
theorem integral_norm_sq_dilationCenteredSource_tail (a : ℕ → ℂ) (m : ℂ) :
    (∫ t in Ioi (1 : ℝ), ‖dilationCenteredSource a m t‖ ^ 2) = ‖m‖ ^ 2 := by
  calc
    _ = ∫ t in Ioi (1 : ℝ), ‖m‖ ^ 2 * t ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [dilationCenteredSource_eq_neg_mean_div a m ht, norm_div, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans ht),
        div_pow, div_eq_mul_inv, ← inv_pow, inv_sq_eq_rpow (zero_lt_one.trans ht)]
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
      norm_num

theorem norm_mean_sq_le_dilationCenteredSource_mass {a : ℕ → ℂ} {m : ℂ}
    (hc : MemLp (dilationCenteredSource a m) 2 (volume.restrict (Ioi 0))) :
    ‖m‖ ^ 2 ≤ ∫ t in Ioi (0 : ℝ), ‖dilationCenteredSource a m t‖ ^ 2 := by
  rw [← integral_norm_sq_dilationCenteredSource_tail a m]
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp hc)
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun _ ht => zero_lt_one.trans ht)

theorem memLp_stepFun_of_dilationCenteredSource {c : ℕ → ℝ} {m : ℝ}
    (hc : MemLp (dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ)) 2
      (volume.restrict (Ioi 0))) :
    MemLp (stepFun (weightCenteredPrefix c m)) 2 bdMeasure := by
  have hr := memLp_reciprocal_halfDensity (measurable_dilationCenteredSource _ _) hc
  have hrt := MemLp.mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi.mpr zero_le_one) le_rfl) hr
  have h := hrt.add (memLp_fract_div_bdMeasure.const_mul (m : ℂ))
  apply (memLp_congr_ae ?_).mp h
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (stepFun_eq_centeredSource_add_fract c m (zero_lt_one.trans hx)).symm

private theorem norm_add_sq_le_twice (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    gcongr
    exact norm_add_le z w
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem integral_norm_sq_fract_div_le_one :
    (∫ x in Ioi (1 : ℝ), ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ)‖ ^ 2) ≤ 1 := by
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ), x ^ (-2 : ℝ) := by
      apply integral_mono_ae
        ((memLp_two_iff_integrable_sq_norm
          memLp_fract_div_bdMeasure.aestronglyMeasurable).mp memLp_fract_div_bdMeasure)
        (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 := zero_lt_one.trans hx
      rw [pm_norm_div_real_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        ← inv_sq_eq_rpow hx0, div_eq_mul_inv, ← inv_pow]
      have hfract : Int.fract x ^ 2 ≤ 1 := by
        nlinarith [Int.fract_nonneg x, Int.fract_lt_one x]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfract (sq_nonneg (x⁻¹))
    _ = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
      norm_num

/-- Both reciprocal transport and integer centering are paid by the full centered mass. -/
theorem integral_norm_sq_stepFun_le_dilationCenteredSource_mass {c : ℕ → ℝ} {m : ℝ}
    (hc : MemLp (dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ)) 2
      (volume.restrict (Ioi 0))) :
    (∫ x in Ioi (1 : ℝ), ‖stepFun (weightCenteredPrefix c m) x‖ ^ 2) ≤
      4 * ∫ t in Ioi (0 : ℝ),
        ‖dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ) t‖ ^ 2 := by
  let C := dilationCenteredSource (fun d => (c d : ℂ)) (m : ℂ)
  let f := fun x : ℝ => C (1 / x) / (x : ℂ)
  let g := fun x : ℝ => (m : ℂ) * (((Int.fract x : ℝ) : ℂ) / (x : ℂ))
  have hf := memLp_reciprocal_halfDensity (measurable_dilationCenteredSource _ _) hc
  have hfi : IntegrableOn (fun x => ‖f x‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hfit := hfi.mono_set (Ioi_subset_Ioi.mpr zero_le_one)
  have hg : MemLp g 2 bdMeasure := memLp_fract_div_bdMeasure.const_mul (m : ℂ)
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hs := memLp_stepFun_of_dilationCenteredSource hc
  have hsi := (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  have hb : (∫ x in Ioi (1 : ℝ), ‖stepFun (weightCenteredPrefix c m) x‖ ^ 2) ≤
      ∫ x in Ioi (1 : ℝ), 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
    apply integral_mono_ae hsi ((hfit.const_mul 2).add (hgi.const_mul 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [stepFun_eq_centeredSource_add_fract c m (zero_lt_one.trans hx)]
    exact norm_add_sq_le_twice (f x) (g x)
  rw [integral_add (hfit.const_mul 2) (hgi.const_mul 2),
    integral_const_mul, integral_const_mul] at hb
  have hfm : (∫ x in Ioi (1 : ℝ), ‖f x‖ ^ 2) ≤
      ∫ t in Ioi (0 : ℝ), ‖C t‖ ^ 2 := by
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := setIntegral_mono_set hfi
        (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ hx => zero_lt_one.trans hx)
      _ = _ := integral_norm_sq_reciprocal_halfDensity C
  have hgm : (∫ x in Ioi (1 : ℝ), ‖g x‖ ^ 2) ≤ m ^ 2 := by
    have he : (∫ x in Ioi (1 : ℝ), ‖g x‖ ^ 2) =
        m ^ 2 * ∫ x in Ioi (1 : ℝ), ‖((Int.fract x : ℝ) : ℂ) / (x : ℂ)‖ ^ 2 := by
      simp only [g, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact integral_const_mul _ _
    rw [he]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      integral_norm_sq_fract_div_le_one (sq_nonneg m)
  have hmm : m ^ 2 ≤ ∫ t in Ioi (0 : ℝ), ‖C t‖ ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      norm_mean_sq_le_dilationCenteredSource_mass hc
  change _ ≤ 4 * ∫ t in Ioi (0 : ℝ), ‖C t‖ ^ 2
  linarith

theorem hasSum_norm_sq_stepFun {s : ℕ → ℝ} (hs : MemLp (stepFun s) 2 bdMeasure) :
    HasSum (fun n : ℕ => s (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (∫ x in Ioi (1 : ℝ), ‖stepFun s x‖ ^ 2) := by
  have he : (fun x : ℝ => ‖stepFun s x‖ ^ 2) =
      fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2 := by
    funext x
    simp only [stepFun, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, inv_pow, sq_abs, sq_abs, inv_pow, sq]
  have hi : IntegrableOn (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2) (Ioi 1) := by
    rw [← he]
    exact (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  have hu : IntegrableOn (fun x : ℝ => s ⌊x⌋₊ * s ⌊x⌋₊ * (x⁻¹) ^ 2)
      (⋃ n : ℕ, tailCell n) := by simpa only [iUnion_tailCell] using hi
  have h := hasSum_integral_iUnion measurableSet_tailCell pairwise_disjoint_tailCell hu
  rw [iUnion_tailCell] at h
  simp_rw [integral_tailCell_stepGramIntegrand] at h
  rw [he]
  simpa only [sq] using h

theorem weightPronicEnergy_le_stepFun_mass (c : ℕ → ℝ) (m : ℝ)
    (hs : MemLp (stepFun (weightCenteredPrefix c m)) 2 bdMeasure) (T : ℕ) :
    weightPronicEnergy c m T ≤
      ∫ x in Ioi (1 : ℝ), ‖stepFun (weightCenteredPrefix c m) x‖ ^ 2 := by
  have he (N : ℕ) : weightPronicEnergy c m N =
      ∑ n ∈ Finset.range N, weightCenteredPrefix c m (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    induction N with
    | zero => simp [weightPronicEnergy]
    | succ N ih =>
      rw [weightPronicEnergy, Finset.sum_Icc_succ_top (by omega),
        ← weightPronicEnergy, ih, Finset.sum_range_succ]
      congr 1
      push_cast
      ring
  rw [he]
  have hh := hasSum_norm_sq_stepFun hs
  rw [← hh.tsum_eq]
  exact hh.summable.sum_le_tsum _ (fun _ _ => by positivity)

/-- Stable inversion pays every finite pronic receiver directly from the literal Fermi mass. -/
theorem weightPronicEnergy_le_dilationFermiSource_mass {c : ℕ → ℝ}
    (hc : Summable (fun d : ℕ => c d / (d : ℝ)))
    (hf : MemLp (dilationFermiSource (fun d => (c d : ℂ))) 2
      (volume.restrict (Ioi 0))) (T : ℕ) :
    weightPronicEnergy c (∑' d : ℕ, c d / (d : ℝ)) T ≤
      (4 * (1 + Real.sqrt 2) ^ 2) *
        ∫ t in Ioi (0 : ℝ), ‖dilationFermiSource (fun d => (c d : ℂ)) t‖ ^ 2 := by
  have hcC : Summable (fun d : ℕ => (c d : ℂ) / (d : ℂ)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      (Complex.summable_ofReal.mpr hc)
  have hm : (∑' d : ℕ, (c d : ℂ) / (d : ℂ)) =
      ((∑' d : ℕ, c d / (d : ℝ) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_natCast]
  have hC := memLp_dilationCenteredSource hcC hf
  have hmass := dilationCenteredSource_mass_le hcC hf
  rw [hm] at hC hmass
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ),
        ‖stepFun (weightCenteredPrefix c (∑' d : ℕ, c d / (d : ℝ))) x‖ ^ 2 :=
      weightPronicEnergy_le_stepFun_mass c _ (memLp_stepFun_of_dilationCenteredSource hC) T
    _ ≤ 4 * ∫ t in Ioi (0 : ℝ),
        ‖dilationCenteredSource (fun d => (c d : ℂ))
          ((∑' d : ℕ, c d / (d : ℝ) : ℝ) : ℂ) t‖ ^ 2 :=
      integral_norm_sq_stepFun_le_dilationCenteredSource_mass hC
    _ ≤ _ := by nlinarith

end RHTower
