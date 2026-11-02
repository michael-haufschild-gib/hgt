import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.IntrinsicWeilTraceAndWindowCorollaries
import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadCoherentQuantileGammaNoGo

/-!
# The explicit tent form vector

The tent `τ_a(x) = (1 - |x|/a)⁺` (`HTGeometry.triangleFn a`) is an `H¹₀((-a, a))` profile whose
data are all explicit: `∫ τ_a = a`, `∫ τ_a² = 2a/3`, and `𝓕 τ_a (ξ) = a sinc(π a ξ)²`.

The exact archimedean form weight satisfies the global bound
`ccmArchimedeanFormWeight ξ ≤ 75 + ξ²/2` (from `-3 ≤ θ'(0)` and the uniform digamma estimate).
With `s = sinc(π a ξ)²` one has `s ≤ 1` and `s (π a ξ)² = sin² ≤ 1`, so the weighted Fourier
density of `τ_a` is at most `(150 a² + 1/π²) / (1 + (π a ξ)²)`, whose integral is
`150 a + 1/(π² a)`. Hence `τ_a` belongs to the archimedean form domain at aperture `a`, with form
norm `‖u_a‖² ≤ 150 a + 1/(π² a)`, `L²` norm `‖τ_a‖² = 2a/3`, and polar moments
`∫ e^{s x} τ_a ≥ e^{-|s| a} a`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace Real
open _root_.RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-! ## The archimedean weight is at most quadratic -/

/-- `θ'(0) = -(3 log 2 + γ + π/2)/2 - (log π)/2 ≥ -3`. -/
theorem neg_three_le_gammaHardyPhaseRate_zero : -3 ≤ gammaHardyPhaseRate 0 := by
  rw [gammaHardyPhaseRate_zero_closed]
  have hlog2 := Real.log_two_lt_d9
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d2
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogπ : Real.log Real.pi < Real.log 4 :=
    Real.log_lt_log Real.pi_pos (by linarith)
  norm_num at hlog2 hπ
  linarith

/-- Global quadratic majorant of the exact archimedean form weight. -/
theorem ccmArchimedeanFormWeight_le_quadratic (ξ : ℝ) :
    ccmArchimedeanFormWeight ξ ≤ 75 + ξ ^ 2 / 2 := by
  have h0 := neg_three_le_gammaHardyPhaseRate_zero
  by_cases hξ : |ξ| ≤ 1
  · have hmono := ccmArchimedeanFourierWeight.monotoneOn_nonneg
      (Set.mem_Ici.mpr (abs_nonneg ξ)) (Set.mem_Ici.mpr zero_le_one) hξ
    have hmono' : ccmArchimedeanFormWeight ξ ≤ ccmArchimedeanFormWeight 1 := by
      simpa [ccmArchimedeanFourierWeight, ccmArchimedeanFormWeight] using hmono
    have hp := gammaHardyPhaseRate_log_abs_le_thirtyFour (r := (1 : ℝ)) le_rfl
    simp only [mul_one, Real.log_one, zero_div, sub_zero, abs_le] at hp
    have hone : ccmArchimedeanFormWeight 1 ≤ 75 := by
      unfold ccmArchimedeanFormWeight
      simp only [abs_one, mul_one]
      linarith [hp.2]
    nlinarith [sq_nonneg ξ]
  · have hr : 1 ≤ |ξ| := (lt_of_not_ge hξ).le
    have hpu := (abs_le.mp (gammaHardyPhaseRate_log_abs_le_thirtyFour hr)).2
    have hlog : Real.log |ξ| ≤ |ξ| - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hsq : |ξ| - 1 ≤ ξ ^ 2 / 2 := by
      nlinarith [sq_abs ξ, sq_nonneg (|ξ| - 1)]
    unfold ccmArchimedeanFormWeight
    linarith

/-! ## The tent profile -/

theorem triangleFn_eq_zero_of_notMem {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ∉ Icc (-a) a) :
    triangleFn a x = 0 := by
  apply triangleFn_eq_zero ha
  by_contra h
  push Not at h
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

theorem continuous_tentProfile (a : ℝ) :
    Continuous fun x : ℝ => ((triangleFn a x : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_triangleFn a)

theorem hasCompactSupport_tentProfile {a : ℝ} (ha : 0 < a) :
    HasCompactSupport fun x : ℝ => ((triangleFn a x : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx => by
    simp [triangleFn_eq_zero_of_notMem ha hx]

theorem memLp_tentProfile {a : ℝ} (ha : 0 < a) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ => ((triangleFn a x : ℝ) : ℂ)) p volume :=
  (continuous_tentProfile a).memLp_of_hasCompactSupport (hasCompactSupport_tentProfile ha)

theorem integrable_triangleFn {a : ℝ} (ha : 0 < a) : Integrable (triangleFn a) volume :=
  (continuous_triangleFn a).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun _ hx =>
      triangleFn_eq_zero_of_notMem ha hx)

/-- A function vanishing off `[-a, a]` integrates over `ℝ` as over `[-a, a]`. -/
theorem integral_eq_intervalIntegral_of_vanish {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : 0 < a) {g : ℝ → E}
    (hg : ∀ x, x ∉ Icc (-a) a → g x = 0) :
    ∫ x, g x = ∫ x in (-a)..a, g x := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hg]

/-- `∫ τ_a = a`. -/
theorem integral_triangleFn_real {a : ℝ} (ha : 0 < a) : ∫ x, triangleFn a x = a := by
  rw [integral_eq_intervalIntegral_of_vanish ha fun x hx => triangleFn_eq_zero_of_notMem ha hx]
  have h := integral_triangleFn ha
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- `∫ τ_a² = 2a/3`. -/
theorem integral_triangleFn_sq {a : ℝ} (ha : 0 < a) : ∫ x, triangleFn a x ^ 2 = 2 * a / 3 := by
  rw [integral_eq_intervalIntegral_of_vanish ha fun x hx => by
    rw [triangleFn_eq_zero_of_notMem ha hx]; norm_num]
  have hcont : Continuous fun x : ℝ => triangleFn a x ^ 2 := (continuous_triangleFn a).pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hneg : ∀ x ∈ uIcc (-a) (0 : ℝ), triangleFn a x ^ 2 = (1 + x / a) ^ 2 := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    unfold triangleFn
    rw [abs_of_nonpos hx.2, show 1 - -x / a = 1 + x / a by ring, max_eq_left]
    have : -1 ≤ x / a := by rw [le_div_iff₀ ha]; linarith [hx.1]
    linarith
  have hpos : ∀ x ∈ uIcc (0 : ℝ) a, triangleFn a x ^ 2 = (1 - x / a) ^ 2 := by
    intro x hx
    rw [uIcc_of_le ha.le] at hx
    unfold triangleFn
    rw [abs_of_nonneg hx.1, max_eq_left]
    have : x / a ≤ 1 := by rw [div_le_iff₀ ha]; linarith [hx.2]
    linarith
  rw [intervalIntegral.integral_congr hneg, intervalIntegral.integral_congr hpos]
  have hd1 : ∀ x ∈ uIcc (-a) (0 : ℝ),
      HasDerivAt (fun x : ℝ => x + x ^ 2 / a + x ^ 3 / (3 * a ^ 2)) ((1 + x / a) ^ 2) x := by
    intro x _
    have h := ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const a)).add
      ((hasDerivAt_pow 3 x).div_const (3 * a ^ 2))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hd2 : ∀ x ∈ uIcc (0 : ℝ) a,
      HasDerivAt (fun x : ℝ => x - x ^ 2 / a + x ^ 3 / (3 * a ^ 2)) ((1 - x / a) ^ 2) x := by
    intro x _
    have h := ((hasDerivAt_id x).sub ((hasDerivAt_pow 2 x).div_const a)).add
      ((hasDerivAt_pow 3 x).div_const (3 * a ^ 2))
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd1 (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 (by
      apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring

/-- Exponential moments of the tent: `e^{-|s| a} a ≤ ∫ e^{s x} τ_a(x) dx`. -/
theorem exp_neg_abs_mul_le_tentMoment {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Real.exp (-(|s| * a)) * a ≤ ∫ x, Real.exp (s * x) * triangleFn a x := by
  have hint : Integrable (fun x => Real.exp (s * x) * triangleFn a x) volume :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_triangleFn a)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx => by
        simp [triangleFn_eq_zero_of_notMem ha hx])
  calc Real.exp (-(|s| * a)) * a = Real.exp (-(|s| * a)) * ∫ x, triangleFn a x := by
        rw [integral_triangleFn_real ha]
    _ = ∫ x, Real.exp (-(|s| * a)) * triangleFn a x := (integral_const_mul _ _).symm
    _ ≤ ∫ x, Real.exp (s * x) * triangleFn a x :=
        integral_mono ((integrable_triangleFn ha).const_mul _) hint fun x => ?_
  by_cases hx : x ∈ Icc (-a) a
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (triangleFn_nonneg a x)
    have hxa : |x| ≤ a := abs_le.mpr hx
    have h1 : -(s * x) ≤ |s| * |x| := by
      rw [← abs_mul]; exact neg_le_abs _
    nlinarith [abs_nonneg s]
  · simp [triangleFn_eq_zero_of_notMem ha hx]

/-! ## The tent as a physical aperture vector -/

/-- The tent `τ_a` as a physical `L²` vector. -/
def tentL2 (a : ℝ) (ha : 0 < a) : SoninL2 :=
  (memLp_tentProfile ha 2).toLp fun x : ℝ => ((triangleFn a x : ℝ) : ℂ)

theorem tentL2_coeFn {a : ℝ} (ha : 0 < a) :
    (tentL2 a ha : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => ((triangleFn a x : ℝ) : ℂ) :=
  (memLp_tentProfile ha 2).coeFn_toLp

theorem indicatorCutoff_tentL2 (a : SuzukiPositiveAperture) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (tentL2 a.1 a.2) = tentL2 a.1 a.2 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (tentL2 a.1 a.2), tentL2_coeFn a.2] with x hcut hvec
  rw [hcut]
  by_cases hx : x ∈ centralInterval a.1
  · simp [hx]
  · rw [Set.indicator_of_notMem hx, hvec, triangleFn_eq_zero_of_notMem a.2 hx,
      Complex.ofReal_zero]

/-- The tent `τ_a` as a vector of the physical aperture space at aperture `a`. -/
def tentApertureVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ⟨tentL2 a.1 a.2, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨tentL2 a.1 a.2, indicatorCutoff_tentL2 a⟩⟩

/-- `‖τ_a‖² = 2a/3`. -/
theorem norm_sq_tentApertureVector (a : SuzukiPositiveAperture) :
    ‖tentApertureVector a‖ ^ 2 = 2 * a.1 / 3 := by
  have hnorm : ‖tentApertureVector a‖ = ‖tentL2 a.1 a.2‖ := rfl
  have hinner : (inner ℂ (tentL2 a.1 a.2) (tentL2 a.1 a.2) : ℂ) =
      ((∫ x, triangleFn a.1 x ^ 2 : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [tentL2_coeFn a.2] with x hx
    rw [hx, RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    ring
  rw [inner_self_eq_norm_sq_to_K, integral_triangleFn_sq a.2] at hinner
  rw [hnorm]
  have hre := congrArg Complex.re hinner
  simpa [← Complex.ofReal_pow] using hre

/-- The polar coefficients of the tent are its exponential moments. -/
theorem inner_ccmPolarApertureVector_tent (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s) (tentApertureVector a) =
      ((∫ x, Real.exp (s * x) * triangleFn a.1 x : ℝ) : ℂ) := by
  change inner ℂ (ccmPolarL2Vector a s) (tentL2 a.1 a.2) = _
  rw [L2.inner_def, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [ccmPolarL2Vector_coeFn a s, tentL2_coeFn a.2] with x hx hy
  rw [hx, hy]
  by_cases hmem : x ∈ centralInterval a.1
  · rw [Set.indicator_of_mem hmem]
    simp only [ccmPolarProfile, RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hmem, triangleFn_eq_zero_of_notMem a.2 hmem]
    simp

/-! ## The tent in the archimedean form domain -/

theorem fourier_tentL2 {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    FourierTransform.fourier (tentL2 a ha : ℝ → ℂ) ξ =
      ((a * Real.sinc (Real.pi * a * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [← fourier_triangleFn ha ξ, Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards [tentL2_coeFn ha] with v hv
  rw [hv]

theorem fourierUnitary_tentL2_ae {a : ℝ} (ha : 0 < a) :
    (fourierUnitary (tentL2 a ha) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => ((a * Real.sinc (Real.pi * a * ξ) ^ 2 : ℝ) : ℂ) := by
  have hint : Integrable (tentL2 a ha : ℝ → ℂ) volume :=
    (memLp_one_iff_integrable.mp (memLp_tentProfile ha 1)).congr (tentL2_coeFn ha).symm
  filter_upwards [fourierUnitary_ae_eq_fourier_of_integrable _ hint] with ξ hξ
  rw [hξ, fourier_tentL2 ha ξ]

/-- Pointwise majorant of the weighted Fourier density of the tent. -/
theorem weight_mul_norm_sq_fourier_tent_le {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    ccmArchimedeanFormWeight ξ * ‖((a * Real.sinc (Real.pi * a * ξ) ^ 2 : ℝ) : ℂ)‖ ^ 2 ≤
      (150 * a ^ 2 + 1 / Real.pi ^ 2) * (1 + (Real.pi * a * ξ) ^ 2)⁻¹ := by
  set y := Real.pi * a * ξ with hy_def
  set s := Real.sinc y ^ 2 with hs_def
  have hs0 : 0 ≤ s := sq_nonneg _
  have hs1 : s ≤ 1 := by
    have h := Real.abs_sinc_le_one y
    rw [hs_def, ← sq_abs]
    nlinarith [abs_nonneg (Real.sinc y)]
  have hsy : s * y ^ 2 ≤ 1 := by
    by_cases hy : y = 0
    · rw [hy]; norm_num
    · rw [hs_def, Real.sinc_of_ne_zero hy, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hy)]
      nlinarith [Real.sin_sq_le_one y]
  have hw := ccmArchimedeanFormWeight_le_quadratic ξ
  have hw0 := (ccmArchimedeanFormWeight_pos ξ).le
  have hnorm : ‖((a * s : ℝ) : ℂ)‖ ^ 2 = a ^ 2 * s ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hnorm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hξa : ξ ^ 2 * a ^ 2 = y ^ 2 / Real.pi ^ 2 := by
    rw [hy_def]; field_simp
  have hstep1 : ccmArchimedeanFormWeight ξ * (a ^ 2 * s ^ 2) * (1 + y ^ 2) ≤
      (75 + ξ ^ 2 / 2) * (a ^ 2 * s ^ 2) * (1 + y ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hstep2 : (75 + ξ ^ 2 / 2) * (a ^ 2 * s ^ 2) * (1 + y ^ 2) ≤
      (75 + ξ ^ 2 / 2) * (a ^ 2 * s) * 2 := by
    have hsum : s * (1 + y ^ 2) ≤ 2 := by nlinarith
    have hfac : 0 ≤ (75 + ξ ^ 2 / 2) * (a ^ 2 * s) := by positivity
    calc (75 + ξ ^ 2 / 2) * (a ^ 2 * s ^ 2) * (1 + y ^ 2)
        = ((75 + ξ ^ 2 / 2) * (a ^ 2 * s)) * (s * (1 + y ^ 2)) := by ring
      _ ≤ ((75 + ξ ^ 2 / 2) * (a ^ 2 * s)) * 2 := mul_le_mul_of_nonneg_left hsum hfac
  have hstep3 : (75 + ξ ^ 2 / 2) * (a ^ 2 * s) * 2 = 150 * a ^ 2 * s + (ξ ^ 2 * a ^ 2) * s := by
    ring
  have hlast : 150 * a ^ 2 * s + (ξ ^ 2 * a ^ 2) * s ≤ 150 * a ^ 2 + 1 / Real.pi ^ 2 := by
    rw [hξa]
    have h1 : 150 * a ^ 2 * s ≤ 150 * a ^ 2 := by nlinarith [sq_nonneg a]
    have h2 : y ^ 2 / Real.pi ^ 2 * s ≤ 1 / Real.pi ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    linarith
  linarith

theorem integrable_tentMajorant {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : ℝ =>
      (150 * a ^ 2 + 1 / Real.pi ^ 2) * (1 + (Real.pi * a * ξ) ^ 2)⁻¹) volume :=
  (integrable_inv_one_add_sq.comp_mul_left' (mul_pos Real.pi_pos ha).ne').const_mul _

theorem integral_tentMajorant {a : ℝ} (ha : 0 < a) :
    ∫ ξ : ℝ, (150 * a ^ 2 + 1 / Real.pi ^ 2) * (1 + (Real.pi * a * ξ) ^ 2)⁻¹ =
      150 * a + 1 / (Real.pi ^ 2 * a) := by
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) (Real.pi * a),
    integral_univ_inv_one_add_sq, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (mul_pos Real.pi_pos ha))]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem memLp_fourierUnitary_tent (a : SuzukiPositiveAperture) :
    MemLp (fun ξ : ℝ => (fourierUnitary (tentApertureVector a).1 : ℝ → ℂ) ξ) 2
      ccmArchimedeanFormMeasure := by
  have hmeasVol : AEStronglyMeasurable
      (fun ξ : ℝ => (fourierUnitary (tentApertureVector a).1 : ℝ → ℂ) ξ) volume :=
    Lp.aestronglyMeasurable _
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => (fourierUnitary (tentApertureVector a).1 : ℝ → ℂ) ξ)
      ccmArchimedeanFormMeasure :=
    hmeasVol.mono_ac ccmArchimedeanFormMeasure_absolutelyContinuous_volume
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  unfold ccmArchimedeanFormMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal]
  have hreal : Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ *
      ‖(fourierUnitary (tentApertureVector a).1 : ℝ → ℂ) ξ‖ ^ 2) volume := by
    refine Integrable.mono' (integrable_tentMajorant a.2)
      (measurable_ccmArchimedeanFormWeight.aestronglyMeasurable.mul
        (hmeasVol.norm.pow 2)) ?_
    filter_upwards [fourierUnitary_tentL2_ae a.2] with ξ hξ
    change ‖ccmArchimedeanFormWeight ξ * ‖(fourierUnitary (tentL2 a.1 a.2) : ℝ → ℂ) ξ‖ ^ 2‖ ≤ _
    rw [hξ, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _))]
    exact weight_mul_norm_sq_fourier_tent_le a.2 ξ
  refine hreal.congr ?_
  filter_upwards with ξ
  rw [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

/-- The tent `τ_a` as a vector of the exact archimedean form domain at aperture `a`. -/
def tentFormVector (a : SuzukiPositiveAperture) : CCMArchimedeanFormDomain a :=
  Classical.choose (exists_ccmArchimedeanFormDomain_of_fourier_memLp a (tentApertureVector a)
    (memLp_fourierUnitary_tent a))

theorem ccmArchimedeanFormToAperture_tentFormVector (a : SuzukiPositiveAperture) :
    ccmArchimedeanFormToAperture a (tentFormVector a) = tentApertureVector a :=
  Classical.choose_spec (exists_ccmArchimedeanFormDomain_of_fourier_memLp a (tentApertureVector a)
    (memLp_fourierUnitary_tent a))

/-- **Explicit form norm of the tent:** `‖u_a‖² ≤ 150 a + 1/(π² a)`. -/
theorem norm_sq_tentFormVector_le (a : SuzukiPositiveAperture) :
    ‖tentFormVector a‖ ^ 2 ≤ 150 * a.1 + 1 / (Real.pi ^ 2 * a.1) := by
  have hnorm : ‖tentFormVector a‖ = ‖(tentFormVector a).1‖ := rfl
  rw [hnorm, norm_sq_ccmArchimedeanFourierL2, ← integral_tentMajorant a.2]
  have hae := ccmFormDomain_ae_eq_fourier a (tentFormVector a)
  rw [ccmArchimedeanFormToAperture_tentFormVector] at hae
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun ξ => mul_nonneg (ccmArchimedeanFormWeight_pos ξ).le (sq_nonneg _))
    (integrable_tentMajorant a.2) ?_
  filter_upwards [hae] with ξ hξ
  change ccmArchimedeanFormWeight ξ * ‖((tentFormVector a).1 : ℝ → ℂ) ξ‖ ^ 2 ≤ _
  rw [hξ]
  change ccmArchimedeanFormWeight ξ *
    ‖FourierTransform.fourier (tentL2 a.1 a.2 : ℝ → ℂ) ξ‖ ^ 2 ≤ _
  rw [fourier_tentL2 a.2 ξ]
  exact weight_mul_norm_sq_fourier_tent_le a.2 ξ

/-- `‖u_a‖² ≤ 150 a + 1/(9 a)`, using `π² ≥ 9`. -/
theorem norm_sq_tentFormVector_le_rational (a : SuzukiPositiveAperture) :
    ‖tentFormVector a‖ ^ 2 ≤ 150 * a.1 + 1 / (9 * a.1) := by
  refine (norm_sq_tentFormVector_le a).trans ?_
  have ha := a.2
  have hπ : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have : 1 / (Real.pi ^ 2 * a.1) ≤ 1 / (9 * a.1) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hπ ha.le)
  linarith

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
