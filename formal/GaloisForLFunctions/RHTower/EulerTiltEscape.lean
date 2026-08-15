import GaloisForLFunctions.RHTower.EulerTiltCovariance
import GaloisForLFunctions.RHTower.EulerTiltSaddleAperture

/-!
# The Euler-edge escape frequency and Schur complement

At the source-faithful tilt the parity–energy data of the Euler-tilted Gibbs source are

```text
A = Var N,   B = Cov(N, E),   C = Var E,   t* = π B / C,   D = π²(A - B²/C).
```

With the canonical cofinal aperture the tilt is `δ ≍ 2 log ℓ/ℓ²`, so `A = log ℓ + O(1)`,
`B = ℓ + O(log ℓ)` and `C = ℓ²/2 + O(ℓ log ℓ)`; hence `t* ℓ → 2π`, `D/log ℓ → π²`, and the
physical shell is resonant: `t* E* → 2π`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The logarithm of the canonical aperture. -/
def apertureLog (L : ℝ) : ℝ := Real.log (cofinalAperture L)

/-- The escape frequency `t* = π Cov(N,E) / Var E`. -/
def eulerTiltEscapeFrequency (σ Y : ℝ) : ℝ :=
  Real.pi * eulerTiltCovariance σ Y / eulerTiltEnergyVariance σ Y

/-- The parity–energy Schur complement `D = π² (Var N - Cov(N,E)²/Var E)`. -/
def eulerTiltSchurComplement (σ Y : ℝ) : ℝ :=
  Real.pi ^ 2 * (eulerTiltMass σ Y
    - eulerTiltCovariance σ Y ^ 2 / eulerTiltEnergyVariance σ Y)

open Classical in
/-- The source-faithful saddle tilt at aperture parameter `L`. -/
def saddleTilt (L : ℝ) : ℝ :=
  if h : ∃ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 then h.choose else 0

theorem eventually_saddleTilt_spec :
    ∀ᶠ L in atTop, saddleTilt L ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect (saddleTilt L) (cofinalAperture L) (Real.exp (-L)) = 0
      ∧ |saddleTilt L - 2 * cofinalApertureWidth L / apertureLog L ^ 2|
          ≤ 2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
            + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3) := by
  filter_upwards [eventually_saddle_root_expansion] with L hL
  obtain ⟨huniq, hexp⟩ := hL
  obtain ⟨δ, ⟨hδmem, hδroot⟩, _⟩ := huniq
  have hex : ∃ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 := ⟨δ, hδmem, hδroot⟩
  have hval : saddleTilt L = hex.choose := by
    rw [saddleTilt, dif_pos hex]
  obtain ⟨hmem, hroot⟩ := hex.choose_spec
  rw [hval]
  exact ⟨hmem, hroot, hexp _ hmem hroot⟩

/-! ## Aperture limits -/

theorem tendsto_apertureLog : Tendsto apertureLog atTop atTop := by
  have hfun : ∀ᶠ L in atTop, apertureLog L = cofinalApertureWidth L + L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact log_cofinalAperture hL
  have hsum : Tendsto (fun L : ℝ => cofinalApertureWidth L + L) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      have h1 : 0 ≤ Real.log L := Real.log_nonneg hL
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    simpa using hw
  exact hsum.congr' (hfun.mono fun L h => h.symm)

theorem tendsto_width_div_apertureLog :
    Tendsto (fun L : ℝ => cofinalApertureWidth L / apertureLog L) atTop (nhds 0) := by
  have hsq := tendsto_widthSq_div_logAperture
  have hA := tendsto_cofinalApertureWidth
  have hquot : Tendsto (fun L : ℝ =>
      (cofinalApertureWidth L ^ 2 / apertureLog L) / cofinalApertureWidth L) atTop (nhds 0) :=
    hsq.div_atTop hA
  refine hquot.congr' ?_
  filter_upwards [hA.eventually_gt_atTop 0, eventually_gt_atTop (1 : ℝ)] with L hApos hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog : apertureLog L = cofinalApertureWidth L + L := log_cofinalAperture hL0
  have hne : cofinalApertureWidth L ≠ 0 := ne_of_gt hApos
  field_simp

theorem tendsto_saddleTilt_mul_apertureLog :
    Tendsto (fun L : ℝ => saddleTilt L * apertureLog L) atTop (nhds 0) := by
  have hspec := eventually_saddleTilt_spec
  have hratio := tendsto_width_div_apertureLog
  have hsq := tendsto_widthSq_div_logAperture
  have hinv : Tendsto (fun L : ℝ => (apertureLog L)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_apertureLog
  have hmaj : Tendsto (fun L : ℝ =>
      2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹))
      atTop (nhds 0) := by
    have h1 := hratio.const_mul (2 : ℝ)
    have h2 := hinv.const_mul (2 * (eulerTiltEnergyConst + 1))
    have h3 := (hsq.mul hinv).const_mul (16 / 3 : ℝ)
    rw [mul_zero] at h1 h2
    rw [mul_zero, mul_zero] at h3
    have h := (h1.add h2).add h3
    rwa [add_zero, add_zero] at h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hspec, tendsto_apertureLog.eventually_gt_atTop 1] with L hL hℓ
  obtain ⟨hmem, _, hexp⟩ := hL
  have hℓ0 : 0 < apertureLog L := by linarith
  have hb := abs_le.mp hexp
  have hpos : 0 < saddleTilt L := hmem.1
  have hupper : saddleTilt L ≤ 2 * cofinalApertureWidth L / apertureLog L ^ 2
      + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
        + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3)) := by
    linarith [hb.2]
  have hstep := mul_le_mul_of_nonneg_right hupper hℓ0.le
  have hval : (2 * cofinalApertureWidth L / apertureLog L ^ 2
      + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
        + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3))) * apertureLog L
      = 2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < saddleTilt L * apertureLog L)]
  calc saddleTilt L * apertureLog L
      ≤ (2 * cofinalApertureWidth L / apertureLog L ^ 2
        + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
          + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3))) * apertureLog L := hstep
    _ = 2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹) := hval

theorem tendsto_cofinalAperture : Tendsto cofinalAperture atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have h1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
  have hL0 : (0 : ℝ) < L := by linarith
  rw [cofinalAperture]
  simp only [id_eq]
  nlinarith

theorem tendsto_saddleTilt : Tendsto saddleTilt atTop (nhds 0) := by
  have hmul := tendsto_saddleTilt_mul_apertureLog
  have hquot := hmul.div_atTop tendsto_apertureLog
  refine hquot.congr' ?_
  filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1] with L hℓ
  have hℓ0 : apertureLog L ≠ 0 := by
    intro h
    rw [h] at hℓ
    linarith
  field_simp

theorem tendsto_inv_apertureLog : Tendsto (fun L : ℝ => (apertureLog L)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_apertureLog

theorem tendsto_inv_logApertureLog :
    Tendsto (fun L : ℝ => (Real.log (apertureLog L))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_apertureLog)

theorem tendsto_logApertureLog : Tendsto (fun L : ℝ => Real.log (apertureLog L)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_apertureLog

/-! ## The Euler-edge covariance limits at the saddle tilt -/

theorem tendsto_eulerTiltCovariance_div :
    Tendsto (fun L : ℝ =>
      eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L) atTop
      (nhds 1) := by
  have hδ0 := tendsto_saddleTilt
  have hδℓ := tendsto_saddleTilt_mul_apertureLog
  have hinv := tendsto_inv_apertureLog
  -- the majorant
  have hmaj : Tendsto (fun L : ℝ =>
      ((mertensPrimeWindowBound + 1) + 3 * logSquareTailConst) * (apertureLog L)⁻¹
        + saddleTilt L * apertureLog L / 2
        + saddleTilt L * (mertensLogSqConst * ((apertureLog L)⁻¹ + 1))
        + saddleTilt L * (Real.log 2 ^ 2 / 2) * (apertureLog L)⁻¹) atTop (nhds 0) := by
    have h1 := hinv.const_mul ((mertensPrimeWindowBound + 1) + 3 * logSquareTailConst)
    have h2 := hδℓ.div_const 2
    have h3 : Tendsto (fun L : ℝ =>
        saddleTilt L * (mertensLogSqConst * ((apertureLog L)⁻¹ + 1))) atTop (nhds 0) := by
      have hb : Tendsto (fun L : ℝ => mertensLogSqConst * ((apertureLog L)⁻¹ + 1)) atTop
          (nhds (mertensLogSqConst * (0 + 1))) := by
        exact (hinv.add tendsto_const_nhds).const_mul _
      have h := hδ0.mul hb
      rwa [zero_mul] at h
    have h4 : Tendsto (fun L : ℝ =>
        saddleTilt L * (Real.log 2 ^ 2 / 2) * (apertureLog L)⁻¹) atTop (nhds 0) := by
      have h := (hδ0.mul_const (Real.log 2 ^ 2 / 2)).mul hinv
      rwa [zero_mul, zero_mul] at h
    rw [mul_zero] at h1
    rw [zero_div] at h2
    have h := ((h1.add h2).add h3).add h4
    rwa [add_zero, add_zero, add_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_saddleTilt_spec, tendsto_apertureLog.eventually_gt_atTop 1,
    tendsto_cofinalAperture.eventually_ge_atTop (2 : ℝ)] with L hspec hℓ hY
  obtain ⟨hmem, _, _⟩ := hspec
  have hℓ0 : 0 < apertureLog L := by linarith
  have hδnn : 0 ≤ saddleTilt L := hmem.1.le
  have hlogY : apertureLog L = Real.log (cofinalAperture L) := rfl
  have hbound := abs_eulerTiltCovariance_sub_log_le (δ := saddleTilt L)
    (Y := cofinalAperture L) hδnn hY
  rw [← hlogY] at hbound
  have hval : eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L - 1
      = (eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) - apertureLog L)
        / apertureLog L := by
    field_simp
  rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos hℓ0]
  rw [div_le_iff₀ hℓ0]
  refine le_trans hbound ?_
  have hexpand : (((mertensPrimeWindowBound + 1) + 3 * logSquareTailConst) * (apertureLog L)⁻¹
      + saddleTilt L * apertureLog L / 2
      + saddleTilt L * (mertensLogSqConst * ((apertureLog L)⁻¹ + 1))
      + saddleTilt L * (Real.log 2 ^ 2 / 2) * (apertureLog L)⁻¹) * apertureLog L
      = ((mertensPrimeWindowBound + 1) + 3 * logSquareTailConst)
        + saddleTilt L * (apertureLog L ^ 2 / 2
          + mertensLogSqConst * (1 + apertureLog L) + Real.log 2 ^ 2 / 2) := by
    field_simp
    ring
  rw [hexpand]

theorem tendsto_eulerTiltEnergyVariance_div :
    Tendsto (fun L : ℝ =>
      eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2) atTop
      (nhds (1 / 2)) := by
  have hδ0 := tendsto_saddleTilt
  have hδℓ := tendsto_saddleTilt_mul_apertureLog
  have hinv := tendsto_inv_apertureLog
  have hinv2 : Tendsto (fun L : ℝ => (apertureLog L ^ 2)⁻¹) atTop (nhds 0) := by
    have h := hinv.mul hinv
    rw [mul_zero] at h
    refine h.congr fun L => ?_
    rw [← mul_inv, ← sq]
  have hmaj : Tendsto (fun L : ℝ =>
      mertensLogSqConst * ((apertureLog L ^ 2)⁻¹ + (apertureLog L)⁻¹)
        + (Real.log 2 ^ 2 / 2 + 3 * logSqSquareTailConst) * (apertureLog L ^ 2)⁻¹
        + saddleTilt L * apertureLog L
          * (1 / 2 + mertensLogSqConst * ((apertureLog L ^ 2)⁻¹ + (apertureLog L)⁻¹)
            + Real.log 2 ^ 2 / 2 * (apertureLog L ^ 2)⁻¹)) atTop (nhds 0) := by
    have h1 : Tendsto (fun L : ℝ =>
        mertensLogSqConst * ((apertureLog L ^ 2)⁻¹ + (apertureLog L)⁻¹)) atTop (nhds 0) := by
      have h := (hinv2.add hinv).const_mul mertensLogSqConst
      rwa [add_zero, mul_zero] at h
    have h2 : Tendsto (fun L : ℝ =>
        (Real.log 2 ^ 2 / 2 + 3 * logSqSquareTailConst) * (apertureLog L ^ 2)⁻¹) atTop
        (nhds 0) := by
      have h := hinv2.const_mul (Real.log 2 ^ 2 / 2 + 3 * logSqSquareTailConst)
      rwa [mul_zero] at h
    have h3 : Tendsto (fun L : ℝ =>
        saddleTilt L * apertureLog L
          * (1 / 2 + mertensLogSqConst * ((apertureLog L ^ 2)⁻¹ + (apertureLog L)⁻¹)
            + Real.log 2 ^ 2 / 2 * (apertureLog L ^ 2)⁻¹)) atTop (nhds 0) := by
      have hfac : Tendsto (fun L : ℝ =>
          1 / 2 + mertensLogSqConst * ((apertureLog L ^ 2)⁻¹ + (apertureLog L)⁻¹)
            + Real.log 2 ^ 2 / 2 * (apertureLog L ^ 2)⁻¹) atTop (nhds (1 / 2)) := by
        have hconst : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)) :=
          tendsto_const_nhds
        have hb := (hconst.add h1).add (hinv2.const_mul (Real.log 2 ^ 2 / 2))
        rw [add_zero, mul_zero, add_zero] at hb
        exact hb
      have h := hδℓ.mul hfac
      rwa [zero_mul] at h
    have h := (h1.add h2).add h3
    rwa [add_zero, add_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_saddleTilt_spec, tendsto_apertureLog.eventually_gt_atTop 1,
    tendsto_cofinalAperture.eventually_ge_atTop (2 : ℝ)] with L hspec hℓ hY
  obtain ⟨hmem, _, _⟩ := hspec
  have hℓ0 : 0 < apertureLog L := by linarith
  have hδnn : 0 ≤ saddleTilt L := hmem.1.le
  have hlogY : apertureLog L = Real.log (cofinalAperture L) := rfl
  have hbound := abs_eulerTiltEnergyVariance_sub_logSq_le (δ := saddleTilt L)
    (Y := cofinalAperture L) hδnn hY
  rw [← hlogY] at hbound
  have hval : eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2
      - 1 / 2
      = (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) - apertureLog L ^ 2 / 2)
        / apertureLog L ^ 2 := by
    field_simp
  rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos (by positivity : (0:ℝ) < apertureLog L ^ 2)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < apertureLog L ^ 2)]
  refine le_trans hbound (le_of_eq ?_)
  field_simp
  ring

theorem tendsto_eulerTiltMass_div :
    Tendsto (fun L : ℝ =>
      eulerTiltMass (1 + saddleTilt L) (cofinalAperture L) / Real.log (apertureLog L)) atTop
      (nhds 1) := by
  have hδ0 := tendsto_saddleTilt
  have hδℓ := tendsto_saddleTilt_mul_apertureLog
  have hinvlog := tendsto_inv_logApertureLog
  have hmaj : Tendsto (fun L : ℝ =>
      eulerTiltMassConst * (Real.log (apertureLog L))⁻¹
        + saddleTilt L * apertureLog L * (Real.log (apertureLog L))⁻¹
        + saddleTilt L * (mertensPrimeWindowBound + 1) * (Real.log (apertureLog L))⁻¹) atTop
      (nhds 0) := by
    have h1 := hinvlog.const_mul eulerTiltMassConst
    have h2 := hδℓ.mul hinvlog
    have h3 := (hδ0.mul_const (mertensPrimeWindowBound + 1)).mul hinvlog
    rw [mul_zero] at h1
    rw [zero_mul] at h2
    rw [zero_mul, zero_mul] at h3
    have h := (h1.add h2).add h3
    rwa [add_zero, add_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_saddleTilt_spec,
    tendsto_logApertureLog.eventually_gt_atTop 1,
    tendsto_apertureLog.eventually_gt_atTop 1,
    tendsto_cofinalAperture.eventually_ge_atTop (Real.exp 2)] with L hspec hlogℓ hℓ hY
  obtain ⟨hmem, _, _⟩ := hspec
  have hℓ0 : 0 < apertureLog L := by linarith
  have hlogℓ0 : 0 < Real.log (apertureLog L) := by linarith
  have hδnn : 0 ≤ saddleTilt L := hmem.1.le
  have hlogY : apertureLog L = Real.log (cofinalAperture L) := rfl
  have hbound := abs_eulerTiltMass_sub_logLog_le (δ := saddleTilt L)
    (Y := cofinalAperture L) hδnn hY
  rw [← hlogY] at hbound
  have hval : eulerTiltMass (1 + saddleTilt L) (cofinalAperture L) / Real.log (apertureLog L) - 1
      = (eulerTiltMass (1 + saddleTilt L) (cofinalAperture L) - Real.log (apertureLog L))
        / Real.log (apertureLog L) := by
    field_simp
  rw [Real.norm_eq_abs, hval, abs_div, abs_of_pos hlogℓ0, div_le_iff₀ hlogℓ0]
  refine le_trans hbound (le_of_eq ?_)
  field_simp
  ring

/-! ## The escape laws -/

theorem eventually_energyVariance_pos :
    ∀ᶠ L in atTop, 0 < eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) := by
  have hC := tendsto_eulerTiltEnergyVariance_div
  filter_upwards [hC.eventually (lt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    tendsto_apertureLog.eventually_gt_atTop 1] with L hCpos hℓ
  have hℓ0 : 0 < apertureLog L ^ 2 := by positivity
  have hval : eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L)
      = (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2)
        * apertureLog L ^ 2 := by
    field_simp
  rw [hval]
  exact mul_pos hCpos hℓ0

/-- **(12) The escape frequency.**  `t* = 2π/ℓ (1 + o(1))`. -/
theorem tendsto_escapeFrequency_mul_apertureLog :
    Tendsto (fun L : ℝ =>
      eulerTiltEscapeFrequency (1 + saddleTilt L) (cofinalAperture L) * apertureLog L) atTop
      (nhds (2 * Real.pi)) := by
  have hB := tendsto_eulerTiltCovariance_div
  have hC := tendsto_eulerTiltEnergyVariance_div
  have hquot : Tendsto (fun L : ℝ =>
      Real.pi * (eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L)
        / (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2))
      atTop (nhds (Real.pi * 1 / (1 / 2))) :=
    (hB.const_mul Real.pi).div hC (by norm_num)
  have hval : Real.pi * 1 / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1, eventually_energyVariance_pos]
    with L hℓ hCpos
  have hℓ0 : 0 < apertureLog L := by linarith
  rw [eulerTiltEscapeFrequency]
  field_simp

/-- **(12) The parity–energy Schur complement.**  `D = π² log ℓ (1 + o(1))`. -/
theorem tendsto_schurComplement_div_logApertureLog :
    Tendsto (fun L : ℝ =>
      eulerTiltSchurComplement (1 + saddleTilt L) (cofinalAperture L)
        / Real.log (apertureLog L)) atTop (nhds (Real.pi ^ 2)) := by
  have hA := tendsto_eulerTiltMass_div
  have hB := tendsto_eulerTiltCovariance_div
  have hC := tendsto_eulerTiltEnergyVariance_div
  have hinvlog := tendsto_inv_logApertureLog
  have hratio : Tendsto (fun L : ℝ =>
      (eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L) ^ 2
        / (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2))
      atTop (nhds ((1 : ℝ) ^ 2 / (1 / 2))) := (hB.pow 2).div hC (by norm_num)
  have hsecond : Tendsto (fun L : ℝ =>
      ((eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L) ^ 2
        / (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2))
        * (Real.log (apertureLog L))⁻¹) atTop (nhds 0) := by
    have h := hratio.mul hinvlog
    rwa [mul_zero] at h
  have hcomb : Tendsto (fun L : ℝ =>
      Real.pi ^ 2 * ((eulerTiltMass (1 + saddleTilt L) (cofinalAperture L)
          / Real.log (apertureLog L))
        - ((eulerTiltCovariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L) ^ 2
          / (eulerTiltEnergyVariance (1 + saddleTilt L) (cofinalAperture L) / apertureLog L ^ 2))
          * (Real.log (apertureLog L))⁻¹)) atTop (nhds (Real.pi ^ 2 * (1 - 0))) :=
    (hA.sub hsecond).const_mul _
  rw [sub_zero, mul_one] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1, eventually_energyVariance_pos,
    tendsto_logApertureLog.eventually_gt_atTop 1] with L hℓ hCpos hlogℓ
  have hℓ0 : 0 < apertureLog L := by linarith
  have hlogℓ0 : 0 < Real.log (apertureLog L) := by linarith
  rw [eulerTiltSchurComplement]
  field_simp

/-- **(13) Shell resonance.**  `t* E* → 2π`. -/
theorem tendsto_escapeFrequency_mul_center :
    Tendsto (fun L : ℝ =>
      eulerTiltEscapeFrequency (1 + saddleTilt L) (cofinalAperture L)
        * Real.log ((1 + saddleTilt L) / Real.exp (-L))) atTop (nhds (2 * Real.pi)) := by
  have hfreq := tendsto_escapeFrequency_mul_apertureLog
  have hδ0 := tendsto_saddleTilt
  have hwidth := tendsto_width_div_apertureLog
  have hinv := tendsto_inv_apertureLog
  -- the centre is the aperture logarithm up to `o(ℓ)`
  have hlogδ : Tendsto (fun L : ℝ => Real.log (1 + saddleTilt L)) atTop (nhds 0) := by
    have hcont : ContinuousAt (fun t : ℝ => Real.log (1 + t)) 0 := by
      have h1 : ContinuousAt (fun t : ℝ => 1 + t) 0 := by fun_prop
      have hne : (1 : ℝ) + 0 ≠ 0 := by norm_num
      exact h1.log hne
    have h := hcont.tendsto.comp hδ0
    have hval : Real.log (1 + (0 : ℝ)) = 0 := by norm_num
    rw [hval] at h
    exact h
  have hcentre : Tendsto (fun L : ℝ =>
      Real.log ((1 + saddleTilt L) / Real.exp (-L)) / apertureLog L) atTop (nhds 1) := by
    have hcomb : Tendsto (fun L : ℝ =>
        1 - cofinalApertureWidth L / apertureLog L
          + Real.log (1 + saddleTilt L) * (apertureLog L)⁻¹) atTop (nhds (1 - 0 + 0 * 0)) := by
      exact (tendsto_const_nhds.sub hwidth).add (hlogδ.mul hinv)
    rw [sub_zero, mul_zero, add_zero] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1, eventually_gt_atTop (1 : ℝ),
      eventually_saddleTilt_spec] with L hℓ hL hspec
    obtain ⟨hmem, _, _⟩ := hspec
    have hℓ0 : 0 < apertureLog L := by linarith
    have hL0 : (0 : ℝ) < L := by linarith
    have hδpos : 0 < 1 + saddleTilt L := by linarith [hmem.1]
    have hlogval : Real.log ((1 + saddleTilt L) / Real.exp (-L))
        = Real.log (1 + saddleTilt L) + L := by
      rw [Real.log_div (ne_of_gt hδpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      ring
    have hwidthval : apertureLog L = cofinalApertureWidth L + L := log_cofinalAperture hL0
    rw [hlogval]
    field_simp
    nlinarith [hwidthval, hℓ0]
  have h := hfreq.mul hcentre
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [tendsto_apertureLog.eventually_gt_atTop 1] with L hℓ
  have hℓ0 : 0 < apertureLog L := by linarith
  field_simp

end

end RHTower
