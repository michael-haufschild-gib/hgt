import GaloisForLFunctions.HyperbolicArakelovTheory.TheGeometricScatteringTowerDetectsTheWeilFormDomain
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadGammaAutocorrelationEnergy
import GaloisForLFunctions.RHTower.FourierL2SobolevDomain
import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The second height jet of the geometric scattering tower

The omitted positive jump tail concentrates at the origin as the scattering height grows.
The quadratic height scaling converges to half the physical Dirichlet energy, including
infinity. On the complete Weil form domain this is exactly the raw scattering defect after
removing the Robin mass drift and an exponentially vanishing finite-prime correction.
A finite second-height limit exists precisely on the physical H¹ subdomain.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped ENNReal InnerProductSpace BigOperators Classical
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower

/-- The extended omitted jump energy at a positive integer scattering height. -/
def scatteringSecondHeightEnergy (N : ℕ) (f : SoninL2) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
    (((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) + 1) * t) *
      archLevyDensity t * ccmActualHeadTranslationDefect t f)

/-- Physical Dirichlet energy in the unitary Fourier normalization, retaining infinity. -/
def scatteringDirichletEnergy (f : SoninL2) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2 * ‖fourierUnitary f ξ‖ ^ 2)


private def heightScale (N : ℕ) : ℝ := (N : ℝ) + 1

private theorem heightScale_pos (N : ℕ) : 0 < heightScale N := by
  unfold heightScale
  positivity

private theorem heightScale_ge_one (N : ℕ) : 1 ≤ heightScale N := by
  unfold heightScale
  linarith only [Nat.cast_nonneg (α := ℝ) N]

private theorem tendsto_heightScale : Tendsto heightScale atTop atTop := by
  exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private theorem levy_moment_bounds {t : ℝ} (ht : 0 < t) :
    1 / 2 + t / 4 - t ^ 2 / 16 - t ^ 3 / 32 ≤ t * archLevyDensity t ∧
      t * archLevyDensity t ≤ 1 / 2 + t / 4 := by
  constructor
  · calc
      _ = t * (1 / (2 * t) + 1 / 4 - t / 16 - t ^ 2 / 32) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ArithmeticIncidencePositivity.inv_le_archLevyDensity ht) ht.le
  · calc
      _ ≤ t * (1 / (2 * t) + 1 / 4) := mul_le_mul_of_nonneg_left
        (ArithmeticIncidencePositivity.archLevyDensity_le_inv ht) ht.le
      _ = _ := by field_simp

private theorem tendsto_scaled_levy_moment {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N => (x / heightScale N) * archLevyDensity (x / heightScale N))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht := tendsto_heightScale.const_div_atTop x
  have hb : Tendsto (fun N => (x / heightScale N) / 4 +
      (x / heightScale N) ^ 2 / 16 + (x / heightScale N) ^ 3 / 32)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (3 : ℕ) ≠ 0), add_zero] using
      ((ht.div_const 4).add ((ht.pow 2).div_const 16)).add ((ht.pow 3).div_const 32)
  have hbound : ∀ᶠ N in atTop,
      ‖(x / heightScale N) * archLevyDensity (x / heightScale N) - 1 / 2‖ ≤
        (x / heightScale N) / 4 + (x / heightScale N) ^ 2 / 16 +
          (x / heightScale N) ^ 3 / 32 := by
    filter_upwards with N
    have htpos : 0 < x / heightScale N := div_pos hx (heightScale_pos N)
    obtain ⟨hl, hu⟩ := levy_moment_bounds htpos
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith only [hl, hu, htpos, sq_nonneg (x / heightScale N),
      pow_nonneg htpos.le 3]
  have h := (squeeze_zero_norm' hbound hb).add_const (1 / 2 : ℝ)
  simpa only [zero_add, sub_add_cancel] using h

/-- The scalar Fourier kernel after rescaling distance by the positive scattering height. -/
private def scaledHeightKernel (N : ℕ) (τ x : ℝ) : ℝ :=
  Real.exp (-x) * ((x / heightScale N) * archLevyDensity (x / heightScale N)) *
    (τ ^ 2 * x) * Real.sinc (τ * x / 2 / heightScale N) ^ 2

private theorem scaledHeightKernel_nonneg (N : ℕ) (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ scaledHeightKernel N τ x := by
  unfold scaledHeightKernel
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (div_pos hx (heightScale_pos N)).le
        (archLevyDensity_pos (div_pos hx (heightScale_pos N))).le))
      (mul_nonneg (sq_nonneg τ) hx.le)) (sq_nonneg _)

private theorem scaledHeightKernel_bound (N : ℕ) (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    scaledHeightKernel N τ x ≤ τ ^ 2 * Real.exp (-x) * (x / 2 + x ^ 2 / 4) := by
  have hn := heightScale_ge_one N
  have hxn : x / heightScale N ≤ x := div_le_self hx.le hn
  have hlevy := (levy_moment_bounds (div_pos hx (heightScale_pos N))).2
  have hm : (x / heightScale N) * archLevyDensity (x / heightScale N) ≤ 1 / 2 + x / 4 := by
    linarith only [hlevy, hxn]
  have hs : Real.sinc (τ * x / 2 / heightScale N) ^ 2 ≤ 1 := by
    have h := Real.abs_sinc_le_one (τ * x / 2 / heightScale N)
    nlinarith only [sq_abs (Real.sinc (τ * x / 2 / heightScale N)),
      abs_nonneg (Real.sinc (τ * x / 2 / heightScale N)), h]
  unfold scaledHeightKernel
  calc
    _ ≤ Real.exp (-x) * (1 / 2 + x / 4) * (τ ^ 2 * x) * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
          (mul_nonneg (sq_nonneg τ) hx.le)
      · exact hs
      · exact sq_nonneg _
      · positivity
    _ = _ := by ring

private theorem tendsto_scaledHeightKernel (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N => scaledHeightKernel N τ x) atTop
      (𝓝 (τ ^ 2 * Real.exp (-x) * x / 2)) := by
  have hs := Real.continuous_sinc.continuousAt.tendsto.comp
    (tendsto_heightScale.const_div_atTop (τ * x / 2))
  simp only [Function.comp_def, Real.sinc_zero] at hs
  have h := (((tendsto_scaled_levy_moment hx).const_mul (Real.exp (-x))).mul_const
    (τ ^ 2 * x)).mul (hs.pow 2)
  simpa only [scaledHeightKernel, one_pow, mul_one, mul_assoc, mul_comm, mul_left_comm,
    div_eq_mul_inv, one_mul] using h

private theorem scaledHeightKernel_eq (N : ℕ) (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    scaledHeightKernel N τ x = heightScale N * Real.exp (-x) *
      archLevyDensity (x / heightScale N) * (2 - 2 * Real.cos (τ * (x / heightScale N))) := by
  have hn : heightScale N ≠ 0 := (heightScale_pos N).ne'
  have hxn : x / heightScale N ≠ 0 := div_ne_zero hx.ne' hn
  have h := HTGeometry.sq_mul_sinc_sq_eq_normalized_cosDefect
    (m := 1) one_ne_zero hxn τ
  rw [div_one, one_mul, show τ / 2 * (x / heightScale N) =
    τ * x / 2 / heightScale N by ring] at h
  unfold scaledHeightKernel
  calc
    _ = Real.exp (-x) * ((x / heightScale N) * archLevyDensity (x / heightScale N)) *
        x * (τ ^ 2 * Real.sinc (τ * x / 2 / heightScale N) ^ 2) := by ring
    _ = _ := by
      rw [h]
      field_simp


private theorem integrable_height_moment (j : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ j * Real.exp (-x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (j : ℝ)) (p := 1) (b := 1)
    (by linarith only [Nat.cast_nonneg (α := ℝ) j]) le_rfl zero_lt_one
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, neg_one_mul]

private theorem integral_height_moment (j : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ j * Real.exp (-x)) = j.factorial := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (j : ℝ) + 1) (r := 1) (by positivity) zero_lt_one
  simpa only [add_sub_cancel_right, Real.rpow_natCast, one_div_one,
    Real.one_rpow, one_mul, Real.Gamma_nat_eq_factorial] using h

private theorem integrable_height_majorant (τ : ℝ) :
    IntegrableOn (fun x : ℝ => τ ^ 2 * Real.exp (-x) * (x / 2 + x ^ 2 / 4)) (Ioi 0) := by
  have h := ((integrable_height_moment 1).const_mul (τ ^ 2 / 2)).add
    ((integrable_height_moment 2).const_mul (τ ^ 2 / 4))
  refine h.congr (Eventually.of_forall fun x => ?_)
  dsimp only [Pi.add_apply]
  ring

private theorem integral_height_majorant (τ : ℝ) :
    (∫ x in Ioi (0 : ℝ), τ ^ 2 * Real.exp (-x) * (x / 2 + x ^ 2 / 4)) = τ ^ 2 := by
  have he : (fun x : ℝ => τ ^ 2 * Real.exp (-x) * (x / 2 + x ^ 2 / 4)) =
      fun x => (τ ^ 2 / 2) * (x ^ 1 * Real.exp (-x)) +
        (τ ^ 2 / 4) * (x ^ 2 * Real.exp (-x)) := by funext x; ring
  rw [he, integral_add ((integrable_height_moment 1).const_mul _)
    ((integrable_height_moment 2).const_mul _), integral_const_mul, integral_const_mul,
    integral_height_moment, integral_height_moment]
  norm_num
  ring

private theorem measurable_scaledHeightKernel (N : ℕ) (τ : ℝ) :
    Measurable (scaledHeightKernel N τ) := by
  unfold scaledHeightKernel archLevyDensity
  fun_prop

private theorem integrable_scaledHeightKernel (N : ℕ) (τ : ℝ) :
    IntegrableOn (scaledHeightKernel N τ) (Ioi 0) := by
  refine (integrable_height_majorant τ).mono'
    (measurable_scaledHeightKernel N τ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (scaledHeightKernel_nonneg N τ hx)]
  exact scaledHeightKernel_bound N τ hx

/-- Fourier multiplier of the second-height jump tail, in physical angular frequency. -/
def scatteringSecondHeightSymbol (N : ℕ) (τ : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), scaledHeightKernel N τ x

theorem scatteringSecondHeightSymbol_nonneg (N : ℕ) (τ : ℝ) :
    0 ≤ scatteringSecondHeightSymbol N τ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact scaledHeightKernel_nonneg N τ hx

/-- A single quadratic-frequency majorant controls every positive scattering height. -/
theorem scatteringSecondHeightSymbol_le (N : ℕ) (τ : ℝ) :
    scatteringSecondHeightSymbol N τ ≤ τ ^ 2 := by
  rw [scatteringSecondHeightSymbol, ← integral_height_majorant τ]
  apply integral_mono_ae (integrable_scaledHeightKernel N τ) (integrable_height_majorant τ)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact scaledHeightKernel_bound N τ hx

/-- The second-height multiplier has the exact physical Laplacian coefficient one half. -/
theorem tendsto_scatteringSecondHeightSymbol (τ : ℝ) :
    Tendsto (fun N => scatteringSecondHeightSymbol N τ) atTop (𝓝 (τ ^ 2 / 2)) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun x : ℝ => τ ^ 2 * Real.exp (-x) * (x / 2 + x ^ 2 / 4))
    (F := fun N => scaledHeightKernel N τ)
    (f := fun x => τ ^ 2 * Real.exp (-x) * x / 2)
    (fun N => (measurable_scaledHeightKernel N τ).aestronglyMeasurable)
    (integrable_height_majorant τ)
    (fun N => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_of_nonneg (scaledHeightKernel_nonneg N τ hx)]
      exact scaledHeightKernel_bound N τ hx)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact tendsto_scaledHeightKernel τ hx)
  have he : (∫ x in Ioi (0 : ℝ), τ ^ 2 * Real.exp (-x) * x / 2) = τ ^ 2 / 2 := by
    have hf : (fun x : ℝ => τ ^ 2 * Real.exp (-x) * x / 2) =
        fun x => (τ ^ 2 / 2) * (x ^ 1 * Real.exp (-x)) := by funext x; ring
    rw [hf, integral_const_mul, integral_height_moment]
    norm_num
  rwa [he] at h

private def originalHeightKernel (N : ℕ) (τ t : ℝ) : ℝ :=
  heightScale N ^ 2 * Real.exp (-heightScale N * t) *
    archLevyDensity t * (2 - 2 * Real.cos (τ * t))

private theorem originalHeightKernel_rescale (N : ℕ) (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    originalHeightKernel N τ ((heightScale N)⁻¹ * x) =
      heightScale N * scaledHeightKernel N τ x := by
  rw [scaledHeightKernel_eq N τ hx]
  unfold originalHeightKernel
  have hn := (heightScale_pos N).ne'
  rw [show (heightScale N)⁻¹ * x = x / heightScale N by ring,
    show -heightScale N * (x / heightScale N) = -x by field_simp]
  ring

private theorem integrable_originalHeightKernel (N : ℕ) (τ : ℝ) :
    IntegrableOn (originalHeightKernel N τ) (Ioi 0) := by
  have h : IntegrableOn (fun x => originalHeightKernel N τ ((heightScale N)⁻¹ * x)) (Ioi 0) := by
    refine ((integrable_scaledHeightKernel N τ).const_mul (heightScale N)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (originalHeightKernel_rescale N τ hx).symm
  have hscale := (integrableOn_Ioi_comp_mul_left_iff (originalHeightKernel N τ)
    0 (inv_pos.mpr (heightScale_pos N))).mp h
  simpa only [mul_zero] using hscale

/-- The rescaled multiplier is exactly the omitted finite-scattering Fourier tail. -/
theorem scatteringSecondHeightSymbol_eq_integral (N : ℕ) (τ : ℝ) :
    scatteringSecondHeightSymbol N τ =
      ∫ t in Ioi (0 : ℝ), ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) + 1) * t) *
        archLevyDensity t * (2 - 2 * Real.cos (τ * t)) := by
  have h := integral_comp_mul_left_Ioi (originalHeightKernel N τ) 0
    (inv_pos.mpr (heightScale_pos N))
  simp only [inv_inv, mul_zero, smul_eq_mul] at h
  have he : (∫ x in Ioi (0 : ℝ), originalHeightKernel N τ ((heightScale N)⁻¹ * x)) =
      heightScale N * scatteringSecondHeightSymbol N τ := by
    unfold scatteringSecondHeightSymbol
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => originalHeightKernel_rescale N τ hx
  rw [he] at h
  have hr := (mul_left_cancel₀ (heightScale_pos N).ne' h)
  exact hr


private theorem originalHeightKernel_nonneg (N : ℕ) (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ originalHeightKernel N τ t := by
  unfold originalHeightKernel
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (archLevyDensity_pos ht).le) (by linarith only [Real.cos_le_one (τ * t)])

private theorem measurable_heightSymbol (N : ℕ) :
    Measurable (scatteringSecondHeightSymbol N) := by
  have h : Measurable (fun p : ℝ × ℝ => scaledHeightKernel N p.1 p.2) := by
    unfold scaledHeightKernel archLevyDensity
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Tonelli and Plancherel identify the omitted geometric tail on every physical L² state. -/
theorem scatteringSecondHeightEnergy_eq_fourier (N : ℕ) (f : SoninL2) :
    scatteringSecondHeightEnergy N f = ∫⁻ ξ : ℝ, ENNReal.ofReal
      (scatteringSecondHeightSymbol N (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2) := by
  let g := fourierUnitary f
  let D : ℝ → ℝ := fun t => heightScale N ^ 2 * Real.exp (-heightScale N * t) * archLevyDensity t
  have hD (t : ℝ) (ht : 0 < t) : 0 ≤ D t :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (archLevyDensity_pos ht).le
  have he : scatteringSecondHeightEnergy N f = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ξ : ℝ,
      ENNReal.ofReal (D t * ((2 - 2 * Real.cos (2 * Real.pi * t * ξ)) * ‖g ξ‖ ^ 2)) := by
    unfold scatteringSecondHeightEnergy
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hf : f = fourierUnitary.symm g := (fourierUnitary.symm_apply_apply f).symm
    change ENNReal.ofReal (D t * ccmActualHeadTranslationDefect t f) = _
    rw [hf, ccmActualHeadTranslationDefect_fourierUnitary_symm]
    have hi := (integrable_ccmGammaCosineDefectSpectralDensity t g).const_mul (D t)
    rw [← integral_const_mul]
    exact ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ξ =>
      mul_nonneg (hD t ht) (ccmGammaCosineDefectSpectralDensity_nonneg t g ξ))
  have hm : AEMeasurable (Function.uncurry fun t ξ : ℝ =>
      ENNReal.ofReal (D t * ((2 - 2 * Real.cos (2 * Real.pi * t * ξ)) * ‖g ξ‖ ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hs : Measurable fun p : ℝ × ℝ => D p.1 *
        (2 - 2 * Real.cos (2 * Real.pi * p.1 * p.2)) := by
      dsimp only [D]
      unfold archLevyDensity
      fun_prop
    have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p.2‖ ^ 2)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
      ((Lp.aestronglyMeasurable g).norm.pow 2).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
    have hr := (hs.aestronglyMeasurable.mul hg).aemeasurable.ennreal_ofReal
    simpa only [Function.uncurry_def, Pi.mul_apply, mul_assoc] using hr
  rw [he, lintegral_lintegral_swap hm]
  apply lintegral_congr
  intro ξ
  have hi := (integrable_originalHeightKernel N (2 * Real.pi * ξ)).mul_const (‖g ξ‖ ^ 2)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => originalHeightKernel N (2 * Real.pi * ξ) t * ‖g ξ‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (originalHeightKernel_nonneg N _ ht) (sq_nonneg _)
  have halg : (fun t => D t * ((2 - 2 * Real.cos (2 * Real.pi * t * ξ)) * ‖g ξ‖ ^ 2)) =
      fun t => originalHeightKernel N (2 * Real.pi * ξ) t * ‖g ξ‖ ^ 2 := by
    funext t
    dsimp only [D, originalHeightKernel]
    rw [show 2 * Real.pi * t * ξ = 2 * Real.pi * ξ * t by ring]
    ring
  simp_rw [congrFun halg]
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_mul_const]
  rw [scatteringSecondHeightSymbol_eq_integral]
  rfl

private theorem measurable_heightSpectralDensity (N : ℕ) (f : SoninL2) :
    Measurable fun ξ : ℝ => ENNReal.ofReal
      (scatteringSecondHeightSymbol N (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2) := by
  exact ((measurable_heightSymbol N |>.comp (by fun_prop)).mul
    ((Lp.stronglyMeasurable (fourierUnitary f)).measurable.norm.pow_const 2)).ennreal_ofReal

/-- The second-height tail converges to half Dirichlet energy, including infinity. -/
theorem tendsto_scatteringSecondHeightEnergy (f : SoninL2) :
    Tendsto (fun N => scatteringSecondHeightEnergy N f) atTop
      (𝓝 (ENNReal.ofReal (1 / 2 : ℝ) * scatteringDirichletEnergy f)) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun N ξ => ENNReal.ofReal
    (scatteringSecondHeightSymbol N (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2)
  let B : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    ((2 * Real.pi * ξ) ^ 2 * ‖fourierUnitary f ξ‖ ^ 2)
  let L : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (1 / 2 : ℝ) * B ξ
  have hm (N : ℕ) : Measurable (F N) := measurable_heightSpectralDensity N f
  have hb : Measurable B := by
    exact ((by fun_prop : Measurable fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2).mul
      ((Lp.stronglyMeasurable (fourierUnitary f)).measurable.norm.pow_const 2)).ennreal_ofReal
  have hlim (ξ : ℝ) : Tendsto (fun N => F N ξ) atTop (𝓝 (L ξ)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_scatteringSecondHeightSymbol (2 * Real.pi * ξ)).mul_const
        (‖fourierUnitary f ξ‖ ^ 2))
    have he : (2 * Real.pi * ξ) ^ 2 / 2 * ‖fourierUnitary f ξ‖ ^ 2 =
        (1 / 2 : ℝ) * ((2 * Real.pi * ξ) ^ 2 * ‖fourierUnitary f ξ‖ ^ 2) := by ring
    simpa only [Function.comp_def, he, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] using h
  have he : (∫⁻ ξ, L ξ) = ENNReal.ofReal (1 / 2 : ℝ) * scatteringDirichletEnergy f :=
    lintegral_const_mul _ hb
  simp_rw [scatteringSecondHeightEnergy_eq_fourier]
  change Tendsto (fun N => ∫⁻ ξ, F N ξ) atTop _
  rw [← he]
  by_cases hfin : scatteringDirichletEnergy f ≠ ∞
  · exact tendsto_lintegral_of_dominated_convergence B hm
      (fun N => Eventually.of_forall fun ξ => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (scatteringSecondHeightSymbol_le N _) (sq_nonneg _)))
      hfin (Eventually.of_forall hlim)
  · have htop : (∫⁻ ξ, L ξ) = ∞ := by
      rw [he, not_ne_iff.mp hfin, ENNReal.mul_top]
      simp
    have hl : (∫⁻ ξ, L ξ) ≤ liminf (fun N => ∫⁻ ξ, F N ξ) atTop := by
      have h := lintegral_liminf_le (μ := volume) (u := atTop) hm
      simpa only [(hlim _).liminf_eq] using h
    exact tendsto_of_le_liminf_of_limsup_le hl (by rw [htop]; exact le_top)

/-- Finiteness of the geometric second-height coefficient is precisely Fourier H¹ regularity. -/
theorem scatteringDirichletEnergy_ne_top_iff (f : SoninL2) :
    scatteringDirichletEnergy f ≠ ∞ ↔ f ∈ fourierL2H1 := by
  have hm : AEStronglyMeasurable (fun ξ : ℝ =>
      (2 * Real.pi * ξ) ^ 2 * ‖fourierUnitary f ξ‖ ^ 2) volume :=
    (by fun_prop : Continuous fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (fourierUnitary f)).norm.pow 2)
  rw [scatteringDirichletEnergy, lintegral_ofReal_ne_top_iff_integrable hm
    (Eventually.of_forall fun ξ => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    mem_fourierL2SobolevDomain_iff]
  simp only [pow_one]
  have hg : AEStronglyMeasurable (fun ξ : ℝ => (ξ : ℂ) * fourierUnitary f ξ) volume :=
    Complex.continuous_ofReal.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  rw [memLp_two_iff_integrable_sq_norm hg]
  have he (ξ : ℝ) : ‖(ξ : ℂ) * fourierUnitary f ξ‖ ^ 2 = ξ ^ 2 * ‖fourierUnitary f ξ‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  constructor
  · intro h
    have hc := h.const_mul ((2 * Real.pi) ^ 2)⁻¹
    refine hc.congr (Eventually.of_forall fun ξ => ?_)
    dsimp only
    field_simp
  · intro h
    exact (h.const_mul ((2 * Real.pi) ^ 2)).congr (Eventually.of_forall fun ξ => by ring)

private theorem integrable_criticalDefect (f : SoninL2) (hf : criticalGreenEnergy f ≠ ∞) :
    IntegrableOn (fun t => archLevyDensity t * ccmActualHeadTranslationDefect t f) (Ioi 0) := by
  have hm : Measurable fun t => archLevyDensity t * ccmActualHeadTranslationDefect t f := by
    have hd : Continuous fun t => ccmActualHeadTranslationDefect t f :=
      ((continuous_logTranslationCLM f).sub continuous_const).norm.pow 2
    exact (by unfold archLevyDensity; fun_prop : Measurable archLevyDensity).mul hd.measurable
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable ?_).mp hf
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (archLevyDensity_pos ht).le (sq_nonneg _)

private theorem secondHeight_integral_identity (N : ℕ) (f : SoninL2)
    (hf : criticalGreenEnergy f ≠ ∞) :
    scatteringSecondHeightEnergy N f = ENNReal.ofReal (heightScale N ^ 2 *
      ((criticalGreenEnergy f).toReal - scatteringJumpEnergy (N + 1) f)) := by
  have hi := integrable_criticalDefect f hf
  have hj := integrable_scatteringJumpEnergy (N + 1) f
  have hcrit : (criticalGreenEnergy f).toReal =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * ccmActualHeadTranslationDefect t f := by
    rw [criticalGreenEnergy, ← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [ENNReal.toReal_ofReal]
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (archLevyDensity_pos ht).le (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (archLevyDensity_pos ht).le (sq_nonneg _)
  have he (t : ℝ) (ht : 0 < t) :
      heightScale N ^ 2 * (archLevyDensity t * ccmActualHeadTranslationDefect t f -
        scatteringCutoffKernel (N + 1) t * ccmActualHeadTranslationDefect t f) =
      heightScale N ^ 2 * Real.exp (-heightScale N * t) * archLevyDensity t *
        ccmActualHeadTranslationDefect t f := by
    rw [scatteringCutoffKernel_eq (N + 1) ht]
    simp only [Nat.cast_add, Nat.cast_one, heightScale]
    ring
  have hint : IntegrableOn (fun t => heightScale N ^ 2 * Real.exp (-heightScale N * t) *
      archLevyDensity t * ccmActualHeadTranslationDefect t f) (Ioi 0) := by
    refine ((hi.sub hj).const_mul (heightScale N ^ 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact he t ht
  rw [hcrit, scatteringJumpEnergy, ← integral_sub hi hj, ← integral_const_mul]
  have hint_eq : (∫ t in Ioi (0 : ℝ), heightScale N ^ 2 *
      (archLevyDensity t * ccmActualHeadTranslationDefect t f -
        scatteringCutoffKernel (N + 1) t * ccmActualHeadTranslationDefect t f)) =
      ∫ t in Ioi (0 : ℝ), heightScale N ^ 2 * Real.exp (-heightScale N * t) *
        archLevyDensity t * ccmActualHeadTranslationDefect t f :=
    setIntegral_congr_fun measurableSet_Ioi he
  rw [hint_eq, ofReal_integral_eq_lintegral_ofReal hint]
  · rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (archLevyDensity_pos ht).le) (sq_nonneg _)

/-- The geometric second-height defect after removing the exact Robin mass drift. -/
def scatteringSecondHeightDefect (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ 2 * ((ccmRestrictedWeilForm a u u).re -
    scatteringWeilEnergy a (N + 1) (ccmArchimedeanFormToAperture a u) +
    (scatteringMassCoefficient (N + 1) - 2 * gammaHardyPhaseRate 0) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2)

private theorem criticalWeil_identity (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a u u).re =
      (criticalGreenEnergy (ccmArchimedeanFormToAperture a u).1).toReal +
      2 * gammaHardyPhaseRate 0 * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
      (inner ℂ (ccmPolarOperator a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re -
      (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  let f := ccmArchimedeanFormToAperture a u
  have hsu : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  have hsf : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
    norm_cast
  change (ccmRestrictedWeilForm a u u).re = (criticalGreenEnergy f.1).toReal +
    2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 + (inner ℂ (ccmPolarOperator a f) f).re -
      (inner ℂ (ccmFinitePrimeOperator a f) f).re
  rw [ccmRestrictedWeilForm, Complex.add_re, hsu,
    ← criticalGreenEnergy_form_norm a u]
  rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re,
    Complex.mul_re, hsf]
  unfold ccmArchimedeanRemainderScalar
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring
/-- The finite arithmetic remainder in the second-height diagonal defect. -/
def primeSecondHeightTail (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    (heightScale N ^ 2 * ((n : ℝ)⁻¹) ^ (N + 1)) *
      (ArithmeticFunction.vonMangoldt n * (inner ℂ (ccmPrimeTransportOperator a n f) f).re)

private theorem tendsto_primeSecondHeightTail (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    Tendsto (primeSecondHeightTail a f) atTop (𝓝 0) := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
      Tendsto (fun N => (heightScale N ^ 2 * ((n : ℝ)⁻¹) ^ (N + 1)) *
        (ArithmeticFunction.vonMangoldt n * (inner ℂ (ccmPrimeTransportOperator a n f) f).re))
        atTop (𝓝 0) := by
    have hn1 : (1 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (Finset.mem_Icc.mp hn).1)
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ)
      (Real.log n) (Real.log_pos hn1)).comp tendsto_heightScale
    have he (N : ℕ) : Real.exp (-Real.log (n : ℝ) * heightScale N) =
        ((n : ℝ)⁻¹) ^ (N + 1) := by
      rw [show -Real.log (n : ℝ) * heightScale N = ((N + 1 : ℕ) : ℝ) *
        (-Real.log (n : ℝ)) by simp only [heightScale, Nat.cast_add, Nat.cast_one]; ring,
        Real.exp_nat_mul, Real.exp_neg, Real.exp_log (zero_lt_one.trans hn1)]
    simp only [Function.comp_def, Real.rpow_two, he] at h
    simpa only [zero_mul] using h.mul_const
      (ArithmeticFunction.vonMangoldt n * (inner ℂ (ccmPrimeTransportOperator a n f) f).re)
  change Tendsto (fun N => primeSecondHeightTail a f N) _ _
  simpa only [primeSecondHeightTail, Finset.sum_const_zero] using tendsto_finsetSum _ hterm

private theorem primeSecondHeightTail_eq (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (N : ℕ) :
    primeSecondHeightTail a f N = heightScale N ^ 2 *
      ((inner ℂ (ccmFinitePrimeOperator a f) f).re -
        (inner ℂ (scatteringPrimeOperator a (N + 1) f) f).re) := by
  unfold primeSecondHeightTail ccmFinitePrimeOperator scatteringPrimeOperator
  rw [_root_.sum_apply, _root_.sum_apply, sum_inner, sum_inner, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [_root_.smul_apply, _root_.smul_apply, inner_smul_left, inner_smul_left,
    Complex.conj_ofReal, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold scatteringHeightMangoldt
  ring

/-- The sole difference between the geometric height defect and its positive jump tail
is an explicit finite-prime correction. -/
theorem scatteringSecondHeightDefect_eq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    scatteringSecondHeightDefect a u N =
      (scatteringSecondHeightEnergy N (ccmArchimedeanFormToAperture a u).1).toReal -
        primeSecondHeightTail a (ccmArchimedeanFormToAperture a u) N := by
  let f := ccmArchimedeanFormToAperture a u
  have hf : criticalGreenEnergy f.1 ≠ ∞ :=
    (criticalGreenEnergy_ne_top_iff_form_range a f).mpr ⟨u, rfl⟩
  have hj : 0 ≤ heightScale N ^ 2 *
      ((criticalGreenEnergy f.1).toReal - scatteringJumpEnergy (N + 1) f.1) := by
    have hle : ENNReal.ofReal (scatteringJumpEnergy (N + 1) f.1) ≤ criticalGreenEnergy f.1 := by
      apply ge_of_tendsto (tendsto_scatteringJumpEnergy_extended f.1)
      filter_upwards [eventually_ge_atTop (N + 1)] with M hM
      apply ENNReal.ofReal_le_ofReal
      apply integral_mono_ae (integrable_scatteringJumpEnergy _ _) (integrable_scatteringJumpEnergy _ _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [scatteringCutoffKernel_eq _ ht, scatteringCutoffKernel_eq _ ht]
      apply mul_le_mul_of_nonneg_right _ (archLevyDensity_pos ht).le
      have hNM : (N + 1 : ℝ) ≤ M := by exact_mod_cast hM
      have he := Real.exp_le_exp.mpr
        (show -(M : ℝ) * t ≤ -((N : ℝ) + 1) * t from
          mul_le_mul_of_nonneg_right (neg_le_neg hNM) ht.le)
      simpa only [Nat.cast_add, Nat.cast_one] using sub_le_sub_left he 1
    have h := ENNReal.toReal_mono hf hle
    rw [ENNReal.toReal_ofReal (scatteringJumpEnergy_nonneg _ _)] at h
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr h)
  rw [secondHeight_integral_identity N f.1 hf, ENNReal.toReal_ofReal hj,
    primeSecondHeightTail_eq]
  unfold scatteringSecondHeightDefect scatteringWeilEnergy
  rw [criticalWeil_identity]
  change heightScale N ^ 2 * _ = _
  ring

private theorem secondHeight_ne_top_form (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (N : ℕ) :
    scatteringSecondHeightEnergy N (ccmArchimedeanFormToAperture a u).1 ≠ ∞ := by
  rw [secondHeight_integral_identity N _
    ((criticalGreenEnergy_ne_top_iff_form_range a _).mpr ⟨u, rfl⟩)]
  exact ENNReal.ofReal_ne_top

/-- On the physical H¹ subdomain, the renormalized raw-tower defect has the exact Dirichlet limit. -/
theorem tendsto_scatteringSecondHeightDefect_finite (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a)
    (hu : (ccmArchimedeanFormToAperture a u).1 ∈ fourierL2H1) :
    Tendsto (scatteringSecondHeightDefect a u) atTop
      (𝓝 ((scatteringDirichletEnergy (ccmArchimedeanFormToAperture a u).1).toReal / 2)) := by
  have hf := (scatteringDirichletEnergy_ne_top_iff _).mpr hu
  have hfin : ENNReal.ofReal (1 / 2 : ℝ) *
      scatteringDirichletEnergy (ccmArchimedeanFormToAperture a u).1 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf
  have h := (ENNReal.tendsto_toReal hfin).comp
    (tendsto_scatteringSecondHeightEnergy (ccmArchimedeanFormToAperture a u).1)
  have hsub := h.sub (tendsto_primeSecondHeightTail a (ccmArchimedeanFormToAperture a u))
  simp only [Function.comp_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), sub_zero] at hsub
  convert hsub using 1
  · funext N
    exact scatteringSecondHeightDefect_eq a u N
  · congr 1
    ring

/-- The geometric height defect diverges on every complete Weil state outside physical H¹. -/
theorem tendsto_scatteringSecondHeightDefect_atTop (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a)
    (hu : (ccmArchimedeanFormToAperture a u).1 ∉ fourierL2H1) :
    Tendsto (scatteringSecondHeightDefect a u) atTop atTop := by
  have hf : scatteringDirichletEnergy (ccmArchimedeanFormToAperture a u).1 = ∞ := by
    by_contra h
    exact hu ((scatteringDirichletEnergy_ne_top_iff _).mp h)
  have h := tendsto_scatteringSecondHeightEnergy (ccmArchimedeanFormToAperture a u).1
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [hf, ENNReal.mul_top hhalf] at h
  have ht : Tendsto (fun N =>
      (scatteringSecondHeightEnergy N (ccmArchimedeanFormToAperture a u).1).toReal)
      atTop atTop := by
    apply ENNReal.tendsto_ofReal_nhds_top.mp
    simpa only [ENNReal.ofReal_toReal (secondHeight_ne_top_form a u _)] using h
  have hp := (tendsto_primeSecondHeightTail a (ccmArchimedeanFormToAperture a u)).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  apply tendsto_atTop.2
  intro b
  filter_upwards [ht.eventually_ge_atTop (b + 1), hp] with N hN hP
  rw [scatteringSecondHeightDefect_eq]
  linarith only [hN, hP]

/-- A finite second-order geometric height limit exists exactly at the physical H¹ threshold. -/
theorem finite_scatteringSecondHeightDefect_limit_iff (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (∃ L : ℝ, Tendsto (scatteringSecondHeightDefect a u) atTop (𝓝 L)) ↔
      (ccmArchimedeanFormToAperture a u).1 ∈ fourierL2H1 := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra hu
    have hinf := tendsto_scatteringSecondHeightDefect_atTop a u hu
    have hsmall := hL.eventually (Iio_mem_nhds (show L < L + 1 by linarith only))
    obtain ⟨N, hN, hNL⟩ := (hinf.eventually_ge_atTop (L + 1)).and hsmall |>.exists
    exact (not_lt_of_ge hN) hNL
  · intro hu
    exact ⟨_, tendsto_scatteringSecondHeightDefect_finite a u hu⟩

open scoped FourierTransform

/-- The coefficient is the literal physical derivative energy on smooth interior sources. -/
theorem scatteringDirichletEnergy_smooth {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    scatteringDirichletEnergy (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 =
      ENNReal.ofReal (∫ x : ℝ, ‖deriv u x‖ ^ 2) := by
  let g := u.toSchwartz
  let d := SchwartzMap.derivCLM ℂ ℂ g
  have hf : (fourierUnitary (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 : ℝ → ℂ)
      =ᵐ[volume] 𝓕 (g : ℝ → ℂ) := by
    change (fourierUnitary (ccmArchimedeanFourierToTime u.toCCMFormVector.1) : ℝ → ℂ) =ᵐ[volume] _
    rw [fourierUnitary_ccmArchimedeanFourierToTime]
    exact (ccmArchimedeanWeightedToL2_coeFn u.toCCMFormVector.1).trans
      u.toCCMFormVector_fourier_coeFn
  have hd (ξ : ℝ) : ‖𝓕 (d : ℝ → ℂ) ξ‖ ^ 2 =
      (2 * Real.pi * ξ) ^ 2 * ‖𝓕 (g : ℝ → ℂ) ξ‖ ^ 2 := by
    have h := congrFun (Real.fourier_deriv g.integrable g.differentiable d.integrable) ξ
    change 𝓕 (d : ℝ → ℂ) ξ = _ at h
    rw [h]
    simp only [smul_eq_mul]
    rw [show (2 * Real.pi * I * (ξ : ℂ)) = I * ((2 * Real.pi * ξ : ℝ) : ℂ) by push_cast; ring]
    rw [norm_mul, norm_mul, norm_I, one_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hi : Integrable (fun ξ : ℝ => ‖𝓕 (d : ℝ → ℂ) ξ‖ ^ 2) := by
    simpa only [SchwartzMap.fourier_coe] using
      ((𝓕 d : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have he : scatteringDirichletEnergy (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖𝓕 (d : ℝ → ℂ) ξ‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hf] with ξ hξ
    rw [hξ, hd]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ξ => sq_nonneg _),
    GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq d.integrable (d.memLp 2 volume)]
  rfl

/-- The actual geometric scattering diagonal, with its exact Robin drift removed, reads
half the physical Dirichlet energy at second order in inverse height. -/
theorem tendsto_rawScattering_secondHeight {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2 *
      ((ccmRestrictedWeilForm a u.toCCMFormVector u.toCCMFormVector).re -
        (RawGeometry.energy u (N + 1)).re +
        (scatteringMassCoefficient (N + 1) - 2 * gammaHardyPhaseRate 0) *
          ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2))
      atTop (𝓝 ((∫ x : ℝ, ‖deriv u x‖ ^ 2) / 2)) := by
  have hu : (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 ∈ fourierL2H1 := by
    apply (scatteringDirichletEnergy_ne_top_iff _).mp
    rw [scatteringDirichletEnergy_smooth]
    exact ENNReal.ofReal_ne_top
  have h := tendsto_scatteringSecondHeightDefect_finite a u.toCCMFormVector hu
  rw [scatteringDirichletEnergy_smooth, ENNReal.toReal_ofReal
    (integral_nonneg fun x => sq_nonneg ‖deriv u x‖)] at h
  change Tendsto (fun N => scatteringSecondHeightDefect a u.toCCMFormVector N) _ _ at h
  simpa only [scatteringSecondHeightDefect, rawEnergy_smooth_eq_scatteringWeilEnergy] using h

#print axioms scatteringSecondHeightEnergy_eq_fourier
#print axioms tendsto_scatteringSecondHeightEnergy
#print axioms scatteringDirichletEnergy_ne_top_iff
#print axioms scatteringSecondHeightDefect_eq
#print axioms finite_scatteringSecondHeightDefect_limit_iff
#print axioms tendsto_scatteringSecondHeightDefect_atTop
#print axioms scatteringDirichletEnergy_smooth
#print axioms tendsto_rawScattering_secondHeight

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
