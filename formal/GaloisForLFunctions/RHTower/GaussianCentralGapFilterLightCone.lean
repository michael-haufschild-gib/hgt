import GaloisForLFunctions.RHTower.GaussianCentralGapMeanSquareBudget
import GaloisForLFunctions.RHTower.GaussianCentralGapZeroFreeRegionBudget
import GaloisForLFunctions.HTGeometry.GaussianLightConeAmplification
import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction

/-!
# The Gaussian-filtered central gap and its light cone

Let `G(u) = P_½(e^{-u}) − C_½(e^{-u})` be the central Gaussian prime gap in the logarithmic
variable.  For `ε > 0` and a height parameter `τ` filter it with the Gaussian window centred at
`u = 2ε` of variance `ε`, modulated at frequency `τ`:

  `F(ε, τ) = ∫_{u > 0} G(u) exp(−(u − 2ε)²/(2ε) − iτ(u − 2ε)) du`.

* **Filtered zero expansion** (`exists_norm_filteredGap_add_zeroSeries_le`).
  `F(ε, τ) = −√(2πε) Σ_ρ ½Γ((ρ−½)/2) e^{−ε w_ρ(τ)} + O(√ε)`, uniformly in `τ`, with the
  light-cone exponent `w_ρ(τ) = −(2a + (a − iτ)²/2)`, `a = (ρ−½)/2`.
* **Light cone.**  For a critical zero `Re w = (γ/2 − τ)²/2 ≥ 0`.  For a zero with `β > ½` at height
  `2τ`, `Re w = −((β−½) + (β−½)²/8) < 0`; the light cone `{Re w < 0}` at fixed `τ` is finite.
* **Criterion** (`riemannHypothesis_iff_filteredCentralGap_isBigO`).  RH holds iff for every height
  `τ` the filtered gap is `O(√ε)` on `ε ≥ 1`.  The converse direction is light-cone amplification
  (`HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg`) applied at the height of an off-line zero.

The Gaussian window in the scale variable localizes the Gaussian prime gap in height: it reads the
zeros within `O(ε^{-1/2})` of height `2τ`, and amplifies an off-line zero there by
`exp(ε((β−½) + (β−½)²/8))`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- The filter kernel `exp(−(u − 2ε)²/(2ε) − iτ(u − 2ε))`. -/
def gaussianFilterKernel (ε τ u : ℝ) : ℂ :=
  Complex.exp (-(((u - 2 * ε) ^ 2 / (2 * ε) : ℝ) : ℂ) - (τ : ℂ) * I * ((u - 2 * ε : ℝ) : ℂ))

theorem norm_gaussianFilterKernel (ε τ u : ℝ) :
    ‖gaussianFilterKernel ε τ u‖ = Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) := by
  rw [gaussianFilterKernel, Complex.norm_exp, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  have h : ((τ : ℂ) * I * ((u - 2 * ε : ℝ) : ℂ)).re = 0 := by simp
  rw [h, sub_zero]

theorem continuous_gaussianFilterKernel (ε τ : ℝ) : Continuous (gaussianFilterKernel ε τ) := by
  unfold gaussianFilterKernel
  fun_prop

/-- The real Gaussian window is integrable with total mass `√(2πε)`. -/
theorem integrable_gaussianWindow {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (2 * ε)) (by positivity)).comp_sub_right (2 * ε)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  congr 1
  field_simp

theorem integral_gaussianWindow {ε : ℝ} (hε : 0 < ε) :
    ∫ u : ℝ, Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) = Real.sqrt (2 * Real.pi * ε) := by
  have h := integral_gaussian (1 / (2 * ε))
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => Real.exp (-(1 / (2 * ε)) * u ^ 2)) (2 * ε)
  rw [← hshift] at h
  rw [show (fun u : ℝ => Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) =
      fun u : ℝ => Real.exp (-(1 / (2 * ε)) * (u - 2 * ε) ^ 2) by
    funext u; congr 1; field_simp, h]
  congr 1
  field_simp

theorem integrable_gaussianFilterKernel {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    Integrable (gaussianFilterKernel ε τ) := by
  refine (integrable_gaussianWindow hε).mono'
    (continuous_gaussianFilterKernel ε τ).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_gaussianFilterKernel]

/-- The filtered exponential as a complex quadratic exponential. -/
theorem cexp_mul_gaussianFilterKernel {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (a : ℂ) (u : ℝ) :
    Complex.exp (a * u) * gaussianFilterKernel ε τ u =
      Complex.exp (-((1 / (2 * ε) : ℝ) : ℂ) * (u : ℂ) ^ 2 + (a + 2 - (τ : ℂ) * I) * u +
        (-(2 * ε : ℝ) + 2 * (τ : ℂ) * I * (ε : ℂ))) := by
  rw [gaussianFilterKernel, ← Complex.exp_add]
  congr 1
  have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  push_cast
  field_simp
  ring

/-- **Full-line Gaussian filter of an exponential.**
`∫ e^{au} K_{ε,τ}(u) du = √(2πε) exp(ε(2a + (a − iτ)²/2))`. -/
theorem integral_cexp_mul_gaussianFilterKernel {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (a : ℂ) :
    ∫ u : ℝ, Complex.exp (a * u) * gaussianFilterKernel ε τ u =
      ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        Complex.exp ((ε : ℂ) * (2 * a + (a - (τ : ℂ) * I) ^ 2 / 2)) := by
  simp_rw [cexp_mul_gaussianFilterKernel hε τ a]
  have hb : 0 < (((1 / (2 * ε) : ℝ) : ℂ)).re := by simp; positivity
  have h := integral_cexp_quadratic (b := -(((1 / (2 * ε) : ℝ) : ℂ))) (by simpa using hb)
    (a + 2 - (τ : ℂ) * I) (-(2 * ε : ℝ) + 2 * (τ : ℂ) * I * (ε : ℂ))
  rw [h]
  have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  have hpi : (Real.pi : ℂ) / -(-(((1 / (2 * ε) : ℝ) : ℂ))) = ((2 * Real.pi * ε : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [hpi, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
    ← Real.sqrt_eq_rpow]
  congr 2
  push_cast
  field_simp
  ring

theorem integrable_cexp_mul_gaussianFilterKernel {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (a : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (a * u) * gaussianFilterKernel ε τ u) := by
  simp_rw [cexp_mul_gaussianFilterKernel hε τ a]
  have hb : 0 < (((1 / (2 * ε) : ℝ) : ℂ)).re := by simp; positivity
  exact integrable_cexp_quadratic hb _ _

/-- The left tail of the filtered exponential is `≤ e^{-2ε}` when `Re a ≥ −¼`. -/
theorem norm_integral_Iic_cexp_mul_gaussianFilterKernel_le {ε : ℝ} (hε : 0 < ε) (τ : ℝ) {a : ℂ}
    (ha : -(1 / 4) ≤ a.re) :
    ‖∫ u in Iic (0 : ℝ), Complex.exp (a * u) * gaussianFilterKernel ε τ u‖ ≤ Real.exp (-2 * ε) := by
  have hbound : ∀ u ∈ Iic (0 : ℝ), ‖Complex.exp (a * u) * gaussianFilterKernel ε τ u‖ ≤
      Real.exp (-2 * ε) * Real.exp ((7 / 4) * u) := by
    intro u hu
    have hu0 : u ≤ 0 := hu
    rw [norm_mul, norm_gaussianFilterKernel, Complex.norm_exp, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hre : (a * (u : ℂ)).re = a.re * u := by simp
    rw [hre]
    have h1 : a.re * u ≤ -(1 / 4) * u := by nlinarith
    have h2 : 0 ≤ u ^ 2 / (2 * ε) := by positivity
    have h3 : (u - 2 * ε) ^ 2 / (2 * ε) = u ^ 2 / (2 * ε) - 2 * u + 2 * ε := by
      field_simp; ring
    rw [h3]
    linarith
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-2 * ε) * Real.exp ((7 / 4) * u)) (Iic 0) := by
    exact (integrableOn_exp_mul_Iic (show (0 : ℝ) < 7 / 4 by norm_num) 0).const_mul _
  calc ‖∫ u in Iic (0 : ℝ), Complex.exp (a * u) * gaussianFilterKernel ε τ u‖
      ≤ ∫ u in Iic (0 : ℝ), Real.exp (-2 * ε) * Real.exp ((7 / 4) * u) :=
        norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Iic hbound)
    _ = Real.exp (-2 * ε) * (4 / 7) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_exp_mul_Iic (show (0 : ℝ) < 7 / 4 by norm_num) 0]
        norm_num
    _ ≤ Real.exp (-2 * ε) := by
        have := Real.exp_pos (-2 * ε); nlinarith

/-! ## The filtered gap -/

/-- The Gaussian-filtered central gap `F(ε, τ) = ∫_{u>0} G(u) K_{ε,τ}(u) du`. -/
def gaussianFilteredCentralGap (ε τ : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (gaussianCentralGapLog u : ℂ) * gaussianFilterKernel ε τ u

/-- The light-cone exponent `w_ρ(τ) = −(2a + (a − iτ)²/2)` with `a = (ρ − ½)/2`. -/
def zeroLightConeExponent (τ : ℝ) (q : XiZeroCopy) : ℂ :=
  -(2 * ((xiZero q - 1 / 2) / 2) + ((xiZero q - 1 / 2) / 2 - (τ : ℂ) * I) ^ 2 / 2)

theorem re_zeroLightConeExponent (τ : ℝ) (q : XiZeroCopy) :
    (zeroLightConeExponent τ q).re = -(((xiZero q).re - 1 / 2) +
      (((xiZero q).re - 1 / 2) ^ 2 / 4 - ((xiZero q).im / 2 - τ) ^ 2) / 2) := by
  simp [zeroLightConeExponent, sq]
  ring

theorem neg_re_zeroLightConeExponent_le (τ : ℝ) (q : XiZeroCopy) :
    -(zeroLightConeExponent τ q).re ≤ 1 := by
  rw [re_zeroLightConeExponent]
  have hb := re_xiZero_sub_half_bounds q
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
  nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]

theorem norm_cexp_neg_mul_zeroLightConeExponent_le {ε : ℝ} (hε : 0 ≤ ε) (τ : ℝ)
    (q : XiZeroCopy) :
    ‖Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤ Real.exp ε := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have h := neg_re_zeroLightConeExponent_le τ q
  have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re = ε * -(zeroLightConeExponent τ q).re := by
    simp
  rw [hre]
  nlinarith

/-- The pointwise remainder: `G(u) + Σ_ρ ½Γ((ρ−½)/2) e^{(ρ−½)u/2}` is bounded on `u > 0`. -/
theorem exists_norm_gaussianCentralGapLog_add_zeroSeries_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      ‖(gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
          zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)‖ ≤ C := by
  have hSs : Summable fun q : XiZeroCopy => ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 :=
    summable_norm_inv_xiZero_sub_half_sq
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set A₀ : ℝ := ‖gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ with hA₀
  have hA0 : 0 ≤ A₀ := norm_nonneg _
  refine ⟨A₀ + 31 + 4 * S, by positivity, fun u hu => ?_⟩
  set y : ℝ := Real.exp (-u) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hexp := gaussianCentralGap_eq_archimedean_sub_zeroSeries hy0
  have hZ : (∑' q : XiZeroCopy, zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) =
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u) := by
    refine tsum_congr fun q => ?_
    rw [hy, exp_neg_cpow_eq_cexp_mul]
    congr 2
    ring
  have hb : ∀ q : XiZeroCopy, ‖criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ ≤
      4 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    refine (norm_criticalZeroGerm_sub_zeroBohr_le hy0 q).trans ?_
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    gcongr
    linarith
  have hsR : Summable fun q : XiZeroCopy => ‖criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hSs.mul_left 4)
  have hsumR : ‖∑' q : XiZeroCopy, (criticalZeroGerm y q -
      zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)))‖ ≤ 4 * S := by
    refine (norm_tsum_le_tsum_norm hsR).trans ?_
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hb hsR (hSs.mul_left 4)
  have hMB : ‖gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ)‖ ≤ A₀ + 31 := by
    have h := norm_gaussianArchimedeanCurrent_half_sub_MB_le hy0 hy1
    have hs : Real.sqrt y ≤ 1 := Real.sqrt_le_one.2 hy1
    have h2 := norm_sub_norm_le (gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ))
      (gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ))
    rw [norm_sub_rev] at h2
    nlinarith
  have hg : (gaussianCentralGapLog u : ℂ) =
      ((gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y : ℝ) : ℂ) := by
    rw [gaussianCentralGapLog]
  rw [hg, hexp, hZ]
  have hsum : gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) -
      (∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)) -
      (∑' q : XiZeroCopy, (criticalZeroGerm y q -
        zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2)))) +
      ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u) =
      gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) - ∑' q : XiZeroCopy, (criticalZeroGerm y q -
        zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))) := by ring
  rw [hsum]
  have := norm_sub_le (gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ)) (∑' q : XiZeroCopy,
    (criticalZeroGerm y q - zeroBohrAmplitude q * (y : ℂ) ^ (-((xiZero q - 1 / 2) / 2))))
  linarith

/-- The weighted Gaussian window `e^{u/4} e^{-(u−2ε)²/(2ε)}` is integrable. -/
theorem integrable_exp_quarter_mul_gaussianWindow {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) := by
  have h := ((integrable_exp_neg_mul_sq (b := 1 / (4 * ε)) (by positivity)).comp_sub_right
    (2 * ε)).const_mul (Real.exp (9 * ε / 16))
  refine h.mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have key : u / 4 + -((u - 2 * ε) ^ 2 / (2 * ε)) + ((u - 2 * ε - ε / 2) ^ 2 / (4 * ε)) =
      9 * ε / 16 + -(1 / (4 * ε)) * (u - 2 * ε) ^ 2 := by
    field_simp; ring
  have hnn : 0 ≤ (u - 2 * ε - ε / 2) ^ 2 / (4 * ε) := by positivity
  linarith

theorem summable_norm_zeroBohrAmplitude' :
    Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude

theorem re_xiZero_sub_half_div_two_le (q : XiZeroCopy) :
    -(1 / 4) ≤ ((xiZero q - 1 / 2) / 2).re ∧ ((xiZero q - 1 / 2) / 2).re ≤ 1 / 4 := by
  have hb := re_xiZero_sub_half_bounds q
  have h : ((xiZero q - 1 / 2) / 2).re = (xiZero q - 1 / 2).re / 2 := by simp
  rw [h]
  constructor <;> linarith [hb.1, hb.2]

/-- The left tail `∫_{u ≤ 0} e^{(ρ−½)u/2} K_{ε,τ}(u) du` of one filtered zero term. -/
def filteredZeroTail (ε τ : ℝ) (q : XiZeroCopy) : ℂ :=
  ∫ u in Iic (0 : ℝ), Complex.exp ((xiZero q - 1 / 2) / 2 * u) * gaussianFilterKernel ε τ u

theorem norm_filteredZeroTail_le {ε : ℝ} (hε : 0 < ε) (τ : ℝ) (q : XiZeroCopy) :
    ‖filteredZeroTail ε τ q‖ ≤ Real.exp (-2 * ε) :=
  norm_integral_Iic_cexp_mul_gaussianFilterKernel_le hε τ (re_xiZero_sub_half_div_two_le q).1

/-- `(G + Σ_ρ c_ρ e^{(ρ−½)u/2}) K_{ε,τ}` is integrable on `u > 0`. -/
theorem integrableOn_gapAddZeroSeries_mul_kernel {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    IntegrableOn (fun u : ℝ => ((gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)) *
        gaussianFilterKernel ε τ u) (Ioi 0) := by
  obtain ⟨C₀, -, hC₀b⟩ := exists_norm_gaussianCentralGapLog_add_zeroSeries_le
  have hZmeas : AEStronglyMeasurable (fun u : ℝ => ∑' q : XiZeroCopy,
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)) (volume.restrict (Ioi 0)) :=
    AEStronglyMeasurable.tsum fun q => (by fun_prop : Continuous fun u : ℝ =>
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)).aestronglyMeasurable
  refine ((integrable_gaussianWindow hε).const_mul C₀).integrableOn.mono'
    ((((Complex.continuous_ofReal.comp continuous_gaussianCentralGapLog).aestronglyMeasurable.add
      hZmeas)).mul (continuous_gaussianFilterKernel ε τ).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, norm_gaussianFilterKernel]
  exact mul_le_mul_of_nonneg_right (hC₀b u hu) (Real.exp_pos _).le

/-- **Filtered zero identity.**
`F(ε, τ) + √(2πε) Σ_ρ c_ρ e^{−ε w_ρ(τ)} = ∫_{u>0} (G + Σ_ρ c_ρ e^{(ρ−½)u/2}) K + Σ_ρ c_ρ T_ρ`,
with `T_ρ` the left tail of the filtered exponential. -/
theorem gaussianFilteredCentralGap_add_zeroSeries_eq {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q *
          Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) =
      (∫ u in Ioi (0 : ℝ), ((gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
          zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)) *
            gaussianFilterKernel ε τ u) +
        ∑' q : XiZeroCopy, zeroBohrAmplitude q * filteredZeroTail ε τ q := by
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set K : ℝ → ℂ := gaussianFilterKernel ε τ with hK
  set a : XiZeroCopy → ℂ := fun q => (xiZero q - 1 / 2) / 2 with ha
  set Z : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) with hZ
  have hKc : Continuous K := continuous_gaussianFilterKernel ε τ
  -- termwise bounds
  have hterm : ∀ q : XiZeroCopy, ∀ u : ℝ, 0 ≤ u →
      ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ))‖ ≤ ‖zeroBohrAmplitude q‖ * Real.exp (u / 4) := by
    intro q u hu
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have hre : (a q * (u : ℂ)).re = (a q).re * u := by simp
    rw [hre]
    nlinarith [(re_xiZero_sub_half_div_two_le q).2]
  -- `Z K` on `Ioi 0`
  have hZmeas : AEStronglyMeasurable Z (volume.restrict (Ioi 0)) :=
    AEStronglyMeasurable.tsum fun q => (by fun_prop : Continuous fun u : ℝ =>
      zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ))).aestronglyMeasurable
  have hZbound : ∀ u : ℝ, 0 < u → ‖Z u‖ ≤ A * Real.exp (u / 4) := by
    intro u hu
    have hs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hterm q u hu.le)
        (hAs.mul_right _)
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    rw [hA, ← tsum_mul_right]
    exact Summable.tsum_le_tsum (fun q => hterm q u hu.le) hs (hAs.mul_right _)
  have hmaj : IntegrableOn (fun u : ℝ => A * (Real.exp (u / 4) *
      Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))))) (Ioi 0) :=
    ((integrable_exp_quarter_mul_gaussianWindow hε).const_mul A).integrableOn
  have hZK : IntegrableOn (fun u => Z u * K u) (Ioi 0) := by
    refine hmaj.mono' (hZmeas.mul hKc.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, hK, norm_gaussianFilterKernel]
    have := hZbound u hu
    calc ‖Z u‖ * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))
        ≤ (A * Real.exp (u / 4)) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) := by gcongr
      _ = _ := by ring
  have hGZK := integrableOn_gapAddZeroSeries_mul_kernel hε τ
  -- interchange for `∫ Z K`
  have hint_q : ∀ q : XiZeroCopy, Integrable (fun u : ℝ => zeroBohrAmplitude q *
      Complex.exp (a q * (u : ℂ)) * K u) (volume.restrict (Ioi 0)) := by
    intro q
    have h := (integrable_cexp_mul_gaussianFilterKernel hε τ (a q)).const_mul (zeroBohrAmplitude q)
    refine h.integrableOn.congr_fun (fun u _ => by simp only [hK]; ring) measurableSet_Ioi
  set M : ℝ := ∫ u : ℝ, Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) with hM
  have hnorm_q : ∀ q : XiZeroCopy, ∫ u in Ioi (0 : ℝ),
      ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u‖ ≤ ‖zeroBohrAmplitude q‖ * M := by
    intro q
    have hle : ∀ u ∈ Ioi (0 : ℝ), ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u‖ ≤
        ‖zeroBohrAmplitude q‖ * (Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) := by
      intro u hu
      rw [norm_mul, hK, norm_gaussianFilterKernel]
      have := hterm q u (le_of_lt hu)
      calc ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ))‖ *
            Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))
          ≤ (‖zeroBohrAmplitude q‖ * Real.exp (u / 4)) *
            Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) := by gcongr
        _ = _ := by ring
    calc ∫ u in Ioi (0 : ℝ), ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u‖
        ≤ ∫ u in Ioi (0 : ℝ), ‖zeroBohrAmplitude q‖ *
            (Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) :=
          setIntegral_mono_on (hint_q q).norm
            ((integrable_exp_quarter_mul_gaussianWindow hε).const_mul _).integrableOn
            measurableSet_Ioi hle
      _ ≤ ∫ u : ℝ, ‖zeroBohrAmplitude q‖ *
            (Real.exp (u / 4) * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε)))) :=
          setIntegral_le_integral ((integrable_exp_quarter_mul_gaussianWindow hε).const_mul _)
            (Eventually.of_forall fun u => by positivity)
      _ = ‖zeroBohrAmplitude q‖ * M := by rw [integral_const_mul]
  have hsumint : Summable fun q : XiZeroCopy => ∫ u in Ioi (0 : ℝ),
      ‖zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u‖ :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm_q
      (hAs.mul_right M)
  have hswap : ∫ u in Ioi (0 : ℝ), Z u * K u = ∑' q : XiZeroCopy, ∫ u in Ioi (0 : ℝ),
      zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u := by
    rw [integral_tsum_of_summable_integral_norm hint_q hsumint]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [hZ]
    rw [tsum_mul_right]
  -- each zero term: full line minus the left tail
  have hsplit_q : ∀ q : XiZeroCopy, ∫ u in Ioi (0 : ℝ),
      zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u =
      zeroBohrAmplitude q * (((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) - filteredZeroTail ε τ q) := by
    intro q
    have hfull := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))
      (integrable_cexp_mul_gaussianFilterKernel hε τ (a q))
    rw [Set.compl_Ioi, integral_cexp_mul_gaussianFilterKernel hε τ (a q)] at hfull
    have hexpo : (ε : ℂ) * (2 * a q + (a q - (τ : ℂ) * I) ^ 2 / 2) =
        -(ε : ℂ) * zeroLightConeExponent τ q := by
      simp only [ha, zeroLightConeExponent]; ring
    rw [hexpo] at hfull
    have hmul : ∫ u in Ioi (0 : ℝ), zeroBohrAmplitude q * Complex.exp (a q * (u : ℂ)) * K u =
        zeroBohrAmplitude q * ∫ u in Ioi (0 : ℝ), Complex.exp (a q * (u : ℂ)) * K u := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      ring
    rw [hmul, filteredZeroTail]
    simp only [hK, ha] at hfull ⊢
    rw [← hfull]
    ring
  have hsW : Summable fun q : XiZeroCopy => zeroBohrAmplitude q *
      Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (hAs.mul_right (Real.exp ε)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_zeroLightConeExponent_le hε.le τ q)
      (norm_nonneg _)
  have hsT : Summable fun q : XiZeroCopy => zeroBohrAmplitude q * filteredZeroTail ε τ q := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_)
      (hAs.mul_right (Real.exp (-2 * ε))))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_filteredZeroTail_le hε τ q) (norm_nonneg _)
  have hZKval : ∫ u in Ioi (0 : ℝ), Z u * K u =
      ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) * (∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)) -
        ∑' q : XiZeroCopy, zeroBohrAmplitude q * filteredZeroTail ε τ q := by
    rw [hswap, tsum_congr hsplit_q, ← tsum_mul_left, ← (hsW.mul_left _).tsum_sub hsT]
    exact tsum_congr fun q => by ring
  have hF : gaussianFilteredCentralGap ε τ =
      (∫ u in Ioi (0 : ℝ), ((gaussianCentralGapLog u : ℂ) + Z u) * K u) -
        ∫ u in Ioi (0 : ℝ), Z u * K u := by
    rw [gaussianFilteredCentralGap, ← integral_sub hGZK hZK]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [hK]
    ring
  rw [hF, hZKval]
  ring

/-- **Filtered zero expansion.**  Uniformly in the height `τ`,
`‖F(ε, τ) + √(2πε) Σ_ρ ½Γ((ρ−½)/2) e^{−ε w_ρ(τ)}‖ ≤ C(√(2πε) + e^{−2ε})`. -/
theorem exists_norm_filteredGap_add_zeroSeries_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ τ : ℝ,
      ‖gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
          ∑' q : XiZeroCopy, zeroBohrAmplitude q *
            Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
        C * (Real.sqrt (2 * Real.pi * ε) + Real.exp (-2 * ε)) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_norm_gaussianCentralGapLog_add_zeroSeries_le
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨C₀ + A, by positivity, fun ε hε τ => ?_⟩
  rw [gaussianFilteredCentralGap_add_zeroSeries_eq hε τ]
  have hrest : ‖∫ u in Ioi (0 : ℝ), ((gaussianCentralGapLog u : ℂ) + ∑' q : XiZeroCopy,
      zeroBohrAmplitude q * Complex.exp ((xiZero q - 1 / 2) / 2 * u)) *
        gaussianFilterKernel ε τ u‖ ≤ C₀ * Real.sqrt (2 * Real.pi * ε) := by
    calc _ ≤ ∫ u in Ioi (0 : ℝ), C₀ * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) :=
          norm_integral_le_of_norm_le ((integrable_gaussianWindow hε).const_mul C₀).integrableOn
            (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
              rw [norm_mul, norm_gaussianFilterKernel]
              exact mul_le_mul_of_nonneg_right (hC₀b u hu) (Real.exp_pos _).le)
      _ ≤ ∫ u : ℝ, C₀ * Real.exp (-((u - 2 * ε) ^ 2 / (2 * ε))) :=
          setIntegral_le_integral ((integrable_gaussianWindow hε).const_mul C₀)
            (Eventually.of_forall fun u => by positivity)
      _ = C₀ * Real.sqrt (2 * Real.pi * ε) := by
          rw [integral_const_mul, integral_gaussianWindow hε]
  have hTsum : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * filteredZeroTail ε τ q‖ ≤
      A * Real.exp (-2 * ε) := by
    have hsT : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q * filteredZeroTail ε τ q‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_filteredZeroTail_le hε τ q) (norm_nonneg _))
        (hAs.mul_right (Real.exp (-2 * ε)))
    refine (norm_tsum_le_tsum_norm hsT).trans ?_
    rw [hA, ← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun q => ?_) hsT (hAs.mul_right _)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_filteredZeroTail_le hε τ q) (norm_nonneg _)
  have hsq : 0 ≤ Real.sqrt (2 * Real.pi * ε) := Real.sqrt_nonneg _
  have he : 0 ≤ Real.exp (-2 * ε) := (Real.exp_pos _).le
  calc _ ≤ C₀ * Real.sqrt (2 * Real.pi * ε) + A * Real.exp (-2 * ε) :=
        (norm_add_le _ _).trans (add_le_add hrest hTsum)
    _ ≤ (C₀ + A) * (Real.sqrt (2 * Real.pi * ε) + Real.exp (-2 * ε)) := by nlinarith

/-! ## The light cone and the criterion -/

theorem re_zeroLightConeExponent_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (τ : ℝ)
    (q : XiZeroCopy) : 0 ≤ (zeroLightConeExponent τ q).re := by
  have h : (xiZero q).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  rw [re_zeroLightConeExponent, h]
  nlinarith [sq_nonneg ((xiZero q).im / 2 - τ)]

/-- The light-cone exponent determines the zero. -/
theorem xiZero_eq_of_zeroLightConeExponent_eq {τ : ℝ} {q q' : XiZeroCopy}
    (h : zeroLightConeExponent τ q = zeroLightConeExponent τ q') : xiZero q = xiZero q' := by
  set b : ℂ := (xiZero q - 1 / 2) / 2 - (τ : ℂ) * I with hb
  set b' : ℂ := (xiZero q' - 1 / 2) / 2 - (τ : ℂ) * I with hb'
  have hsq : (b + 2) ^ 2 = (b' + 2) ^ 2 := by
    simp only [zeroLightConeExponent] at h
    simp only [hb, hb']
    linear_combination (-2 : ℂ) * h
  have hfac : (b - b') * (b + b' + 4) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h1 | h1
  · have : (xiZero q - 1 / 2) / 2 = (xiZero q' - 1 / 2) / 2 := by
      have := sub_eq_zero.1 h1; simp only [hb, hb'] at this; linear_combination this
    linear_combination 2 * this
  · exfalso
    have hre := congrArg Complex.re h1
    have h₁ := (re_xiZero_sub_half_div_two_le q).1
    have h₂ := (re_xiZero_sub_half_div_two_le q').1
    simp only [hb, hb', Complex.add_re, Complex.sub_re, Complex.zero_re] at hre
    have e1 : ((τ : ℂ) * I).re = 0 := by simp
    rw [e1] at hre
    norm_num at hre
    have e₁ : ((xiZero q - 1 / 2) / 2).re = ((xiZero q).re - 1 / 2) / 2 := by simp
    have e₂ : ((xiZero q' - 1 / 2) / 2).re = ((xiZero q').re - 1 / 2) / 2 := by simp
    rw [e₁] at h₁
    rw [e₂] at h₂
    linarith

theorem zeroBohrAmplitude_ne_zero (q : XiZeroCopy) : zeroBohrAmplitude q ≠ 0 := by
  rw [zeroBohrAmplitude]
  refine mul_ne_zero (by norm_num) (Complex.Gamma_ne_zero fun m hm => ?_)
  have hb := re_xiZero_sub_half_div_two_le q
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, Nat.cast_zero, neg_zero] at hm
    exact xiZero_sub_half_ne_zero q (by linear_combination 2 * hm)
  · have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    linarith [hb.1]

/-- **Criterion.**  RH holds iff for every height `τ` the Gaussian-filtered central gap is
`O(√ε)` on `ε ≥ 1`. -/
theorem riemannHypothesis_iff_filteredCentralGap_isBigO :
    RiemannHypothesis ↔ ∀ τ : ℝ, ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
      ‖gaussianFilteredCentralGap ε τ‖ ≤ C * Real.sqrt ε := by
  obtain ⟨C₀, hC₀, hexp⟩ := exists_norm_filteredGap_add_zeroSeries_le
  have hAs : Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q‖ := summable_norm_zeroBohrAmplitude
  set A : ℝ := ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hsqrt : ∀ ε : ℝ, 0 ≤ ε → Real.sqrt (2 * Real.pi * ε) = Real.sqrt (2 * Real.pi) * Real.sqrt ε :=
    fun ε hε => Real.sqrt_mul (by positivity) ε
  have hsum_le : ∀ ε : ℝ, 0 ≤ ε → ∀ τ : ℝ,
      Summable fun q : XiZeroCopy => ‖zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ := by
    intro ε hε τ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hAs.mul_right (Real.exp ε))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_zeroLightConeExponent_le hε τ q)
      (norm_nonneg _)
  constructor
  · intro hRH τ
    refine ⟨C₀ * (Real.sqrt (2 * Real.pi) + 1) + Real.sqrt (2 * Real.pi) * A, fun ε hε => ?_⟩
    have hε0 : 0 < ε := by linarith
    have hs1 : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε
    have hZ : ‖∑' q : XiZeroCopy, zeroBohrAmplitude q *
        Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤ A := by
      refine (norm_tsum_le_tsum_norm (hsum_le ε hε0.le τ)).trans ?_
      refine Summable.tsum_le_tsum (fun q => ?_) (hsum_le ε hε0.le τ) hAs
      rw [norm_mul, Complex.norm_exp]
      have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re = -(ε * (zeroLightConeExponent τ q).re) := by
        simp
      rw [hre]
      have := re_zeroLightConeExponent_nonneg_of_riemannHypothesis hRH τ q
      have hle : Real.exp (-(ε * (zeroLightConeExponent τ q).re)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith)
      nlinarith [norm_nonneg (zeroBohrAmplitude q)]
    have h1 := hexp ε hε0 τ
    have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have htri := norm_sub_le (gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
      (((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
    rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at htri
    rw [hsqrt ε hε0.le] at htri h1
    have hspi : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
    have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    have hprod : Real.sqrt (2 * Real.pi) * Real.sqrt ε *
        ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
        Real.sqrt (2 * Real.pi) * Real.sqrt ε * A := by gcongr
    nlinarith
  · intro hbd
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    have hre : 1 / 2 < z.re := mem_rightHalf.mp hz
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_eq_of_xi_eq_zero hzero
    set τ : ℝ := z.im / 2 with hτ
    obtain ⟨Cτ, hCτ⟩ := hbd τ
    -- light-cone amplification of the zero series
    have hneg : (zeroLightConeExponent τ q₀).re < 0 := by
      rw [re_zeroLightConeExponent, hq₀, hτ, sub_self]
      nlinarith
    have hfin : {q : XiZeroCopy | (zeroLightConeExponent τ q).re < 0}.Finite := by
      refine (finite_xiZeroCopy_norm_le (1 / 2 + (2 * |τ| + 4))).subset fun q hq => ?_
      simp only [mem_setOf_eq] at hq ⊢
      rw [re_zeroLightConeExponent] at hq
      have hb := re_xiZero_sub_half_bounds q
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hb
      have hγ : ((xiZero q).im / 2 - τ) ^ 2 < 4 := by nlinarith
      have hγ' : |(xiZero q).im / 2 - τ| < 2 := by
        rw [← Real.sqrt_sq_eq_abs]
        calc Real.sqrt (((xiZero q).im / 2 - τ) ^ 2) < Real.sqrt 4 := Real.sqrt_lt_sqrt (sq_nonneg _) hγ
          _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have him : |(xiZero q).im| ≤ 2 * |τ| + 4 := by
        have := abs_sub_abs_le_abs_sub ((xiZero q).im / 2) τ
        rw [abs_div, abs_two] at this
        linarith
      rw [norm_xiSpectralPoint]
      calc ‖xiZero q - 1 / 2‖ ≤ |(xiZero q - 1 / 2).re| + |(xiZero q - 1 / 2).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1 / 2 + (2 * |τ| + 4) := by
            have h1 : |(xiZero q - 1 / 2).re| ≤ 1 / 2 := by
              simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
              exact abs_le.2 ⟨by linarith, by linarith⟩
            have h2 : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
            rw [h2]
            linarith
    set target : ℝ := Cτ / Real.sqrt (2 * Real.pi) + 2 * C₀ with htarget
    obtain ⟨ε, hε1, hbig⟩ := GaloisForLFunctions.HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg
      (w := zeroLightConeExponent τ) (c := zeroBohrAmplitude) (ε₀ := 1) zero_le_one
      (fun q q' h => by unfold zeroBohrAmplitude; rw [xiZero_eq_of_zeroLightConeExponent_eq h])
      (fun q _ => zeroBohrAmplitude_ne_zero q) hfin (m := fun q => ‖zeroBohrAmplitude q‖)
      (fun _ => norm_nonneg _) hAs
      (fun q hq ε hε => by
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(ε : ℂ) * zeroLightConeExponent τ q).re =
            -(ε * (zeroLightConeExponent τ q).re) := by simp
        rw [hre]
        have hle : Real.exp (-(ε * (zeroLightConeExponent τ q).re)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith)
        nlinarith [norm_nonneg (zeroBohrAmplitude q)])
      (fun ε hε => hsum_le ε (by linarith) τ) ⟨q₀, hneg⟩ target
    have hε0 : 0 < ε := by linarith
    have h1 := hexp ε hε0 τ
    have h2 := hCτ ε hε1
    have htri := norm_sub_le (gaussianFilteredCentralGap ε τ + ((Real.sqrt (2 * Real.pi * ε) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q))
      (gaussianFilteredCentralGap ε τ)
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at htri
    rw [hsqrt ε hε0.le] at htri h1
    have hspi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    have hsε : 1 ≤ Real.sqrt ε := Real.one_le_sqrt.2 hε1
    have he : Real.exp (-2 * ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 < Real.sqrt (2 * Real.pi) * Real.sqrt ε := by positivity
    -- `√(2π)√ε · ‖Σ‖ ≤ Cτ √ε + C₀ (√(2π)√ε + 1)`
    have hkey : Real.sqrt (2 * Real.pi) * Real.sqrt ε *
        ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ ≤
        Cτ * Real.sqrt ε + C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left he hC₀]
    have hbig' : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target <
        Real.sqrt (2 * Real.pi) * Real.sqrt ε *
        ‖∑' q : XiZeroCopy, zeroBohrAmplitude q * Complex.exp (-(ε : ℂ) * zeroLightConeExponent τ q)‖ :=
      mul_lt_mul_of_pos_left hbig hpos
    have hexpand : Real.sqrt (2 * Real.pi) * Real.sqrt ε * target =
        Cτ * Real.sqrt ε + 2 * C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
      rw [htarget]; field_simp
    have hfin' : C₀ ≤ C₀ * (Real.sqrt (2 * Real.pi) * Real.sqrt ε) := by
      have : 1 ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ε := by
        have h2pi : 1 ≤ Real.sqrt (2 * Real.pi) := by
          rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
        nlinarith
      nlinarith
    linarith

end

end RHTower
