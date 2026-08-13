import GaloisForLFunctions.RHTower.XiShiftedHardEdgePaleyWienerPeriodization
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.HTGeometry.SchwartzPositiveMeasureRepresentation
import GaloisForLFunctions.HTGeometry.FiniteRegularityFourierDecay
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Exact complex-phase Paley--Wiener periodization at the shifted-Xi hard edge

The real-line hard-edge periodization is insufficient for the Xi divisor: an off-line zero gives
a genuinely complex spectral point. This module removes that obstruction without a computational
surrogate. Compact support absorbs the imaginary part of an arbitrary complex phase as a real
exponential tilt, after which the already proved real modulated Poisson theorem applies exactly.

The amplitude is the canonical compactly supported approximation of an arbitrary Schwartz map.
Consequently every declaration is premise-free: compact support and smoothness are proved by the
construction, not supplied as hypotheses.
-/

open scoped SchwartzMap FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open MeasureTheory

/-- A compactly supported amplitude tilted by the imaginary part of a complex frequency. -/
def routeUComplexTiltFun (n : ℕ) (f : SchwartzMap ℝ ℂ) (v : ℝ) : ℝ → ℂ :=
  fun t => cexpLin (-(v : ℂ)) t * SchwartzMap.compactSupportApproximation n f t

theorem routeUComplexTiltFun_hasCompactSupport
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (v : ℝ) :
    HasCompactSupport (routeUComplexTiltFun n f v) := by
  exact (SchwartzMap.compactSupportApproximation_hasCompactSupport n f).mul_left

theorem routeUComplexTiltFun_contDiff
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (v : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (routeUComplexTiltFun n f v) := by
  exact (contDiff_cexpLin (-(v : ℂ))).mul
    ((SchwartzMap.compactSupportApproximation n f).smooth ⊤)

/-- Imaginary exponential tilt as an actual Schwartz map. -/
def routeUComplexTilt (n : ℕ) (f : SchwartzMap ℝ ℂ) (v : ℝ) : SchwartzMap ℝ ℂ :=
  (routeUComplexTiltFun_hasCompactSupport n f v).toSchwartzMap
    (routeUComplexTiltFun_contDiff n f v)

@[simp]
theorem routeUComplexTilt_apply
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (v t : ℝ) :
    routeUComplexTilt n f v t =
      Complex.exp (-(v : ℂ) * (t : ℂ)) *
        SchwartzMap.compactSupportApproximation n f t := rfl

/-- Pointwise majorant for every derivative of every imaginary tilt with `|v| ≤ 1`. -/
def routeUComplexTiltDerivMajorant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : ℕ) (t : ℝ) : ℝ :=
  Real.exp |t| *
    ∑ i ∈ Finset.range (q + 1),
      (q.choose i : ℝ) *
        ‖iteratedFDeriv ℝ (q - i) (SchwartzMap.compactSupportApproximation n f) t‖

/-- Uniform `L¹` derivative bound for the fixed compact amplitude over the full tilt strip. -/
def routeUComplexTiltDerivL1Bound
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : ℕ) : ℝ :=
  ∫ t : ℝ, routeUComplexTiltDerivMajorant n f q t

theorem iteratedDeriv_routeUComplexTiltFun
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (v t : ℝ) (q : ℕ) :
    iteratedDeriv q (routeUComplexTiltFun n f v) t =
      ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℂ) * ((-(v : ℂ)) ^ i * cexpLin (-(v : ℂ)) t) *
          iteratedDeriv (q - i) (SchwartzMap.compactSupportApproximation n f) t := by
  change iteratedDeriv q (fun t => cexpLin (-(v : ℂ)) t *
    SchwartzMap.compactSupportApproximation n f t) t = _
  have hfun : (fun t => cexpLin (-(v : ℂ)) t *
      SchwartzMap.compactSupportApproximation n f t) =
      cexpLin (-(v : ℂ)) *
        ((SchwartzMap.compactSupportApproximation n f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := rfl
  rw [hfun, iteratedDeriv_mul
    ((contDiff_cexpLin (-(v : ℂ))).contDiffAt.of_le (by exact_mod_cast le_top))
    (((SchwartzMap.compactSupportApproximation n f).smooth q).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [congrFun (iteratedDeriv_cexpLin (-(v : ℂ)) i) t]

theorem norm_cexpLin_real_tilt_le_exp_abs
    {v : ℝ} (hv : |v| ≤ 1) (t : ℝ) :
    ‖cexpLin (-(v : ℂ)) t‖ ≤ Real.exp |t| := by
  rw [cexpLin, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp [Complex.mul_re]
  calc
    -(v * t) ≤ |v * t| := neg_le_abs _
    _ = |v| * |t| := abs_mul v t
    _ ≤ 1 * |t| := by gcongr
    _ = |t| := one_mul _

theorem norm_iteratedDeriv_routeUComplexTiltFun_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) {v : ℝ} (hv : |v| ≤ 1) (q : ℕ) (t : ℝ) :
    ‖iteratedDeriv q (routeUComplexTiltFun n f v) t‖ ≤
      routeUComplexTiltDerivMajorant n f q t := by
  rw [iteratedDeriv_routeUComplexTiltFun]
  calc
    ‖∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℂ) * ((-(v : ℂ)) ^ i * cexpLin (-(v : ℂ)) t) *
          iteratedDeriv (q - i) (SchwartzMap.compactSupportApproximation n f) t‖ ≤
      ∑ i ∈ Finset.range (q + 1),
        ‖(q.choose i : ℂ) * ((-(v : ℂ)) ^ i * cexpLin (-(v : ℂ)) t) *
          iteratedDeriv (q - i) (SchwartzMap.compactSupportApproximation n f) t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) * Real.exp |t| *
          ‖iteratedFDeriv ℝ (q - i)
            (SchwartzMap.compactSupportApproximation n f) t‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_natCast]
      have hvi : |v| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg v) hv
      have hexp := norm_cexpLin_real_tilt_le_exp_abs hv t
      have hprod : |v| ^ i * ‖cexpLin (-(v : ℂ)) t‖ ≤ Real.exp |t| := by
        calc
          |v| ^ i * ‖cexpLin (-(v : ℂ)) t‖ ≤
              1 * ‖cexpLin (-(v : ℂ)) t‖ := by gcongr
          _ ≤ 1 * Real.exp |t| := by gcongr
          _ = Real.exp |t| := one_mul _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      gcongr
    _ = routeUComplexTiltDerivMajorant n f q t := by
      rw [routeUComplexTiltDerivMajorant, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem integrable_routeUComplexTiltDerivMajorant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : ℕ) :
    Integrable (routeUComplexTiltDerivMajorant n f q) := by
  let A := SchwartzMap.compactSupportApproximation n f
  have hA : HasCompactSupport A :=
    SchwartzMap.compactSupportApproximation_hasCompactSupport n f
  have hfun : routeUComplexTiltDerivMajorant n f q = fun t : ℝ =>
      ∑ i ∈ Finset.range (q + 1),
        Real.exp |t| * ((q.choose i : ℝ) * ‖iteratedFDeriv ℝ (q - i) A t‖) := by
    funext t
    rw [routeUComplexTiltDerivMajorant, Finset.mul_sum]
  rw [hfun]
  apply integrable_finsetSum
  intro i hi
  have hderivCont : Continuous fun t : ℝ => iteratedFDeriv ℝ (q - i) A t :=
    (A.smooth (q - i)).continuous_iteratedFDeriv le_rfl
  have hcont : Continuous fun t : ℝ =>
      Real.exp |t| * ((q.choose i : ℝ) * ‖iteratedFDeriv ℝ (q - i) A t‖) :=
    (Real.continuous_exp.comp continuous_abs).mul
      (continuous_const.mul hderivCont.norm)
  have hsupp : HasCompactSupport fun t : ℝ =>
      Real.exp |t| * ((q.choose i : ℝ) * ‖iteratedFDeriv ℝ (q - i) A t‖) := by
    exact ((hA.iteratedFDeriv (q - i)).norm.mul_left).mul_left
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem routeUComplexTiltDerivL1Bound_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : ℕ) :
    0 ≤ routeUComplexTiltDerivL1Bound n f q := by
  apply integral_nonneg
  intro t
  rw [routeUComplexTiltDerivMajorant]
  exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun i hi => by positivity)

theorem derivL1_routeUComplexTiltFun_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) {v : ℝ} (hv : |v| ≤ 1) (q : ℕ) :
    derivL1 q (routeUComplexTiltFun n f v) ≤
      routeUComplexTiltDerivL1Bound n f q := by
  rw [derivL1, routeUComplexTiltDerivL1Bound]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun t => norm_nonneg _
  · exact integrable_routeUComplexTiltDerivMajorant n f q
  · exact Filter.Eventually.of_forall fun t => by
      change ‖iteratedFDeriv ℝ q (routeUComplexTiltFun n f v) t‖ ≤
        routeUComplexTiltDerivMajorant n f q t
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact norm_iteratedDeriv_routeUComplexTiltFun_le n f hv q t

/-- Uniform finite-regularity Fourier decay constant over the complete phase strip `|v| ≤ 1`. -/
def routeUComplexTiltUniformDecay
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ :=
  2 ^ j * (routeUComplexTiltDerivL1Bound n f 0 +
    ((2 * Real.pi) ^ (2 * j))⁻¹ * routeUComplexTiltDerivL1Bound n f (2 * j))

theorem routeUComplexTiltUniformDecay_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (j : ℕ) :
    0 ≤ routeUComplexTiltUniformDecay n f j := by
  rw [routeUComplexTiltUniformDecay]
  exact mul_nonneg (by positivity)
    (add_nonneg (routeUComplexTiltDerivL1Bound_nonneg n f 0)
      (mul_nonneg (by positivity)
        (routeUComplexTiltDerivL1Bound_nonneg n f (2 * j))))

theorem contDiffDecay_routeUComplexTiltFun_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) {v : ℝ} (hv : |v| ≤ 1) (j : ℕ) :
    contDiffDecay j (routeUComplexTiltFun n f v) ≤
      routeUComplexTiltUniformDecay n f j := by
  rw [contDiffDecay, routeUComplexTiltUniformDecay]
  have h0 := derivL1_routeUComplexTiltFun_le n f hv 0
  have hj := derivL1_routeUComplexTiltFun_le n f hv (2 * j)
  gcongr

/-- **Uniform Fourier decay over the complete complex phase strip.** -/
theorem routeUComplexTilt_uniform_fourier_decay
    (n : ℕ) (f : SchwartzMap ℝ ℂ) {v : ℝ} (hv : |v| ≤ 1)
    (j : ℕ) (w : ℝ) :
    kgFreq w ^ (2 * j) * ‖𝓕 (routeUComplexTiltFun n f v) w‖ ≤
      routeUComplexTiltUniformDecay n f j := by
  exact (kgFreq_pow_mul_norm_fourier_le
    ((routeUComplexTiltFun_contDiff n f v).of_le
      (WithTop.coe_le_coe.mpr (show (((2 * j : ℕ) : ℕ∞) ≤ ⊤) from le_top)))
    (routeUComplexTiltFun_hasCompactSupport n f v) w).trans
      (contDiffDecay_routeUComplexTiltFun_le n f hv j)

/-- Positive-exponent Fourier extension at an arbitrary complex frequency. -/
def routeUComplexPositiveFourierExtension
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (z : ℂ) : ℂ :=
  routeUPositiveFourierExtension (routeUComplexTilt n f z.im) z.re

/-- Uniform weighted bound for the complex positive Fourier extension on `|Im z| ≤ 1`. -/
theorem routeUComplexPositiveFourierExtension_uniform_decay
    (n : ℕ) (f : SchwartzMap ℝ ℂ) {z : ℂ} (hz : |z.im| ≤ 1) (j : ℕ) :
    kgFreq (-z.re / (2 * Real.pi)) ^ (2 * j) *
        ‖routeUComplexPositiveFourierExtension n f z‖ ≤
      routeUComplexTiltUniformDecay n f j := by
  rw [routeUComplexPositiveFourierExtension,
    routeUPositiveFourierExtension, SchwartzMap.fourier_coe]
  change kgFreq (-z.re / (2 * Real.pi)) ^ (2 * j) *
      ‖𝓕 (routeUComplexTiltFun n f z.im) (-z.re / (2 * Real.pi))‖ ≤
    routeUComplexTiltUniformDecay n f j
  exact routeUComplexTilt_uniform_fourier_decay n f hz j
    (-z.re / (2 * Real.pi))

/-- The complex exponential is a real modulation times the compact-support imaginary tilt. -/
theorem routeU_complex_exp_decomposition (z : ℂ) (t : ℝ) :
    Complex.exp (Complex.I * z * (t : ℂ)) =
      Complex.exp (Complex.I * (z.re : ℂ) * (t : ℂ)) *
        Complex.exp (-(z.im : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- **Exact Route U complex hard-edge periodization (complex HEPW.8).**

For every complex phase, the sampled compactly supported amplitude equals its complete complex
Fourier alias packet. No zero-location, strip, asymptotic, or RH hypothesis is used. -/
theorem routeU_complex_hardEdge_periodization
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ) :
    ((routeUHardEdgeMesh r : ℝ) : ℂ) *
        (∑' k : ℤ,
          Complex.exp
              (Complex.I * z *
                (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
            SchwartzMap.compactSupportApproximation n f
              (routeUHardEdgeMesh r * (k : ℝ))) =
      ∑' m : ℤ,
        routeUComplexPositiveFourierExtension n f
          (z + (routeUHardEdgeAliasPeriod r * (m : ℝ) : ℝ)) := by
  rw [show (∑' k : ℤ,
          Complex.exp
              (Complex.I * z *
                (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
            SchwartzMap.compactSupportApproximation n f
              (routeUHardEdgeMesh r * (k : ℝ))) =
        ∑' k : ℤ,
          Complex.exp
              (Complex.I * (z.re : ℂ) *
                (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
            routeUComplexTilt n f z.im (routeUHardEdgeMesh r * (k : ℝ)) by
      apply tsum_congr
      intro k
      rw [routeUComplexTilt_apply, routeU_complex_exp_decomposition]
      ring]
  rw [routeU_hardEdge_periodization (routeUComplexTilt n f z.im) r z.re]
  apply tsum_congr
  intro m
  rw [routeUComplexPositiveFourierExtension]
  congr 2
  simp

/-- Principal complex arctangent always has real part in the closed central half-period. -/
theorem abs_complex_arctan_re_le_pi_div_two (z : ℂ) :
    |(Complex.arctan z).re| ≤ Real.pi / 2 := by
  rw [Complex.arctan]
  have hre :
      (-Complex.I / 2 *
        Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
        (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im / 2 := by
    simp [Complex.mul_re]
    ring
  rw [hre, Complex.log_im, abs_div]
  have habs2 : |(2 : ℝ)| = 2 := by norm_num
  rw [habs2]
  exact (div_le_div_iff_of_pos_right two_pos).2 (Complex.abs_arg_le_pi _)

/-- Imaginary part of principal complex arctangent as an exact logarithmic norm ratio. -/
theorem complex_arctan_im_eq_log_norm_ratio (z : ℂ) :
    (Complex.arctan z).im =
      -Real.log ‖(1 + z * Complex.I) / (1 - z * Complex.I)‖ / 2 := by
  rw [Complex.arctan]
  simp [Complex.mul_im, Complex.log_re]
  ring

/-- Logarithm is quantitatively Lipschitz between two positive real arguments, with denominator
the smaller argument. -/
theorem abs_log_sub_log_le_abs_sub_div_min
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |Real.log p - Real.log q| ≤ |p - q| / min p q := by
  rcases le_total p q with hpq | hqp
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hp hpq)),
      abs_of_nonpos (sub_nonpos.mpr hpq), min_eq_left hpq]
    have hlog : Real.log (q / p) ≤ q / p - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    rw [show q / p - 1 = (q - p) / p by field_simp] at hlog
    simpa only [neg_sub] using hlog
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hq hqp)),
      abs_of_nonneg (sub_nonneg.mpr hqp), min_eq_right hqp]
    have hlog : Real.log (p / q) ≤ p / q - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hp hq)
    rw [Real.log_div hp.ne' hq.ne'] at hlog
    rw [show p / q - 1 = (p - q) / q by field_simp] at hlog
    exact hlog

/-- Horizontal-strip contraction for principal complex arctangent. The estimate is independent of
the real part, which is the uniformity needed for the unbounded Xi divisor. -/
theorem abs_complex_arctan_im_le_of_abs_im_lt_one
    {z : ℂ} (hz : |z.im| < 1) :
    |(Complex.arctan z).im| ≤ |z.im| / (1 - |z.im|) := by
  let U : ℂ := 1 + z * Complex.I
  let V : ℂ := starRingEnd ℂ (1 - z * Complex.I)
  have hUre : U.re = 1 - z.im := by
    simp [U, Complex.mul_re]
    ring
  have hVre : V.re = 1 + z.im := by
    simp [V, Complex.mul_re]
  have hlowerU : 1 - |z.im| ≤ ‖U‖ := by
    have hre : 1 - |z.im| ≤ U.re := by
      rw [hUre]
      linarith [le_abs_self z.im]
    exact hre.trans (le_trans (le_abs_self U.re) (Complex.abs_re_le_norm U))
  have hlowerV : 1 - |z.im| ≤ ‖V‖ := by
    have hre : 1 - |z.im| ≤ V.re := by
      rw [hVre]
      linarith [neg_le_abs z.im]
    exact hre.trans (le_trans (le_abs_self V.re) (Complex.abs_re_le_norm V))
  have hbase : 0 < 1 - |z.im| := sub_pos.mpr hz
  have hUpos : 0 < ‖U‖ := hbase.trans_le hlowerU
  have hVpos : 0 < ‖V‖ := hbase.trans_le hlowerV
  have hVnorm : ‖V‖ = ‖1 - z * Complex.I‖ := by
    change ‖star (1 - z * Complex.I)‖ = ‖1 - z * Complex.I‖
    exact norm_star _
  have hUV : U - V = ((-2 * z.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [U, V, Complex.mul_re]
      ring
    · simp [U, V, Complex.mul_im]
  have hnormUV : ‖U - V‖ = 2 * |z.im| := by
    rw [hUV, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  have hnormdiff : |‖U‖ - ‖V‖| ≤ 2 * |z.im| := by
    exact (abs_norm_sub_norm_le U V).trans_eq hnormUV
  have hlog := abs_log_sub_log_le_abs_sub_div_min hUpos hVpos
  have hmin : 1 - |z.im| ≤ min ‖U‖ ‖V‖ := le_min hlowerU hlowerV
  have hlogBound :
      |Real.log ‖U‖ - Real.log ‖V‖| ≤ 2 * |z.im| / (1 - |z.im|) := by
    calc
      |Real.log ‖U‖ - Real.log ‖V‖| ≤
          |‖U‖ - ‖V‖| / min ‖U‖ ‖V‖ := hlog
      _ ≤ 2 * |z.im| / (1 - |z.im|) := by
        have hminpos : 0 < min ‖U‖ ‖V‖ := hbase.trans_le hmin
        gcongr
  rw [complex_arctan_im_eq_log_norm_ratio,
    show 1 + z * Complex.I = U by rfl, norm_div,
    Real.log_div hUpos.ne' (by simpa [hVnorm] using hVpos.ne')]
  rw [← hVnorm]
  have habs2 : |(2 : ℝ)| = 2 := by norm_num
  rw [abs_div, abs_neg, habs2]
  calc
    |Real.log ‖U‖ - Real.log ‖V‖| / 2 ≤
        (2 * |z.im| / (1 - |z.im|)) / 2 := by gcongr
    _ = |z.im| / (1 - |z.im|) := by field_simp

/-- Complex Cayley phase in the literal shifted-Xi hard-edge scale. -/
def routeUComplexHardEdgePhase (r : ℝ) (alpha : ℂ) : ℂ :=
  (routeUHardEdgeMass r : ℂ) *
    Complex.arctan (alpha / (routeUHardEdgeMass r : ℂ))

/-- Imaginary part under scaling by the positive hard-edge mass. -/
theorem abs_im_div_routeUHardEdgeMass (r : ℝ) (alpha : ℂ) :
    |(alpha / (routeUHardEdgeMass r : ℂ)).im| =
      |alpha.im| / routeUHardEdgeMass r := by
  have hmass := routeUHardEdgeMass_pos r
  have him : (alpha / (routeUHardEdgeMass r : ℂ)).im =
      alpha.im / routeUHardEdgeMass r := by
    rw [Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp [hmass.ne']
  rw [him, abs_div, abs_of_pos hmass]

/-- The complex Cayley phase maps the full open Xi strip into a fixed horizontal strip, uniformly
in spectral height and hard-edge mass. -/
theorem abs_routeUComplexHardEdgePhase_im_lt_one_of_abs_im_lt_half
    (r : ℝ) {alpha : ℂ} (halpha : |alpha.im| < 1 / 2) :
    |(routeUComplexHardEdgePhase r alpha).im| < 1 := by
  let a : ℝ := routeUHardEdgeMass r
  let w : ℂ := alpha / (a : ℂ)
  have ha : 1 ≤ a := by simp [a, routeUHardEdgeMass]
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hwi : |w.im| = |alpha.im| / a := by
    simpa only [w, a] using abs_im_div_routeUHardEdgeMass r alpha
  have hwhalf : |w.im| < 1 / 2 := by
    rw [hwi]
    exact (div_lt_iff₀ hapos).2 (by nlinarith)
  have hwone : |w.im| < 1 := hwhalf.trans (by norm_num)
  have hatan := abs_complex_arctan_im_le_of_abs_im_lt_one hwone
  have hden : 1 / 2 < 1 - |w.im| := by linarith
  have hquot : |w.im| / (1 - |w.im|) < 2 * |w.im| ∨ w.im = 0 := by
    by_cases hw : w.im = 0
    · exact Or.inr hw
    · left
      have hwabs : 0 < |w.im| := abs_pos.mpr hw
      apply (div_lt_iff₀ (by linarith : 0 < 1 - |w.im|)).2
      nlinarith
  have hatanTwo : |(Complex.arctan w).im| ≤ 2 * |w.im| := by
    rcases hquot with hquot | hw
    · exact hatan.trans hquot.le
    · simp [hw] at hatan ⊢
      exact hatan
  rw [routeUComplexHardEdgePhase]
  change |((a : ℂ) * Complex.arctan w).im| < 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [abs_mul, abs_of_pos hapos]
  calc
    a * |(Complex.arctan w).im| ≤ a * (2 * |w.im|) := by gcongr
    _ = 2 * |alpha.im| := by rw [hwi]; field_simp
    _ < 1 := by nlinarith

/-- **Premise-free Xi strip bound for the complex Cayley phase.** -/
theorem abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one
    (r : ℝ) (q : XiZeroCopy) :
    |(routeUComplexHardEdgePhase r (xiSpectralPoint q)).im| < 1 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have him : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
    rw [xiSpectralPoint]
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_im,
      Complex.I_re, Complex.I_im]
  apply abs_routeUComplexHardEdgePhase_im_lt_one_of_abs_im_lt_half r
  rw [him, abs_lt]
  constructor <;> linarith

/-- Real part of every complex Cayley phase lies in the central alias cell. -/
theorem abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod
    (r : ℝ) (alpha : ℂ) :
    |(routeUComplexHardEdgePhase r alpha).re| ≤
      routeUHardEdgeAliasPeriod r / 2 := by
  have hmass := routeUHardEdgeMass_pos r
  have hatan := abs_complex_arctan_re_le_pi_div_two
    (alpha / (routeUHardEdgeMass r : ℂ))
  rw [routeUComplexHardEdgePhase, routeUHardEdgeAliasPeriod]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [abs_mul, abs_of_pos hmass]
  nlinarith

/-- Complete noncentral complex-frequency alias tail. -/
def routeUComplexHardEdgeAliasTail
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  routeUHardEdgeAliasTail (routeUComplexTilt n f z.im) r z.re

/-- Absolute value is bounded by the one-dimensional Klein--Gordon frequency. -/
theorem abs_le_kgFreq_real (x : ℝ) :
    |x| ≤ kgFreq x := by
  rw [kgFreq, Real.norm_eq_abs,
    Real.le_sqrt (abs_nonneg x) (by positivity)]
  nlinarith [sq_nonneg |x|]

/-- Phase-independent coefficient for the complex hard-edge alias tail on `|Im z| ≤ 1`. -/
def routeUComplexHardEdgeUniformAliasTailCoefficient
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (N : ℕ) : ℝ :=
  routeUComplexTiltUniformDecay n f (N + 1) *
    (4 * Real.pi) ^ ccmRationalArchimedeanDecayExponent N

theorem routeUComplexHardEdgeUniformAliasTailCoefficient_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    0 ≤ routeUComplexHardEdgeUniformAliasTailCoefficient n f N := by
  rw [routeUComplexHardEdgeUniformAliasTailCoefficient]
  exact mul_nonneg (routeUComplexTiltUniformDecay_nonneg n f (N + 1)) (by positivity)

/-- Full phase-independent constant for the complex hard-edge alias tail on `|Im z| ≤ 1`. -/
def routeUComplexHardEdgeUniformAliasTailConstant
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (N : ℕ) : ℝ :=
  routeUComplexHardEdgeUniformAliasTailCoefficient n f N *
    ∑' m : ℤ, ccmRationalArchimedeanPSeriesKernel N m

theorem routeUComplexHardEdgeUniformAliasTailConstant_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (N : ℕ) :
    0 ≤ routeUComplexHardEdgeUniformAliasTailConstant n f N := by
  rw [routeUComplexHardEdgeUniformAliasTailConstant]
  exact mul_nonneg
    (routeUComplexHardEdgeUniformAliasTailCoefficient_nonneg n f N)
    (tsum_nonneg (ccmRationalArchimedeanPSeriesKernel_nonneg N))

/-- Each complex noncentral alias has a phase-independent even-power majorant throughout the
closed strip `|Im z| ≤ 1` and central real alias cell. -/
theorem norm_routeUComplexHardEdgeAliasTailTerm_uniform_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hzIm : |z.im| ≤ 1)
    (hzRe : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2)
    (N : ℕ) (m : ℤ) :
    ‖routeUHardEdgeAliasTailTerm (routeUComplexTilt n f z.im) r z.re m‖ ≤
      (routeUComplexHardEdgeUniformAliasTailCoefficient n f N /
          routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N) *
        ccmRationalArchimedeanPSeriesKernel N m := by
  by_cases hm : m = 0
  · subst m
    simp [routeUHardEdgeAliasTailTerm,
      ccmRationalArchimedeanPSeriesKernel]
  · let p := ccmRationalArchimedeanDecayExponent N
    let L := routeUHardEdgeAliasPeriod r
    let v := z.re + L * (m : ℝ)
    let w := -v / (2 * Real.pi)
    let za : ℂ := z + (L * (m : ℝ) : ℝ)
    let C := routeUComplexTiltUniformDecay n f (N + 1)
    have hL : 0 < L := routeUHardEdgeAliasPeriod_pos r
    have hmone : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hm
    have hlowerpos : 0 < L * |(m : ℝ)| / (4 * Real.pi) := by positivity
    have hsep : L * |(m : ℝ)| / 2 ≤ |v| := by
      exact routeU_alias_separation hL hzRe hm
    have hwabs : |w| = |v| / (2 * Real.pi) := by
      dsimp only [w]
      rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos Real.pi_pos)]
    have hfreqLower : L * |(m : ℝ)| / (4 * Real.pi) ≤ |w| := by
      calc
        L * |(m : ℝ)| / (4 * Real.pi) =
            (L * |(m : ℝ)| / 2) / (2 * Real.pi) := by ring
        _ ≤ |v| / (2 * Real.pi) := by gcongr
        _ = |w| := hwabs.symm
    have hkgLower : L * |(m : ℝ)| / (4 * Real.pi) ≤ kgFreq w :=
      hfreqLower.trans (abs_le_kgFreq_real w)
    have hzaIm : |za.im| ≤ 1 := by
      simpa only [za, Complex.add_im, Complex.ofReal_im, add_zero] using hzIm
    have hdecay :
        kgFreq w ^ p * ‖routeUComplexPositiveFourierExtension n f za‖ ≤ C := by
      simpa only [w, v, za, p, C, Complex.add_re, Complex.ofReal_re,
          ccmRationalArchimedeanDecayExponent] using
        routeUComplexPositiveFourierExtension_uniform_decay n f hzaIm (N + 1)
    have hC : 0 ≤ C := routeUComplexTiltUniformDecay_nonneg n f (N + 1)
    have hnorm :
        ‖routeUComplexPositiveFourierExtension n f za‖ ≤ C / kgFreq w ^ p := by
      apply (le_div_iff₀ (pow_pos (kgFreq_pos w) p)).2
      simpa only [mul_comm] using hdecay
    have hden :
        C / kgFreq w ^ p ≤ C / (L * |(m : ℝ)| / (4 * Real.pi)) ^ p := by
      gcongr
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have habspow : |(m : ℝ)| ^ p = (m : ℝ) ^ p := by
      change |(m : ℝ)| ^ (2 * (N + 1)) =
        (m : ℝ) ^ (2 * (N + 1))
      rw [pow_mul, pow_mul, sq_abs]
    have hterm :
        routeUHardEdgeAliasTailTerm (routeUComplexTilt n f z.im) r z.re m =
          routeUComplexPositiveFourierExtension n f za := by
      simp [routeUHardEdgeAliasTailTerm, hm, routeUPositiveFourierSchwartz_apply,
        routeUComplexPositiveFourierExtension, za, L]
    rw [hterm, ccmRationalArchimedeanPSeriesKernel, if_neg hm]
    calc
      ‖routeUComplexPositiveFourierExtension n f za‖ ≤ C / kgFreq w ^ p := hnorm
      _ ≤ C / (L * |(m : ℝ)| / (4 * Real.pi)) ^ p := hden
      _ = (routeUComplexHardEdgeUniformAliasTailCoefficient n f N /
            routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N) *
          (1 / (m : ℝ) ^ ccmRationalArchimedeanDecayExponent N) := by
        rw [routeUComplexHardEdgeUniformAliasTailCoefficient]
        change C / (L * |(m : ℝ)| / (4 * Real.pi)) ^ p =
          (C * (4 * Real.pi) ^ p / L ^ p) * (1 / (m : ℝ) ^ p)
        rw [div_pow, mul_pow, habspow]
        field_simp [hL.ne', hmR, Real.pi_ne_zero]

theorem summable_norm_routeUComplexHardEdgeAliasTailTerm_uniform
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hzIm : |z.im| ≤ 1)
    (hzRe : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2) (N : ℕ) :
    Summable (fun m : ℤ =>
      ‖routeUHardEdgeAliasTailTerm (routeUComplexTilt n f z.im) r z.re m‖) := by
  let C := routeUComplexHardEdgeUniformAliasTailCoefficient n f N /
    routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N
  have hmajor : Summable (fun m : ℤ =>
      C * ccmRationalArchimedeanPSeriesKernel N m) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left C
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => norm_routeUComplexHardEdgeAliasTailTerm_uniform_le
      n f r z hzIm hzRe N m) hmajor

/-- **Uniform complex HEPW.9 alias decay.** The constant depends only on compact approximation and
requested power, not on hard-edge mass, real phase, imaginary phase, or Xi-zero height. -/
theorem norm_routeUComplexHardEdgeAliasTail_uniform_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hzIm : |z.im| ≤ 1)
    (hzRe : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2) (N : ℕ) :
    ‖routeUComplexHardEdgeAliasTail n f r z‖ ≤
      routeUComplexHardEdgeUniformAliasTailConstant n f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  have hnorm := summable_norm_routeUComplexHardEdgeAliasTailTerm_uniform
    n f r z hzIm hzRe N
  let C := routeUComplexHardEdgeUniformAliasTailCoefficient n f N /
    routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N
  have hmajor : Summable (fun m : ℤ =>
      C * ccmRationalArchimedeanPSeriesKernel N m) :=
    (ccmRationalArchimedeanPSeriesKernel_summable N).mul_left C
  calc
    ‖routeUComplexHardEdgeAliasTail n f r z‖ ≤
        ∑' m : ℤ,
          ‖routeUHardEdgeAliasTailTerm (routeUComplexTilt n f z.im) r z.re m‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℤ, C * ccmRationalArchimedeanPSeriesKernel N m := by
      exact hnorm.tsum_le_tsum
        (fun m => norm_routeUComplexHardEdgeAliasTailTerm_uniform_le
          n f r z hzIm hzRe N m) hmajor
    _ = routeUComplexHardEdgeUniformAliasTailConstant n f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
      rw [tsum_mul_left, routeUComplexHardEdgeUniformAliasTailConstant]
      dsimp only [C]
      ring

/-- **Premise-free uniform complex HEPW.9 at every Xi divisor point.** -/
theorem norm_routeUComplexHardEdgeAliasTail_xiSpectralPoint_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) (N : ℕ) :
    ‖routeUComplexHardEdgeAliasTail n f r
        (routeUComplexHardEdgePhase r (xiSpectralPoint q))‖ ≤
      routeUComplexHardEdgeUniformAliasTailConstant n f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  exact norm_routeUComplexHardEdgeAliasTail_uniform_le n f r
    (routeUComplexHardEdgePhase r (xiSpectralPoint q))
    (abs_routeUComplexHardEdgePhase_xiSpectralPoint_im_lt_one r q).le
    (abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod r (xiSpectralPoint q)) N

/-- A complex alias packet is its central entire value plus its noncentral tail. -/
theorem tsum_routeUComplexAlias_eq_extension_add_tail
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ)
    (hz : |z.re| ≤ routeUHardEdgeAliasPeriod r / 2) :
    (∑' m : ℤ, routeUComplexPositiveFourierExtension n f
        (z + (routeUHardEdgeAliasPeriod r * (m : ℝ) : ℝ))) =
      routeUComplexPositiveFourierExtension n f z +
        routeUComplexHardEdgeAliasTail n f r z := by
  simpa only [routeUComplexPositiveFourierExtension,
      routeUComplexHardEdgeAliasTail, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.add_re, Complex.ofReal_re] using
    tsum_routeUAlias_eq_extension_add_tail
      (routeUComplexTilt n f z.im) r z.re hz

/-- **Complex hard-edge alias decay at the actual Cayley phase.**

Every requested even power is available without assuming line placement. The remaining constant
is the Schwartz seminorm of the compact-support imaginary tilt; bounding it uniformly on the Xi
strip is the next, strictly localized HEPW.9 obligation. -/
theorem norm_routeUComplexHardEdgeAliasTail_phase_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (alpha : ℂ) (N : ℕ) :
    ‖routeUComplexHardEdgeAliasTail n f r
        (routeUComplexHardEdgePhase r alpha)‖ ≤
      routeUHardEdgeAliasTailConstant
          (routeUComplexTilt n f (routeUComplexHardEdgePhase r alpha).im) N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  exact norm_routeUHardEdgeAliasTail_le
    (routeUComplexTilt n f (routeUComplexHardEdgePhase r alpha).im) r
    (routeUComplexHardEdgePhase r alpha).re
    (abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod r alpha) N

/-- **Exact complex hard-edge sampling decomposition at the actual Cayley phase.** -/
theorem routeU_complex_hardEdge_periodization_phase_eq_extension_add_tail
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (alpha : ℂ) :
    ((routeUHardEdgeMesh r : ℝ) : ℂ) *
        (∑' k : ℤ,
          Complex.exp
              (Complex.I * routeUComplexHardEdgePhase r alpha *
                (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
            SchwartzMap.compactSupportApproximation n f
              (routeUHardEdgeMesh r * (k : ℝ))) =
      routeUComplexPositiveFourierExtension n f
          (routeUComplexHardEdgePhase r alpha) +
        routeUComplexHardEdgeAliasTail n f r
          (routeUComplexHardEdgePhase r alpha) := by
  rw [routeU_complex_hardEdge_periodization]
  exact tsum_routeUComplexAlias_eq_extension_add_tail n f r
    (routeUComplexHardEdgePhase r alpha)
    (abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod r alpha)

/-- Quantitative complex hard-edge sampling error at every complex spectral point. -/
theorem norm_routeU_complex_hardEdge_periodization_phase_sub_extension_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (alpha : ℂ) (N : ℕ) :
    ‖((routeUHardEdgeMesh r : ℝ) : ℂ) *
          (∑' k : ℤ,
            Complex.exp
                (Complex.I * routeUComplexHardEdgePhase r alpha *
                  (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
              SchwartzMap.compactSupportApproximation n f
                (routeUHardEdgeMesh r * (k : ℝ))) -
        routeUComplexPositiveFourierExtension n f
          (routeUComplexHardEdgePhase r alpha)‖ ≤
      routeUHardEdgeAliasTailConstant
          (routeUComplexTilt n f (routeUComplexHardEdgePhase r alpha).im) N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  rw [routeU_complex_hardEdge_periodization_phase_eq_extension_add_tail]
  simpa only [add_sub_cancel_left] using
    norm_routeUComplexHardEdgeAliasTail_phase_le n f r alpha N

/-- **Premise-free uniform complex HEPW.9 sampling error at every Xi divisor point.**

The error constant is independent of hard-edge mass and divisor height. This is the closed Lean
form needed before summing the sampling error over the infinite Xi divisor. -/
theorem norm_routeU_complex_hardEdge_periodization_xiSpectralPoint_sub_extension_le
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (q : XiZeroCopy) (N : ℕ) :
    ‖((routeUHardEdgeMesh r : ℝ) : ℂ) *
          (∑' k : ℤ,
            Complex.exp
                (Complex.I *
                  routeUComplexHardEdgePhase r (xiSpectralPoint q) *
                  (((routeUHardEdgeMesh r) * (k : ℝ) : ℝ) : ℂ)) *
              SchwartzMap.compactSupportApproximation n f
                (routeUHardEdgeMesh r * (k : ℝ))) -
        routeUComplexPositiveFourierExtension n f
          (routeUComplexHardEdgePhase r (xiSpectralPoint q))‖ ≤
      routeUComplexHardEdgeUniformAliasTailConstant n f N /
        routeUHardEdgeAliasPeriod r ^ ccmRationalArchimedeanDecayExponent N := by
  rw [routeU_complex_hardEdge_periodization_phase_eq_extension_add_tail]
  simpa only [add_sub_cancel_left] using
    norm_routeUComplexHardEdgeAliasTail_xiSpectralPoint_le n f r q N

end RHTower
