import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewUniformBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewLowBand
import GaloisForLFunctions.HTGeometry.ModularDirichletFormDomain

/-!
# The plateau kernel in the covariance variable and the assembled on-line clock bound

The plateau kernel `K(s, μ)` is a rational function of the Laplace harmonic `μ = −l` with
numerator and denominator of degree four.  The bounded covariance `C = (1 − Δ)⁻¹` of the modular
Laplacian has spectrum in `[0, 1]`, and the harmonic `μ` corresponds to the covariance value
`r = 1/(1 − μ)`, i.e. `μ = 1 − 1/r`.  Clearing `r⁴` gives the kernel in the covariance variable,
a rational function `K̂(s, r)` with `K̂(s, r) = K(s, 1 − 1/r)` for `r ≠ 0`, continuous on `[0, 1]`
on the critical line (its denominator has nonzero imaginary part for `0 < r ≤ 1` and value `128`
at `r = 0`), with `K̂(s, 1) = K(s, 0)` the constant-mode kernel.

The certified bounds `Im K(s, −l) ≥ −t⁹` for every harmonic `l ≥ 0` and
`Im K(s, 0) ≥ t¹¹/2176` transfer to `Im K̂(s, ·) ≥ −t⁹` on `[0, 1]` and `Im K̂(s, 1) ≥ t¹¹/2176`,
and the spectral assembly of the modular surface yields the assembled on-line clock bound

`t¹¹/2176 · |∫_𝒟 F|²/vol(𝒟) − t⁹ · ‖F − P₀F‖² ≤ Re ⟪(Im K̂)(C) F, F⟫`

for every `F ∈ L²(𝒟)` and `t ≥ 50`.
-/

open UpperHalfPlane MeasureTheory ModularGroup GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

namespace RHTower.D4BMScalarStream

noncomputable section

/-! ## The numerator by harmonic degree -/

/-- Coefficient of `μ⁰` in the plateau numerator. -/
def skewPlateauCoeff0 (s : ℂ) : ℂ := (-17280 : ℂ) * s + (-97956 : ℂ) * s ^ (2 : ℕ) + (-261744 : ℂ) * s ^ (3 : ℕ) + (-922941 / 2 : ℂ) * s ^ (4 : ℕ) + (-2552481 / 4 : ℂ) * s ^ (5 : ℕ) + (-2979537 / 4 : ℂ) * s ^ (6 : ℕ) + (-723325 : ℂ) * s ^ (7 : ℕ) + (-558684 : ℂ) * s ^ (8 : ℕ) + (-1327433 / 4 : ℂ) * s ^ (9 : ℕ) + (-593769 / 4 : ℂ) * s ^ (10 : ℕ) + (-98021 / 2 : ℂ) * s ^ (11 : ℕ) + (-11583 : ℂ) * s ^ (12 : ℕ) + (-1854 : ℂ) * s ^ (13 : ℕ) + (-180 : ℂ) * s ^ (14 : ℕ) + (-8 : ℂ) * s ^ (15 : ℕ)

/-- Coefficient of `μ¹` in the plateau numerator. -/
def skewPlateauCoeff1 (s : ℂ) : ℂ := (-360 : ℂ) + (15924 : ℂ) * s + (87363 : ℂ) * s ^ (2 : ℕ) + (421985 / 2 : ℂ) * s ^ (3 : ℕ) + (1277613 / 4 : ℂ) * s ^ (4 : ℕ) + (5659371 / 16 : ℂ) * s ^ (5 : ℕ) + (4930203 / 16 : ℂ) * s ^ (6 : ℕ) + (854075 / 4 : ℂ) * s ^ (7 : ℕ) + (917487 / 8 : ℂ) * s ^ (8 : ℕ) + (734643 / 16 : ℂ) * s ^ (9 : ℕ) + (209319 / 16 : ℂ) * s ^ (10 : ℕ) + (19915 / 8 : ℂ) * s ^ (11 : ℕ) + (1131 / 4 : ℂ) * s ^ (12 : ℕ) + (29 / 2 : ℂ) * s ^ (13 : ℕ)

/-- Coefficient of `μ²` in the plateau numerator. -/
def skewPlateauCoeff2 (s : ℂ) : ℂ := (378 : ℂ) + (-3969 : ℂ) * s + (-22095 : ℂ) * s ^ (2 : ℕ) + (-408679 / 8 : ℂ) * s ^ (3 : ℕ) + (-2333337 / 32 : ℂ) * s ^ (4 : ℕ) + (-2339771 / 32 : ℂ) * s ^ (5 : ℕ) + (-1753455 / 32 : ℂ) * s ^ (6 : ℕ) + (-253427 / 8 : ℂ) * s ^ (7 : ℕ) + (-456003 / 32 : ℂ) * s ^ (8 : ℕ) + (-157363 / 32 : ℂ) * s ^ (9 : ℕ) + (-40161 / 32 : ℂ) * s ^ (10 : ℕ) + (-3557 / 16 : ℂ) * s ^ (11 : ℕ) + (-195 / 8 : ℂ) * s ^ (12 : ℕ) + (-5 / 4 : ℂ) * s ^ (13 : ℕ)

/-- Coefficient of `μ³` in the plateau numerator. -/
def skewPlateauCoeff3 (s : ℂ) : ℂ := (-108 : ℂ) + (180 : ℂ) * s + (3015 / 2 : ℂ) * s ^ (2 : ℕ) + (7105 / 2 : ℂ) * s ^ (3 : ℕ) + (78471 / 16 : ℂ) * s ^ (4 : ℕ) + (71715 / 16 : ℂ) * s ^ (5 : ℕ) + (45171 / 16 : ℂ) * s ^ (6 : ℕ) + (4977 / 4 : ℂ) * s ^ (7 : ℕ) + (6129 / 16 : ℂ) * s ^ (8 : ℕ) + (1279 / 16 : ℂ) * s ^ (9 : ℕ) + (165 / 16 : ℂ) * s ^ (10 : ℕ) + (5 / 8 : ℂ) * s ^ (11 : ℕ)

/-- Coefficient of `μ⁴` in the plateau numerator. -/
def skewPlateauCoeff4 (s : ℂ) : ℂ := (9 / 2 : ℂ) + (-33 / 4 : ℂ) * s + (-225 / 8 : ℂ) * s ^ (2 : ℕ) + (-2339 / 32 : ℂ) * s ^ (3 : ℕ) + (-12675 / 128 : ℂ) * s ^ (4 : ℕ) + (-4373 / 64 : ℂ) * s ^ (5 : ℕ) + (-1743 / 64 : ℂ) * s ^ (6 : ℕ) + (-109 / 16 : ℂ) * s ^ (7 : ℕ) + (-135 / 128 : ℂ) * s ^ (8 : ℕ) + (-5 / 64 : ℂ) * s ^ (9 : ℕ)

theorem skewPlateauMuNumerator_eq_coeff (s μ : ℂ) :
    skewPlateauMuNumerator s μ = skewPlateauCoeff0 s + skewPlateauCoeff1 s * μ +
      skewPlateauCoeff2 s * μ ^ (2 : ℕ) + skewPlateauCoeff3 s * μ ^ (3 : ℕ) + skewPlateauCoeff4 s * μ ^ (4 : ℕ) := by
  unfold skewPlateauMuNumerator skewPlateauCoeff0 skewPlateauCoeff1 skewPlateauCoeff2
    skewPlateauCoeff3 skewPlateauCoeff4
  ring

/-! ## The kernel in the covariance variable -/

/-- `r⁴ · N(s, 1 − 1/r)`, a polynomial in `r`. -/
def skewPlateauCovNumerator (s r : ℂ) : ℂ :=
  skewPlateauCoeff0 s * r ^ (4 : ℕ) + skewPlateauCoeff1 s * (r - 1) * r ^ (3 : ℕ) +
    skewPlateauCoeff2 s * (r - 1) ^ (2 : ℕ) * r ^ (2 : ℕ) + skewPlateauCoeff3 s * (r - 1) ^ (3 : ℕ) * r +
    skewPlateauCoeff4 s * (r - 1) ^ (4 : ℕ)

/-- `r⁴ · D(s, 1 − 1/r)`, a polynomial in `r`. -/
def skewPlateauCovDenominator (s r : ℂ) : ℂ :=
  128 * (r + 1) ^ (2 : ℕ) * ((r - 1) - r * ((2 * s + 1) * (2 * s + 2))) *
    ((r - 1) - r * ((2 * s + 4) * (2 * s + 5)))

/-- The plateau kernel in the covariance variable `r = 1/(1 − μ)`. -/
def skewPlateauCov (s r : ℂ) : ℂ := skewPlateauCovNumerator s r / skewPlateauCovDenominator s r

theorem skewPlateauCovNumerator_eq (s r : ℂ) (hr : r ≠ 0) :
    skewPlateauCovNumerator s r = r ^ (4 : ℕ) * skewPlateauMuNumerator s (1 - 1 / r) := by
  rw [skewPlateauMuNumerator_eq_coeff]
  unfold skewPlateauCovNumerator
  field_simp

theorem skewPlateauCovDenominator_eq (s r : ℂ) (hr : r ≠ 0) :
    skewPlateauCovDenominator s r = r ^ (4 : ℕ) * (128 * (2 - (1 - 1 / r)) ^ (2 : ℕ) *
      ((1 - 1 / r) - (2 * s + 1) * (2 * s + 2)) * ((1 - 1 / r) - (2 * s + 4) * (2 * s + 5))) := by
  unfold skewPlateauCovDenominator
  field_simp
  ring

/-- For `r ≠ 0` the covariance-variable kernel is the plateau kernel at the harmonic `1 − 1/r`. -/
theorem skewPlateauCov_eq (s r : ℂ) (hr : r ≠ 0) :
    skewPlateauCov s r = skewPlateauMu s (1 - 1 / r) := by
  unfold skewPlateauCov skewPlateauMu
  rw [skewPlateauCovNumerator_eq s r hr, skewPlateauCovDenominator_eq s r hr,
    mul_div_mul_left _ _ (pow_ne_zero 4 hr)]

/-- At `r = 1` the covariance-variable kernel is the constant-mode kernel. -/
theorem skewPlateauCov_one (s : ℂ) : skewPlateauCov s 1 = skewPlateauMu s 0 := by
  rw [skewPlateauCov_eq s 1 one_ne_zero]
  norm_num

/-! ## The critical line -/

/-- The critical-line parameter `s = −3/2 + it`. -/
def lineParam (t : ℝ) : ℂ := (-3 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem lineParam_factor_one (t : ℝ) :
    (2 * lineParam t + 1) * (2 * lineParam t + 2) =
      ((2 - 4 * t ^ (2 : ℕ) : ℝ) : ℂ) + ((-6 * t : ℝ) : ℂ) * Complex.I := by
  unfold lineParam
  apply Complex.ext <;> simp [pow_two] <;> ring

theorem lineParam_factor_two (t : ℝ) :
    (2 * lineParam t + 4) * (2 * lineParam t + 5) =
      ((2 - 4 * t ^ (2 : ℕ) : ℝ) : ℂ) + ((6 * t : ℝ) : ℂ) * Complex.I := by
  unfold lineParam
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- The covariance-variable denominator does not vanish on `[0, 1]` for `t > 0`. -/
theorem skewPlateauCovDenominator_line_ne_zero (t : ℝ) (ht : 0 < t) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    skewPlateauCovDenominator (lineParam t) (r : ℂ) ≠ 0 := by
  unfold skewPlateauCovDenominator
  rw [lineParam_factor_one, lineParam_factor_two]
  have hA : ((r : ℂ) - 1) - (r : ℂ) * (((2 - 4 * t ^ (2 : ℕ) : ℝ) : ℂ) + ((-6 * t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [pow_two] at him
    rcases him with h0 | h0
    · subst h0
      have hre := congrArg Complex.re h
      simp at hre
    · linarith
  have hB : ((r : ℂ) - 1) - (r : ℂ) * (((2 - 4 * t ^ (2 : ℕ) : ℝ) : ℂ) + ((6 * t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [pow_two] at him
    rcases him with h0 | h0
    · subst h0
      have hre := congrArg Complex.re h
      simp at hre
    · linarith
  have hr1 : ((r : ℂ) + 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hr.1]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr1)) hA) hB

/-- The imaginary part of the covariance-variable kernel on the critical line, as a real function
of the covariance value. -/
def skewCovKernelIm (t : ℝ) (r : ℝ) : ℝ := (skewPlateauCov (lineParam t) (r : ℂ)).im

theorem continuousOn_skewCovKernelIm (t : ℝ) (ht : 0 < t) :
    ContinuousOn (skewCovKernelIm t) (Set.Icc 0 1) := by
  have hnum : Continuous fun r : ℝ => skewPlateauCovNumerator (lineParam t) (r : ℂ) := by
    unfold skewPlateauCovNumerator; fun_prop
  have hden : Continuous fun r : ℝ => skewPlateauCovDenominator (lineParam t) (r : ℂ) := by
    unfold skewPlateauCovDenominator; fun_prop
  have hdiv : ContinuousOn (fun r : ℝ => skewPlateauCov (lineParam t) (r : ℂ)) (Set.Icc 0 1) :=
    hnum.continuousOn.div hden.continuousOn
      (fun r hr => skewPlateauCovDenominator_line_ne_zero t ht hr)
  exact Complex.continuous_im.comp_continuousOn hdiv

/-- On `(0, 1]` the kernel is the plateau kernel at the harmonic `l = 1/r − 1 ≥ 0`, hence
bounded below by `−t⁹`. -/
theorem skewCovKernelIm_ge_neg_of_pos (t : ℝ) (ht : (50 : ℝ) ≤ t) {r : ℝ}
    (hr : r ∈ Set.Ioc (0 : ℝ) 1) : -t ^ (9 : ℕ) ≤ skewCovKernelIm t r := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.1.ne'
  have hl : (0 : ℝ) ≤ 1 / r - 1 := by
    have h1 : 1 ≤ 1 / r := by
      rw [le_div_iff₀ hr.1]; linarith [hr.2]
    linarith
  have hμ : (1 : ℂ) - 1 / (r : ℂ) = -(((1 / r - 1 : ℝ)) : ℂ) := by push_cast; ring
  unfold skewCovKernelIm
  rw [skewPlateauCov_eq _ _ hr0, hμ]
  unfold lineParam
  set l : ℝ := 1 / r - 1 with hldef
  rcases le_or_gt l t with h | h
  · have hlow := skewPlateauMu_low_band_im_ge t l (by linarith) hl h
    have hpos : (0 : ℝ) ≤ t ^ (11 : ℕ) / (544 * (2 + l) ^ (2 : ℕ)) := by positivity
    have ht9 : (0 : ℝ) ≤ t ^ (9 : ℕ) := by positivity
    linarith
  · have habs := skewPlateauMu_line_abs_im_le t l ht h.le
    exact (abs_le.mp habs).1

/-- **Lower bound on the spectrum.**  `Im K̂(s, r) ≥ −t⁹` for every `r ∈ [0, 1]`, `t ≥ 50`. -/
theorem skewCovKernelIm_ge_neg (t : ℝ) (ht : (50 : ℝ) ≤ t) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    -t ^ (9 : ℕ) ≤ skewCovKernelIm t r := by
  have hcl : closure (Set.Ioc (0 : ℝ) 1) = Set.Icc 0 1 := closure_Ioc zero_ne_one
  have hcont := continuousOn_skewCovKernelIm t (by linarith)
  rw [← hcl] at hcont hr
  exact le_on_closure (fun x hx => skewCovKernelIm_ge_neg_of_pos t ht hx) continuousOn_const
    hcont hr

/-- **Constant mode.**  `Im K̂(s, 1) = Im K(s, 0) ≥ t¹¹/2176`. -/
theorem skewCovKernelIm_one_ge (t : ℝ) (ht : (5 : ℝ) ≤ t) : t ^ (11 : ℕ) / 2176 ≤ skewCovKernelIm t 1 := by
  unfold skewCovKernelIm
  rw [Complex.ofReal_one, skewPlateauCov_one]
  have h := skewPlateauMu_constant_mode_im_ge t ht
  simpa [lineParam] using h

/-! ## The assembled on-line clock bound -/

/-- **Assembled on-line clock bound.**  For `t ≥ 50` and every `F ∈ L²(𝒟)`,
`t¹¹/2176 · |⟪1, F⟫|²/‖1‖² − t⁹ · ‖F − P₀F‖² ≤ Re⟪(Im K̂)(C) F, F⟫`, where `C = (1 − Δ)⁻¹` is
the covariance of the modular Dirichlet form and `P₀` the projection onto constants. -/
theorem hb_online_clock_spectral_assembly (t : ℝ) (ht : (50 : ℝ) ≤ t) (F : ModularL2) :
    t ^ (11 : ℕ) / 2176 * (‖⟪modularOne, F⟫_ℂ‖ ^ (2 : ℕ) / ‖modularOne‖ ^ (2 : ℕ)) -
        t ^ (9 : ℕ) * ‖F - (ℂ ∙ modularOne).starProjection F‖ ^ (2 : ℕ) ≤
      RCLike.re ⟪cfc (skewCovKernelIm t) modularCovariance F, F⟫_ℂ := by
  have h := modular_spectral_assembly (continuousOn_skewCovKernelIm t (by linarith))
    (fun x hx => skewCovKernelIm_ge_neg t ht hx) F
  have h1 := skewCovKernelIm_one_ge t (by linarith)
  have hX : 0 ≤ ‖⟪modularOne, F⟫_ℂ‖ ^ (2 : ℕ) / ‖modularOne‖ ^ (2 : ℕ) := by positivity
  have h2 : t ^ (11 : ℕ) / 2176 * (‖⟪modularOne, F⟫_ℂ‖ ^ (2 : ℕ) / ‖modularOne‖ ^ (2 : ℕ)) ≤
      skewCovKernelIm t 1 * (‖⟪modularOne, F⟫_ℂ‖ ^ (2 : ℕ) / ‖modularOne‖ ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_right h1 hX
  linarith

/-- The same bound with the constant mode written as `|∫_𝒟 F|² / vol(𝒟)`. -/
theorem hb_online_clock_spectral_assembly' (t : ℝ) (ht : (50 : ℝ) ≤ t) (F : ModularL2) :
    t ^ (11 : ℕ) / 2176 * (‖∫ z in fd, modularToLp F z ∂volume‖ ^ (2 : ℕ) / ((volume : Measure ℍ) fd).toReal) -
        t ^ (9 : ℕ) * ‖F - (ℂ ∙ modularOne).starProjection F‖ ^ (2 : ℕ) ≤
      RCLike.re ⟪cfc (skewCovKernelIm t) modularCovariance F, F⟫_ℂ := by
  have h := hb_online_clock_spectral_assembly t ht F
  rwa [inner_modularOne, norm_modularOne_sq] at h

end

end RHTower.D4BMScalarStream
