import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.MobiusLaplaceSubpowerCriterion
import GaloisForLFunctions.RHTower.SoninSemilocalGammaShiftedKernel
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# Exact Mellin--Plancherel bridge for the Möbius--Laplace source

After `x = exp(-u)`, the Mellin trace on `Re s = sigma` is the Fourier transform of

`u ↦ exp(-sigma*u) Phi(exp(-u))`.

Whenever this logarithmic source lies in `L¹ ∩ L²`, the classical Mellin integral has exact line
energy

`integral_R |M Phi(sigma+i t)|² dt
  = 2*pi*integral_R |exp(-sigma*u) Phi(exp(-u))|² du`.

This supplies the infinite-aperture harmonic-analysis connector used by the Gamma--Hankel
boundary-zero argument.  It does not prove the required Möbius source belongs to `L²` at any new
abscissa and therefore does not assume or prove RH.
-/

open Complex Real MeasureTheory Set Filter FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace RHTower

private theorem norm_l2_sq_complex_mellinBridge (K : Lp (α := ℝ) ℂ 2) :
    ‖K‖ ^ 2 = ∫ x : ℝ, ‖K x‖ ^ 2 := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable K),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable K)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

/-- Logarithmic source whose Fourier transform is the Mellin trace on `Re s = sigma`. -/
def logMellinLineSource (f : ℝ → ℂ) (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) • f (Real.exp (-u))

/-- Mellin transform in logarithmic coordinates, retaining the full complex exponent. -/
theorem mellin_eq_integral_exp_neg_mul_log
    (f : ℝ → ℂ) (s : ℂ) :
    mellin f s =
      ∫ u : ℝ, Complex.exp (-s * (u : ℂ)) * f (Real.exp (-u)) := by
  rw [mellin_eq_fourier, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  change Complex.exp (((-2 * Real.pi * u * (s.im / (2 * Real.pi)) : ℝ) : ℂ) * I) *
      (((Real.exp (-s.re * u) : ℝ) : ℂ) * f (Real.exp (-u))) =
    Complex.exp (-s * (u : ℂ)) * f (Real.exp (-u))
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  have hphase :
      -2 * Real.pi * u * (s.im / (2 * Real.pi)) = -s.im * u := by
    field_simp
  rw [hphase]
  apply Complex.ext <;> simp

/-- Exact pointwise Mellin--Fourier identity with mathlib's `2*pi` frequency convention. -/
theorem mellin_line_eq_fourier_logMellinLineSource
    (f : ℝ → ℂ) (sigma y : ℝ) :
    mellin f ((sigma : ℂ) + (y : ℂ) * I) =
      𝓕 (logMellinLineSource f sigma) (y / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hsource :
      (fun u : ℝ =>
        Real.exp (-(((sigma : ℂ) + (y : ℂ) * I).re) * u) •
          f (Real.exp (-u))) = logMellinLineSource f sigma := by
    funext u
    simp only [logMellinLineSource, add_re, ofReal_re, mul_re, I_re, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  rw [hsource]
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_add,
    add_zero, zero_mul, mul_one]

/-- The classical Mellin trace has an integrable squared norm whenever its logarithmic source
lies in `L¹ ∩ L²`.  This is the integrability companion to the exact Plancherel identity below. -/
theorem integrable_norm_sq_mellin_line_of_logMellinLineSource
    {f : ℝ → ℂ} {sigma : ℝ}
    (h1 : Integrable (logMellinLineSource f sigma))
    (h2 : MemLp (logMellinLineSource f sigma) 2 volume) :
    Integrable (fun y : ℝ =>
      ‖mellin f ((sigma : ℂ) + (y : ℂ) * I)‖ ^ 2) := by
  let g : ℝ → ℂ := logMellinLineSource f sigma
  let g2 : Lp ℂ 2 volume := h2.toLp g
  have hcoe : (g2 : ℝ → ℂ) =ᵐ[volume] g := by
    simpa [g, g2] using h2.coeFn_toLp
  have hg2int : Integrable (g2 : ℝ → ℂ) := h1.congr hcoe.symm
  have hfourAE : ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
    calc
      ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          (Real.Lp.fourierTransform
            ((memLp_one_iff_integrable.mpr hg2int).toLp g2) : ℝ → ℂ) :=
        l2_fourier_coeFn_eq_l1_fourier_of_integrable g2 hg2int
      _ =ᵐ[volume] 𝓕 g := Eventually.of_forall fun x => by
        rw [Real.fourierTransform_toLp]
        exact Real.fourier_congr_ae hcoe x
  have hfourMem : MemLp
      (fun x : ℝ => (𝓕 g2 : Lp ℂ 2 volume) x) 2 volume :=
    Lp.memLp (𝓕 g2 : Lp ℂ 2 volume)
  have hfourSq : Integrable
      (fun x : ℝ => ‖(𝓕 g2 : Lp ℂ 2 volume) x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfourMem.1).mp hfourMem
  have hgFourSq : Integrable (fun x : ℝ => ‖𝓕 g x‖ ^ 2) :=
    hfourSq.congr (hfourAE.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hscaled := hgFourSq.comp_div
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  apply hscaled.congr
  filter_upwards [] with y
  rw [mellin_line_eq_fourier_logMellinLineSource]

/-- **Exact Mellin--Plancherel line law.** `L¹` identifies the classical Fourier integral with
the unitary `L²` transform; Plancherel and frequency rescaling then give the stated factor
`2*pi`. -/
theorem integral_norm_sq_mellin_line_eq_logMellinLineSource
    {f : ℝ → ℂ} {sigma : ℝ}
    (h1 : Integrable (logMellinLineSource f sigma))
    (h2 : MemLp (logMellinLineSource f sigma) 2 volume) :
    (∫ y : ℝ, ‖mellin f ((sigma : ℂ) + (y : ℂ) * I)‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, ‖logMellinLineSource f sigma u‖ ^ 2 := by
  let g : ℝ → ℂ := logMellinLineSource f sigma
  let g2 : Lp ℂ 2 volume := h2.toLp g
  have hcoe : (g2 : ℝ → ℂ) =ᵐ[volume] g := by
    simpa [g, g2] using h2.coeFn_toLp
  have hg2int : Integrable (g2 : ℝ → ℂ) := h1.congr hcoe.symm
  have hfourAE : ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
    calc
      ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          (Real.Lp.fourierTransform
            ((memLp_one_iff_integrable.mpr hg2int).toLp g2) : ℝ → ℂ) :=
        l2_fourier_coeFn_eq_l1_fourier_of_integrable g2 hg2int
      _ =ᵐ[volume] 𝓕 g := Eventually.of_forall fun x => by
        rw [Real.fourierTransform_toLp]
        exact Real.fourier_congr_ae hcoe x
  have hplancherel :
      (∫ x : ℝ, ‖𝓕 g x‖ ^ 2) = ∫ u : ℝ, ‖g u‖ ^ 2 := by
    calc
      (∫ x : ℝ, ‖𝓕 g x‖ ^ 2) =
          ∫ x : ℝ, ‖(𝓕 g2 : Lp ℂ 2 volume) x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hfourAE] with x hx
        rw [hx]
      _ = ‖(𝓕 g2 : Lp ℂ 2 volume)‖ ^ 2 :=
        (norm_l2_sq_complex_mellinBridge (𝓕 g2 : Lp ℂ 2 volume)).symm
      _ = ‖g2‖ ^ 2 := by rw [Lp.norm_fourier_eq]
      _ = ∫ u : ℝ, ‖g2 u‖ ^ 2 := norm_l2_sq_complex_mellinBridge g2
      _ = ∫ u : ℝ, ‖g u‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hcoe] with u hu
        rw [hu]
  have hline : (fun y : ℝ =>
      ‖mellin f ((sigma : ℂ) + (y : ℂ) * I)‖ ^ 2) =
      fun y : ℝ => ‖𝓕 g (y / (2 * Real.pi))‖ ^ 2 := by
    funext y
    rw [mellin_line_eq_fourier_logMellinLineSource]
  rw [hline]
  let H : ℝ → ℝ := fun x => ‖𝓕 g x‖ ^ 2
  have hscale := MeasureTheory.Measure.integral_comp_div H (2 * Real.pi)
  rw [hscale]
  rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  simp only [smul_eq_mul]
  rw [hplancherel]

/-- A pointwise `c/r` floor on a centered window of radius `r` forces at least
`2*c²/r` total squared energy. -/
theorem integral_norm_sq_ge_two_mul_sq_div_of_window_floor
    {F : ℝ → ℂ} {gamma r c : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c)
    (hF : Integrable (fun t : ℝ => ‖F t‖ ^ 2))
    (hfloor : ∀ t : ℝ, |t - gamma| ≤ r → c / r ≤ ‖F t‖) :
    2 * c ^ 2 / r ≤ ∫ t : ℝ, ‖F t‖ ^ 2 := by
  let S : Set ℝ := Icc (gamma - r) (gamma + r)
  let K : ℝ := (c / r) ^ 2
  have hconst : Integrable (fun _ : ℝ => K) (volume.restrict S) :=
    integrableOn_const (by simp [S])
  have htarget : Integrable (fun t : ℝ => ‖F t‖ ^ 2) (volume.restrict S) :=
    hF.mono_measure Measure.restrict_le_self
  have hlocal : (∫ _ : ℝ in S, K) ≤ ∫ t : ℝ in S, ‖F t‖ ^ 2 := by
    apply integral_mono_ae hconst htarget
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have habs : |t - gamma| ≤ r := by
      dsimp only [S] at ht
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact (sq_le_sq₀ (div_nonneg hc hr.le) (norm_nonneg (F t))).2 (hfloor t habs)
  have hglobal : (∫ t : ℝ in S, ‖F t‖ ^ 2) ≤ ∫ t : ℝ, ‖F t‖ ^ 2 := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖F t‖)) hF
  calc
    2 * c ^ 2 / r = (∫ _ : ℝ in S, K) := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc]
      simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ gamma + r - (gamma - r)),
        smul_eq_mul]
      dsimp only [K]
      field_simp [hr.ne']
      ring
    _ ≤ ∫ t : ℝ in S, ‖F t‖ ^ 2 := hlocal
    _ ≤ ∫ t : ℝ, ‖F t‖ ^ 2 := hglobal

/-- Möbius specialization of the logarithmic Mellin source. -/
def mobiusLaplaceLogMellinLineSource (sigma u : ℝ) : ℂ :=
  logMellinLineSource mobiusDiscreteLaplaceTransform sigma u

/-- The logarithmic Möbius--Laplace Mellin source is continuous on every vertical line. -/
theorem continuous_mobiusLaplaceLogMellinLineSource (sigma : ℝ) :
    Continuous (mobiusLaplaceLogMellinLineSource sigma) := by
  have hcomp : Continuous (fun u : ℝ =>
      mobiusDiscreteLaplaceTransform (Real.exp (-u))) := by
    apply continuousOn_univ.mp
    simpa only [Function.comp_def] using
      continuousOn_mobiusDiscreteLaplaceTransform.comp
        (by fun_prop : ContinuousOn (fun v : ℝ => Real.exp (-v)) univ)
        (fun u _ => Real.exp_pos (-u))
  unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
  fun_prop

/-- Log-coordinate integrand for the concrete Möbius Mellin transform. -/
def mobiusLaplaceMellinLogIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-s * (u : ℂ)) * mobiusDiscreteLaplaceTransform (Real.exp (-u))

/-- Parameter derivative of the log-coordinate Möbius Mellin integrand. -/
def mobiusLaplaceMellinLogIntegrandDeriv (s : ℂ) (u : ℝ) : ℂ :=
  (-(u : ℂ)) * Complex.exp (-s * (u : ℂ)) *
    mobiusDiscreteLaplaceTransform (Real.exp (-u))

theorem continuous_mobiusLaplaceMellinLogIntegrand (s : ℂ) :
    Continuous (mobiusLaplaceMellinLogIntegrand s) := by
  have hcomp : Continuous (fun u : ℝ =>
      mobiusDiscreteLaplaceTransform (Real.exp (-u))) := by
    apply continuousOn_univ.mp
    simpa only [Function.comp_def] using
      continuousOn_mobiusDiscreteLaplaceTransform.comp
        (by fun_prop : ContinuousOn (fun v : ℝ => Real.exp (-v)) univ)
        (fun u _ => Real.exp_pos (-u))
  unfold mobiusLaplaceMellinLogIntegrand
  fun_prop

theorem continuous_mobiusLaplaceMellinLogIntegrandDeriv (s : ℂ) :
    Continuous (mobiusLaplaceMellinLogIntegrandDeriv s) := by
  have hcomp : Continuous (fun u : ℝ =>
      mobiusDiscreteLaplaceTransform (Real.exp (-u))) := by
    apply continuousOn_univ.mp
    simpa only [Function.comp_def] using
      continuousOn_mobiusDiscreteLaplaceTransform.comp
        (by fun_prop : ContinuousOn (fun v : ℝ => Real.exp (-v)) univ)
        (fun u _ => Real.exp_pos (-u))
  unfold mobiusLaplaceMellinLogIntegrandDeriv
  fun_prop

theorem norm_mobiusLaplaceMellinLogIntegrand (s : ℂ) (u : ℝ) :
    ‖mobiusLaplaceMellinLogIntegrand s u‖ =
      ‖mobiusLaplaceLogMellinLineSource s.re u‖ := by
  unfold mobiusLaplaceMellinLogIntegrand mobiusLaplaceLogMellinLineSource
    logMellinLineSource
  rw [norm_mul, Complex.norm_exp, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  congr 1
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

theorem norm_mobiusLaplaceMellinLogIntegrandDeriv (s : ℂ) (u : ℝ) :
    ‖mobiusLaplaceMellinLogIntegrandDeriv s u‖ =
      |u| * ‖mobiusLaplaceLogMellinLineSource s.re u‖ := by
  unfold mobiusLaplaceMellinLogIntegrandDeriv
  rw [mul_assoc]
  change ‖(-(u : ℂ)) * mobiusLaplaceMellinLogIntegrand s u‖ = _
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    norm_mobiusLaplaceMellinLogIntegrand]

/-- Moving right by `r` exponentially tilts the base logarithmic Mellin source. -/
theorem mobiusLaplaceLogMellinLineSource_add
    (sigma r u : ℝ) :
    mobiusLaplaceLogMellinLineSource (sigma + r) u =
      Real.exp (-r * u) • mobiusLaplaceLogMellinLineSource sigma u := by
  unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
  rw [← smul_assoc]
  congr 1
  simp only [smul_eq_mul]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- Exact norm comparison between two logarithmic Mellin lines. -/
theorem norm_mobiusLaplaceLogMellinLineSource_eq_exp_sub_mul
    (a b u : ℝ) :
    ‖mobiusLaplaceLogMellinLineSource a u‖ =
      Real.exp ((b - a) * u) * ‖mobiusLaplaceLogMellinLineSource b u‖ := by
  unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- A derivative weight at any parameter in a real interval is dominated by the two outer Mellin
lines.  The two-line envelope is the local normal-family mechanism behind base-energy
continuation. -/
theorem abs_mul_norm_mobiusLaplaceLogMellinLineSource_le_outer
    {center v y u : ℝ} (hv : 0 < v) (hy : |y - center| < v) :
    |u| * ‖mobiusLaplaceLogMellinLineSource y u‖ ≤
      (1 / v) *
        (‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖ +
          ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖) := by
  rcases abs_lt.mp hy with ⟨hyLower, hyUpper⟩
  by_cases hu : 0 ≤ u
  · have hgap : 0 ≤ y - (center - 2 * v) - v := by linarith
    have hgapMul : 0 ≤ (y - (center - 2 * v) - v) * u :=
      mul_nonneg hgap hu
    have hexp :
        Real.exp (((center - 2 * v) - y) * u) ≤ Real.exp (-v * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpow := pow_mul_exp_neg_le (mul_nonneg hv.le hu) 1
    have hdecay : u * Real.exp (-v * u) ≤ 1 / v := by
      apply (le_div_iff₀ hv).2
      simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using hpow
    have hcoef : u * Real.exp (((center - 2 * v) - y) * u) ≤ 1 / v := by
      calc
        u * Real.exp (((center - 2 * v) - y) * u) ≤
            u * Real.exp (-v * u) := mul_le_mul_of_nonneg_left hexp hu
        _ ≤ 1 / v := hdecay
    rw [norm_mobiusLaplaceLogMellinLineSource_eq_exp_sub_mul y (center - 2 * v) u,
      abs_of_nonneg hu]
    calc
      u * (Real.exp (((center - 2 * v) - y) * u) *
          ‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖) =
          (u * Real.exp (((center - 2 * v) - y) * u)) *
            ‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖ := by ring
      _ ≤ (1 / v) * ‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ (1 / v) *
          (‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖ +
            ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
          (one_div_nonneg.mpr hv.le)
  · have hu0 : u ≤ 0 := le_of_not_ge hu
    have hgap : 0 ≤ center + 2 * v - y - v := by linarith
    have hgapMul : (center + 2 * v - y - v) * u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hgap hu0
    have hexp :
        Real.exp ((center + 2 * v - y) * u) ≤ Real.exp (v * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hwu : 0 ≤ v * (-u) := mul_nonneg hv.le (neg_nonneg.mpr hu0)
    have hpow := pow_mul_exp_neg_le hwu 1
    have hdecay : (-u) * Real.exp (v * u) ≤ 1 / v := by
      apply (le_div_iff₀ hv).2
      simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using hpow
    have hcoef : (-u) * Real.exp ((center + 2 * v - y) * u) ≤ 1 / v := by
      calc
        (-u) * Real.exp ((center + 2 * v - y) * u) ≤
            (-u) * Real.exp (v * u) :=
          mul_le_mul_of_nonneg_left hexp (neg_nonneg.mpr hu0)
        _ ≤ 1 / v := hdecay
    rw [norm_mobiusLaplaceLogMellinLineSource_eq_exp_sub_mul y (center + 2 * v) u,
      abs_of_nonpos hu0]
    calc
      -u * (Real.exp ((center + 2 * v - y) * u) *
          ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖) =
          ((-u) * Real.exp ((center + 2 * v - y) * u)) *
            ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖ := by ring
      _ ≤ (1 / v) * ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ ≤ (1 / v) *
          (‖mobiusLaplaceLogMellinLineSource (center - 2 * v) u‖ +
            ‖mobiusLaplaceLogMellinLineSource (center + 2 * v) u‖) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
          (one_div_nonneg.mpr hv.le)

/-- The elementary `|Phi(x)| ≤ 1/x` bound gives a global exponential majorant in logarithmic
coordinates. -/
theorem norm_mobiusLaplaceLogMellinLineSource_le_exp (a u : ℝ) :
    ‖mobiusLaplaceLogMellinLineSource a u‖ ≤ Real.exp ((1 - a) * u) := by
  unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hx := norm_mobiusDiscreteLaplaceTransform_le_inv (Real.exp_pos (-u))
  calc
    Real.exp (-a * u) * ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖ ≤
        Real.exp (-a * u) * (1 / Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _)
    _ = Real.exp ((1 - a) * u) := by
      rw [one_div, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring_nf

/-- Backward-compatible specialization of the global elementary majorant to nonpositive
logarithmic coordinates. -/
theorem norm_mobiusLaplaceLogMellinLineSource_le_exp_of_nonpos
    {a u : ℝ} (_hu : u ≤ 0) :
    ‖mobiusLaplaceLogMellinLineSource a u‖ ≤ Real.exp ((1 - a) * u) :=
  norm_mobiusLaplaceLogMellinLineSource_le_exp a u

/-- The actual exponential Laplace tail becomes superexponential in negative logarithmic
coordinates.  Any requested real Mellin exponent is absorbed by one factorial term. -/
theorem norm_mobiusLaplaceLogMellinLineSource_le_factorial_exp_of_nonpos
    (a : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ‖mobiusLaplaceLogMellinLineSource a u‖ ≤
      (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial n : ℝ) *
        Real.exp (((n : ℝ) - a) * u) := by
  unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hx : 1 ≤ Real.exp (-u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hphi := norm_mobiusDiscreteLaplaceTransform_le_exp_neg hx
  have hseries : 0 ≤ ∑' k : ℕ, Real.exp (-(k : ℝ)) :=
    tsum_nonneg fun _ => (Real.exp_nonneg _)
  have hsuper := exp_neg_exp_neg_le_factorial_mul_exp_nat_mul n u
  calc
    Real.exp (-a * u) *
        ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖ ≤
        Real.exp (-a * u) *
          (Real.exp (-Real.exp (-u)) *
            ∑' k : ℕ, Real.exp (-(k : ℝ))) :=
      mul_le_mul_of_nonneg_left hphi (Real.exp_nonneg _)
    _ = (∑' k : ℕ, Real.exp (-(k : ℝ))) *
          (Real.exp (-a * u) * Real.exp (-Real.exp (-u))) := by ring
    _ ≤ (∑' k : ℕ, Real.exp (-(k : ℝ))) *
          (Real.exp (-a * u) *
            ((Nat.factorial n : ℝ) * Real.exp ((n : ℝ) * u))) := by
      gcongr
    _ = (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial n : ℝ) *
          (Real.exp (-a * u) * Real.exp ((n : ℝ) * u)) := by ring
    _ = (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial n : ℝ) *
          Real.exp (((n : ℝ) - a) * u) := by
      rw [← Real.exp_add]
      ring_nf

/-- Every logarithmic Mellin line has an integrable negative-coordinate tail. -/
theorem integrableOn_mobiusLaplaceLogMellinLineSource_Iic (a : ℝ) :
    IntegrableOn (mobiusLaplaceLogMellinLineSource a) (Iic 0) := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt a
  let C : ℝ :=
    (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial n : ℝ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (tsum_nonneg fun _ => Real.exp_nonneg _) (by positivity)
  have hmajor : IntegrableOn
      (fun u : ℝ => C * Real.exp (((n : ℝ) - a) * u)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).const_mul C
  refine hmajor.mono'
    ((continuous_mobiusLaplaceLogMellinLineSource a).aestronglyMeasurable
      |>.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  simpa only [C] using
    norm_mobiusLaplaceLogMellinLineSource_le_factorial_exp_of_nonpos a n hu

/-- Every logarithmic Mellin line has a square-integrable negative-coordinate tail. -/
theorem integrableOn_norm_sq_mobiusLaplaceLogMellinLineSource_Iic (a : ℝ) :
    IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource a u‖ ^ 2) (Iic 0) := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt a
  let C : ℝ :=
    (∑' k : ℕ, Real.exp (-(k : ℝ))) * (Nat.factorial n : ℝ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (tsum_nonneg fun _ => Real.exp_nonneg _) (by positivity)
  have hmajor : IntegrableOn
      (fun u : ℝ => C ^ 2 * Real.exp ((2 * ((n : ℝ) - a)) * u)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).const_mul (C ^ 2)
  refine hmajor.mono'
    ((continuous_mobiusLaplaceLogMellinLineSource a).aestronglyMeasurable.norm.pow 2
      |>.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have htail :=
    norm_mobiusLaplaceLogMellinLineSource_le_factorial_exp_of_nonpos a n hu
  have hmajorNonneg : 0 ≤ C * Real.exp (((n : ℝ) - a) * u) :=
    mul_nonneg hC (Real.exp_nonneg _)
  have hsq :
      ‖mobiusLaplaceLogMellinLineSource a u‖ ^ 2 ≤
        (C * Real.exp (((n : ℝ) - a) * u)) ^ 2 := by
    nlinarith [norm_nonneg (mobiusLaplaceLogMellinLineSource a u)]
  calc
    ‖mobiusLaplaceLogMellinLineSource a u‖ ^ 2 ≤
        (C * Real.exp (((n : ℝ) - a) * u)) ^ 2 := hsq
    _ = C ^ 2 * Real.exp ((2 * ((n : ℝ) - a)) * u) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf

/-- Every line strictly right of absolute convergence has finite logarithmic `L²` energy.  This
is unconditional and uses no cancellation: on `u > 0`, the crude `|Phi(x)| ≤ 1/x` estimate gives
`exp((1-sigma)u)`; on `u ≤ 0`, the actual Laplace tail is superexponential. -/
theorem mobiusLaplaceLogMellinLineSource_memLp_two_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) :
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume := by
  have hmajor : IntegrableOn
      (fun u : ℝ => Real.exp ((2 * (1 - sigma)) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hpos : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) (Ioi 0) := by
    refine hmajor.mono'
      ((continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable.norm.pow 2
        |>.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hnorm := norm_mobiusLaplaceLogMellinLineSource_le_exp sigma u
    have hexp : 0 ≤ Real.exp ((1 - sigma) * u) := Real.exp_nonneg _
    calc
      ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 ≤
          Real.exp ((1 - sigma) * u) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hexp).2 hnorm
      _ = Real.exp ((2 * (1 - sigma)) * u) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf
  have hneg := integrableOn_norm_sq_mobiusLaplaceLogMellinLineSource_Iic sigma
  have hmeas : AEStronglyMeasurable
      (mobiusLaplaceLogMellinLineSource sigma) volume :=
    (continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- Finite base-line `L²` energy propagates to every strict right shift.

The positive logarithmic half is a contractive exponential tilt; the negative half has the
unconditional superexponential Laplace tail. -/
theorem mobiusLaplaceLogMellinLineSource_memLp_two_of_base
    {sigma r : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    (hr : 0 < r) :
    MemLp (mobiusLaplaceLogMellinLineSource (sigma + r)) 2 volume := by
  have htargetMeas : AEStronglyMeasurable
      (mobiusLaplaceLogMellinLineSource (sigma + r)) volume :=
    (continuous_mobiusLaplaceLogMellinLineSource (sigma + r)).aestronglyMeasurable
  have hbaseSq : Integrable
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hbase.1).mp hbase
  have hpos : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2)
      (Ioi 0) := by
    refine hbaseSq.integrableOn.mono'
      (htargetMeas.norm.pow 2 |>.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [mobiusLaplaceLogMellinLineSource_add, norm_smul,
      Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow]
    have hu0 : 0 < u := hu
    have hexp : Real.exp (-r * u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hexpSq : Real.exp (-r * u) ^ 2 ≤ 1 := by
      nlinarith [Real.exp_nonneg (-r * u)]
    calc
      Real.exp (-r * u) ^ 2 *
          ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 ≤
          1 * ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hexpSq (sq_nonneg _)
      _ = ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 := one_mul _
  have hneg : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2)
      (Iic 0) :=
    integrableOn_norm_sq_mobiusLaplaceLogMellinLineSource_Iic (sigma + r)
  apply (memLp_two_iff_integrable_sq_norm htargetMeas).2
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- The same finite base `L²` energy supplies `L¹` on each strictly interior line.  The positive
half uses Cauchy--Schwarz against the exponential tilt, while the negative half is elementary. -/
theorem integrable_mobiusLaplaceLogMellinLineSource_of_base
    {sigma r : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    (hr : 0 < r) :
    Integrable (mobiusLaplaceLogMellinLineSource (sigma + r)) volume := by
  have htargetMeas : AEStronglyMeasurable
      (mobiusLaplaceLogMellinLineSource (sigma + r)) volume :=
    (continuous_mobiusLaplaceLogMellinLineSource (sigma + r)).aestronglyMeasurable
  have hdecayMem : MemLp (fun u : ℝ => (Real.exp (-r * u) : ℂ)) 2
      (volume.restrict (Ioi 0)) := by
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => (Real.exp (-r * u) : ℂ)) (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous (fun u : ℝ => (Real.exp (-r * u) : ℂ)))
        |>.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    have h := integrableOn_exp_mul_Ioi (a := -2 * r) (by linarith) 0
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hbaseRestrict : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2
      (volume.restrict (Ioi 0)) :=
    hbase.mono_measure Measure.restrict_le_self
  have hposProduct : Integrable
      ((fun u : ℝ => (Real.exp (-r * u) : ℂ)) *
        mobiusLaplaceLogMellinLineSource sigma)
      (volume.restrict (Ioi 0)) :=
    hdecayMem.integrable_mul hbaseRestrict
  have hpos : IntegrableOn
      (mobiusLaplaceLogMellinLineSource (sigma + r)) (Ioi 0) := by
    apply hposProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Pi.mul_apply, mobiusLaplaceLogMellinLineSource_add, Complex.real_smul]
  have hneg : IntegrableOn
      (mobiusLaplaceLogMellinLineSource (sigma + r)) (Iic 0) :=
    integrableOn_mobiusLaplaceLogMellinLineSource_Iic (sigma + r)
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- Finite base-line `L²` energy makes the concrete Mellin transform holomorphic at every strict
right shift.  This is a Hardy-space continuation theorem: no pointwise source decay is assumed. -/
theorem differentiableAt_mellin_mobiusDiscreteLaplaceTransform_of_base
    {sigma : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    {s : ℂ} (hs : sigma < s.re) :
    DifferentiableAt ℂ (mellin mobiusDiscreteLaplaceTransform) s := by
  let v : ℝ := (s.re - sigma) / 4
  have hv : 0 < v := by dsimp only [v]; linarith
  have hminusShift : 0 < (s.re - 2 * v) - sigma := by
    dsimp only [v]
    linarith
  have hplusShift : 0 < (s.re + 2 * v) - sigma := by
    dsimp only [v]
    linarith
  have hcenterShift : 0 < s.re - sigma := sub_pos.mpr hs
  have hminus : Integrable
      (mobiusLaplaceLogMellinLineSource (s.re - 2 * v)) := by
    convert integrable_mobiusLaplaceLogMellinLineSource_of_base
      (sigma := sigma) (r := (s.re - 2 * v) - sigma) hbase hminusShift using 1 ;
      ring_nf
  have hplus : Integrable
      (mobiusLaplaceLogMellinLineSource (s.re + 2 * v)) := by
    convert integrable_mobiusLaplaceLogMellinLineSource_of_base
      (sigma := sigma) (r := (s.re + 2 * v) - sigma) hbase hplusShift using 1 ;
      ring_nf
  have hcenter : Integrable
      (mobiusLaplaceLogMellinLineSource s.re) := by
    convert integrable_mobiusLaplaceLogMellinLineSource_of_base
      (sigma := sigma) (r := s.re - sigma) hbase hcenterShift using 1 ;
      ring_nf
  let bound : ℝ → ℝ := fun u =>
    (1 / v) *
      (‖mobiusLaplaceLogMellinLineSource (s.re - 2 * v) u‖ +
        ‖mobiusLaplaceLogMellinLineSource (s.re + 2 * v) u‖)
  have hbound : Integrable bound := by
    simpa only [bound] using! (hminus.norm.add hplus.norm).const_mul (1 / v)
  have hFmeas : ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (mobiusLaplaceMellinLogIntegrand z) := by
    filter_upwards with z
    exact (continuous_mobiusLaplaceMellinLogIntegrand z).aestronglyMeasurable
  have hFint : Integrable (mobiusLaplaceMellinLogIntegrand s) := by
    refine hcenter.mono
      (continuous_mobiusLaplaceMellinLogIntegrand s).aestronglyMeasurable ?_
    filter_upwards with u
    exact le_of_eq (norm_mobiusLaplaceMellinLogIntegrand s u)
  have hF'meas : AEStronglyMeasurable
      (mobiusLaplaceMellinLogIntegrandDeriv s) :=
    (continuous_mobiusLaplaceMellinLogIntegrandDeriv s).aestronglyMeasurable
  have hdom : ∀ᵐ u : ℝ,
      ∀ z ∈ Metric.ball s v,
        ‖mobiusLaplaceMellinLogIntegrandDeriv z u‖ ≤ bound u := by
    filter_upwards with u
    intro z hz
    have hreNorm : |z.re - s.re| ≤ ‖z - s‖ := by
      simpa only [sub_re] using abs_re_le_norm (z - s)
    have hre : |z.re - s.re| < v := by
      exact hreNorm.trans_lt (by simpa [dist_eq_norm] using hz)
    rw [norm_mobiusLaplaceMellinLogIntegrandDeriv]
    exact abs_mul_norm_mobiusLaplaceLogMellinLineSource_le_outer hv hre
  have hdiff : ∀ᵐ u : ℝ,
      ∀ z ∈ Metric.ball s v,
        HasDerivAt (fun q : ℂ => mobiusLaplaceMellinLogIntegrand q u)
          (mobiusLaplaceMellinLogIntegrandDeriv z u) z := by
    filter_upwards with u
    intro z hz
    have hinner : HasDerivAt (fun q : ℂ => -q * (u : ℂ)) (-(u : ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (u : ℂ)
    unfold mobiusLaplaceMellinLogIntegrand mobiusLaplaceMellinLogIntegrandDeriv
    simpa using!
      (hinner.cexp.mul_const
        (mobiusDiscreteLaplaceTransform (Real.exp (-u)))).congr_deriv (by ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := mobiusLaplaceMellinLogIntegrand)
    (F' := mobiusLaplaceMellinLogIntegrandDeriv)
    (bound := bound) (Metric.ball_mem_nhds s hv) hFmeas hFint hF'meas hdom hbound hdiff
  rw [show mellin mobiusDiscreteLaplaceTransform =
      fun z : ℂ => ∫ u : ℝ, mobiusLaplaceMellinLogIntegrand z u by
    funext z
    exact mellin_eq_integral_exp_neg_mul_log mobiusDiscreteLaplaceTransform z]
  exact hmain.2.differentiableAt

/-- Open half-plane on which one finite base energy continues the concrete Möbius Mellin
transform. -/
def mobiusLaplaceEnergyRightHalf (sigma : ℝ) : Set ℂ :=
  {s : ℂ | sigma < s.re}

theorem isOpen_mobiusLaplaceEnergyRightHalf (sigma : ℝ) :
    IsOpen (mobiusLaplaceEnergyRightHalf sigma) :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Analytic continuation generated by one finite base `L²` energy. -/
theorem analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_base
    {sigma : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume) :
    AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform)
      (mobiusLaplaceEnergyRightHalf sigma) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_mobiusLaplaceEnergyRightHalf sigma)
  intro s hs
  exact (differentiableAt_mellin_mobiusDiscreteLaplaceTransform_of_base hbase hs)
    |>.differentiableWithinAt

/-- One finite base energy propagates the denominator-free classical identity from `Re s > 1`
to the full energy half-plane. -/
theorem mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume) :
    ∀ s ∈ mobiusLaplaceEnergyRightHalf sigma,
      mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s =
        Complex.Gamma s * (s - 1) := by
  let U : Set ℂ := mobiusLaplaceEnergyRightHalf sigma
  let G : ℂ → ℂ := mellin mobiusDiscreteLaplaceTransform
  have hG : AnalyticOnNhd ℂ G U :=
    analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_base hbase
  have hleft : AnalyticOnNhd ℂ (fun s => G s * zetaResidueUnit s) U := by
    intro s hs
    exact (hG s hs).mul (RHTower.analyticAt_zetaResidueUnit s)
  have hright : AnalyticOnNhd ℂ (fun s => Complex.Gamma s * (s - 1)) U := by
    intro s hs
    have hspos : 0 < s.re := hsigma.trans (show sigma < s.re from hs)
    exact (HTGeometry.analyticAt_Gamma_of_re_pos hspos).mul
      (analyticAt_id.sub analyticAt_const)
  let A : ℝ := max sigma 1 + 1
  have hAone : 1 < A := by dsimp only [A]; linarith [le_max_right sigma 1]
  have hAsigma : sigma < A := by dsimp only [A]; linarith [le_max_left sigma 1]
  have hAU : (A : ℂ) ∈ U := by exact hAsigma
  have hevent :
      (fun s => G s * zetaResidueUnit s) =ᶠ[𝓝 (A : ℂ)]
        (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (A : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hAone
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro hsone
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [show G s = Complex.Gamma s * (riemannZeta s)⁻¹ by
      simpa [G] using mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (by simpa only [U, mobiusLaplaceEnergyRightHalf] using
      (convex_halfSpace_re_gt sigma).isPreconnected) hAU hevent

/-- Finite base energy excludes every genuine zeta zero in the strict right half-plane. -/
theorem riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    {s : ℂ} (hs : sigma < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  have hidentity :=
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
      hsigma hbase s hs
  have hresidue : zetaResidueUnit s = 0 := by
    simp [zetaResidueUnit, hs1, hzeta]
  rw [hresidue, mul_zero] at hidentity
  have hspos : 0 < s.re := hsigma.trans hs
  exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hspos)
    (sub_ne_zero.mpr hs1)) hidentity.symm

/-- A zero on the boundary of a canonical Mellin half-plane forces a `c/r` norm floor on a
vertical window of radius `r` just inside the half-plane.  Exact zero multiplicity only strengthens
the singularity; the theorem records the universal simple-pole floor needed for `L²` contradiction. -/
theorem exists_boundary_zero_vertical_window_floor_of_canonical_identity
    {G : ℂ → ℂ} {sigma : ℝ} {rho : ℂ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hrho : rho.re = sigma) (hzero : riemannZeta rho = 0)
    (hidentity : ∀ z : ℂ, sigma < z.re →
      G z * zetaResidueUnit z = Complex.Gamma z * (z - 1)) :
    ∃ c > 0, ∃ delta > 0, ∀ r : ℝ, 0 < r → r < delta →
      ∀ t : ℝ, |t - rho.im| ≤ r →
        c / r ≤ ‖G (((sigma + r : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
    linarith
  have hrhoPos : 0 < rho.re := by rw [hrho]; exact hsigma
  have hstrip : 0 < rho.re ∧ rho.re < 1 := by
    rw [hrho]
    exact ⟨hsigma, hsigmaOne⟩
  have horderEq := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have horderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [← horderEq]
    exact xi_orderAt_ne_top rho
  let n : ℕ := (analyticOrderAt riemannZeta rho).toNat
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta rho :=
    ENat.coe_toNat horderFinite
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrhoOne
  obtain ⟨p, hp, hpzero, hfactor⟩ :=
    (hzetaAnalytic.analyticOrderAt_eq_natCast).mp hncoe.symm
  have hnzero : n ≠ 0 := by
    intro hn
    have horderZero : analyticOrderAt riemannZeta rho = 0 := by
      rw [← hncoe, hn]
      simp
    exact (analyticOrderAt_ne_zero.mpr ⟨hzetaAnalytic, hzero⟩) horderZero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  let q : ℂ → ℂ := fun z => Complex.Gamma z / p z
  have hqcont : ContinuousAt q rho := by
    exact (Complex.continuousAt_Gamma rho hnotGammaPole).div hp.continuousAt hpzero
  have hqzero : q rho ≠ 0 := by
    exact div_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos) hpzero
  have hqpos : 0 < ‖q rho‖ := norm_pos_iff.mpr hqzero
  have hqfloor : ∀ᶠ z : ℂ in 𝓝 rho, ‖q rho‖ / 2 < ‖q z‖ :=
    hqcont.norm.eventually_const_lt (by linarith)
  have hpne : ∀ᶠ z : ℂ in 𝓝 rho, p z ≠ 0 :=
    hp.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hpzero)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 rho,
      riemannZeta z = (z - rho) ^ n * p z ∧ p z ≠ 0 ∧
        ‖q rho‖ / 2 ≤ ‖q z‖ := by
    filter_upwards [hfactor, hpne, hqfloor] with z hz hpz hqz
    exact ⟨by simpa [smul_eq_mul] using hz, hpz, hqz.le⟩
  obtain ⟨eps, heps, hepsLocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let delta : ℝ := min (eps / 2) (min ((1 - sigma) / 2) (1 / 2))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  refine ⟨‖q rho‖ / 4, by positivity, delta, hdelta, ?_⟩
  intro r hr hrdelta t ht
  let z : ℂ := ((sigma + r : ℝ) : ℂ) + (t : ℂ) * I
  have hzre : z.re = sigma + r := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hrEps : 2 * r < eps := by
    have hle : delta ≤ eps / 2 := min_le_left _ _
    nlinarith
  have hrOneSub : r < (1 - sigma) / 2 := by
    have hle : delta ≤ (1 - sigma) / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact hrdelta.trans_le hle
  have hrHalf : r < 1 / 2 := by
    have hle : delta ≤ 1 / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    exact hrdelta.trans_le hle
  have hnorm : ‖z - rho‖ ≤ 2 * r := by
    calc
      ‖z - rho‖ ≤ |(z - rho).re| + |(z - rho).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = r + |t - rho.im| := by simp [hzre, hzim, hrho, abs_of_pos hr]
      _ ≤ 2 * r := by linarith
  have hzdist : dist z rho < eps := by
    rw [Complex.dist_eq]
    exact hnorm.trans_lt hrEps
  obtain ⟨hfactorz, hpnez, hqfloorz⟩ := hepsLocal hzdist
  have hzright : sigma < z.re := by rw [hzre]; linarith
  have hzone : z ≠ 1 := by
    intro hz1
    have hre := congrArg Complex.re hz1
    rw [hzre] at hre
    simp only [one_re] at hre
    nlinarith
  have hcanonical := hidentity z hzright
  simp only [zetaResidueUnit, Function.update_of_ne hzone] at hcanonical
  have hcancel : G z * riemannZeta z = Complex.Gamma z := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hzone)
    calc
      (G z * riemannZeta z) * (z - 1) =
          G z * ((z - 1) * riemannZeta z) := by ring
      _ = Complex.Gamma z * (z - 1) := hcanonical
  have hscaled : G z * (z - rho) ^ n = q z := by
    apply (eq_div_iff hpnez).2
    calc
      (G z * (z - rho) ^ n) * p z =
          G z * ((z - rho) ^ n * p z) := by ring
      _ = G z * riemannZeta z := by rw [hfactorz]
      _ = Complex.Gamma z := hcancel
  have hnormPow : ‖z - rho‖ ^ n ≤ 2 * r := by
    have hnormOne : ‖z - rho‖ ≤ 1 := by nlinarith
    have honePow : ‖z - rho‖ ^ (n - 1) ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) hnormOne (n - 1)
    have hnSplit : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnzero)
    have hpowSelf : ‖z - rho‖ ^ n ≤ ‖z - rho‖ := by
      rw [← hnSplit, pow_add, pow_one]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right honePow (norm_nonneg _)
    exact hpowSelf.trans hnorm
  have hprod : ‖q rho‖ / 2 ≤ ‖G z‖ * (2 * r) := by
    calc
      ‖q rho‖ / 2 ≤ ‖q z‖ := hqfloorz
      _ = ‖G z‖ * ‖z - rho‖ ^ n := by
        rw [← hscaled, norm_mul, norm_pow]
      _ ≤ ‖G z‖ * (2 * r) :=
        mul_le_mul_of_nonneg_left hnormPow (norm_nonneg _)
  change ‖q rho‖ / 4 / r ≤ ‖G z‖
  apply (div_le_iff₀ hr).2
  nlinarith

/-- A finite base-line energy uniformly controls the source energies on every bounded interval of
right shifts staying left of `Re s = 1`.  This is the uniform-norm input needed to rule out a pole
approaching the base line. -/
theorem exists_uniform_integral_norm_sq_mobiusLaplaceLogMellinLineSource_of_base
    {sigma r₀ : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    (_hr₀ : 0 < r₀) (ha₀ : sigma + r₀ < 1) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2) ≤ C := by
  let major : ℝ → ℝ := fun u =>
    (Ioi 0).indicator
        (fun v : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma v‖ ^ 2) u +
      (Iic 0).indicator
        (fun v : ℝ => Real.exp ((2 * (1 - (sigma + r₀))) * v)) u
  have hbaseSq : Integrable
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hbase.1).mp hbase
  have hposMajor : Integrable
      ((Ioi 0).indicator
        (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2)) :=
    hbaseSq.integrableOn.integrable_indicator measurableSet_Ioi
  have hnegMajor : Integrable
      ((Iic 0).indicator
        (fun u : ℝ => Real.exp ((2 * (1 - (sigma + r₀))) * u))) :=
    (integrableOn_exp_mul_Iic (by linarith) 0).integrable_indicator measurableSet_Iic
  have hmajor : Integrable major := by
    simpa only [major] using! hposMajor.add hnegMajor
  refine ⟨∫ u : ℝ, major u, ?_⟩
  intro r hr hrr
  have har : sigma + r < 1 :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrr sigma) ha₀
  have htargetMem :=
    mobiusLaplaceLogMellinLineSource_memLp_two_of_base hbase hr
  have htarget : Integrable
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm htargetMem.1).mp htargetMem
  apply integral_mono_ae htarget hmajor
  filter_upwards [] with u
  by_cases hu : 0 < u
  · rw [mobiusLaplaceLogMellinLineSource_add, norm_smul,
      Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow]
    have hexp : Real.exp (-r * u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hexpSq : Real.exp (-r * u) ^ 2 ≤ 1 := by
      nlinarith [Real.exp_nonneg (-r * u)]
    have hle :
        Real.exp (-r * u) ^ 2 *
            ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 ≤
          ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hexpSq
          (sq_nonneg ‖mobiusLaplaceLogMellinLineSource sigma u‖)
    simpa [major, hu, not_le.mpr hu] using hle
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    have htail := norm_mobiusLaplaceLogMellinLineSource_le_exp_of_nonpos
      (a := sigma + r) hu0
    have hsq :
        ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2 ≤
          Real.exp ((1 - (sigma + r)) * u) ^ 2 := by
      nlinarith [norm_nonneg (mobiusLaplaceLogMellinLineSource (sigma + r) u),
        Real.exp_nonneg ((1 - (sigma + r)) * u)]
    have hshift : 0 ≤ r₀ - r := sub_nonneg.mpr hrr
    have hmul : (r₀ - r) * u ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hshift hu0
    have hexpOrder :
        Real.exp ((2 * (1 - (sigma + r))) * u) ≤
          Real.exp ((2 * (1 - (sigma + r₀))) * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hle :
        ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2 ≤
          Real.exp ((2 * (1 - (sigma + r₀))) * u) := by
      calc
        ‖mobiusLaplaceLogMellinLineSource (sigma + r) u‖ ^ 2 ≤
            Real.exp ((1 - (sigma + r)) * u) ^ 2 := hsq
        _ = Real.exp ((2 * (1 - (sigma + r))) * u) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring_nf
        _ ≤ Real.exp ((2 * (1 - (sigma + r₀))) * u) := hexpOrder
    simpa [major, hu, hu0] using hle

/-- Pointwise Möbius--Laplace Mellin trace as a Fourier transform. -/
theorem mellin_mobiusDiscreteLaplaceTransform_line_eq_fourier
    (sigma y : ℝ) :
    mellin mobiusDiscreteLaplaceTransform ((sigma : ℂ) + (y : ℂ) * I) =
      𝓕 (mobiusLaplaceLogMellinLineSource sigma) (y / (2 * Real.pi)) := by
  exact mellin_line_eq_fourier_logMellinLineSource
    mobiusDiscreteLaplaceTransform sigma y

/-- Infinite-aperture Gamma--Hankel line identity for the concrete Möbius source, conditional only
on the explicitly exposed `L¹ ∩ L²` logarithmic-source premises. -/
theorem integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq
    {sigma : ℝ}
    (h1 : Integrable (mobiusLaplaceLogMellinLineSource sigma))
    (h2 : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume) :
    (∫ y : ℝ,
      ‖mellin mobiusDiscreteLaplaceTransform
        ((sigma : ℂ) + (y : ℂ) * I)‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ,
        ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 := by
  exact integral_norm_sq_mellin_line_eq_logMellinLineSource h1 h2

/-- Finite logarithmic source energy on a base line gives a uniform classical Mellin-line energy
bound on every bounded family of right shifts before `Re s = 1`.  Together with a local pole lower
bound, this is the contradiction mechanism at a zero lying on the base line. -/
theorem exists_uniform_integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_of_base
    {sigma r₀ : ℝ}
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    (hr₀ : 0 < r₀) (ha₀ : sigma + r₀ < 1) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ y : ℝ,
        ‖mellin mobiusDiscreteLaplaceTransform
          (((sigma + r : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_integral_norm_sq_mobiusLaplaceLogMellinLineSource_of_base
      hbase hr₀ ha₀
  refine ⟨2 * Real.pi * C, ?_⟩
  intro r hr hrr
  have har : sigma + r < 1 :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrr sigma) ha₀
  have h2 := mobiusLaplaceLogMellinLineSource_memLp_two_of_base hbase hr
  have h1 := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase hr
  rw [integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq h1 h2]
  exact mul_le_mul_of_nonneg_left (hC r hr hrr)
    (mul_nonneg (by norm_num) Real.pi_nonneg)

/-- **Closed-half-plane energy criterion.**  Finite logarithmic Möbius--Laplace `L²` energy at
`sigma ∈ (0,1)` excludes every genuine zeta zero on or to the right of that line.  Strict-right
zeros are excluded by holomorphic continuation; a boundary zero would force `c/r` on a window of
width `2r`, hence line energy growing like `1/r`, contradicting the uniform Plancherel bound. -/
theorem riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hbase : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume)
    {rho : ℂ} (hrho : sigma ≤ rho.re) (hrhoOne : rho ≠ 1) :
    riemannZeta rho ≠ 0 := by
  rcases hrho.eq_or_lt with hrhoEq | hrhoLt
  · intro hzero
    have hrhoLine : rho.re = sigma := hrhoEq.symm
    have hcanonical : ∀ z : ℂ, sigma < z.re →
        mellin mobiusDiscreteLaplaceTransform z * zetaResidueUnit z =
          Complex.Gamma z * (z - 1) := by
      intro z hz
      exact mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
        hsigma hbase z hz
    obtain ⟨c, hc, delta, hdelta, hfloor⟩ :=
      exists_boundary_zero_vertical_window_floor_of_canonical_identity
        hsigma hsigmaOne hrhoLine hzero hcanonical
    let r₀ : ℝ := (1 - sigma) / 2
    have hr₀ : 0 < r₀ := by dsimp only [r₀]; linarith
    have ha₀ : sigma + r₀ < 1 := by dsimp only [r₀]; linarith
    obtain ⟨C, hC⟩ :=
      exists_uniform_integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_of_base
        hbase hr₀ ha₀
    let B : ℝ := |C| + 1
    have hB : 0 < B := by dsimp only [B]; positivity
    let r : ℝ := min (delta / 2) (min (r₀ / 2) (c ^ 2 / B))
    have hr : 0 < r := by
      dsimp only [r]
      positivity
    have hrdelta : r < delta := by
      have hle : r ≤ delta / 2 := min_le_left _ _
      linarith
    have hrr₀ : r ≤ r₀ := by
      have hle : r ≤ r₀ / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hrBudget : r ≤ c ^ 2 / B :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hBdiv : B ≤ c ^ 2 / r := by
      apply (le_div_iff₀ hr).2
      simpa [mul_comm] using (le_div_iff₀ hB).mp hrBudget
    have hClt : C < 2 * c ^ 2 / r := by
      have hCB : C < B := lt_of_le_of_lt (le_abs_self C) (lt_add_one |C|)
      have hcdiv : 0 < c ^ 2 / r := div_pos (sq_pos_of_pos hc) hr
      calc
        C < B := hCB
        _ ≤ c ^ 2 / r := hBdiv
        _ < 2 * c ^ 2 / r := by
          rw [show 2 * c ^ 2 / r = 2 * (c ^ 2 / r) by ring]
          nlinarith
    have h2 := mobiusLaplaceLogMellinLineSource_memLp_two_of_base hbase hr
    have h1 := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase hr
    have hlineInt : Integrable (fun t : ℝ =>
        ‖mellin mobiusDiscreteLaplaceTransform
          (((sigma + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
      integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
    have hlower := integral_norm_sq_ge_two_mul_sq_div_of_window_floor
      hr hc.le hlineInt (hfloor r hr hrdelta)
    have hupper := hC r hr hrr₀
    exact (not_lt_of_ge (hlower.trans hupper)) hClt
  · exact riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource
      hsigma hbase hrhoLt hrhoOne

/-- Open source frontier isolated by the Mellin--Plancherel argument: every logarithmic
Möbius--Laplace line strictly right of `1/2` has finite squared energy. -/
def MobiusLaplaceStrictRightEnergyFinite : Prop :=
  ∀ sigma : ℝ, 1 / 2 < sigma →
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume

/-- Sparse source frontier: finite logarithmic energy is available on abscissas cofinal from the
right at `1/2`.  No uniform energy bound and no energy at every abscissa is included in the
definition. -/
def MobiusLaplaceCofinalStrictRightEnergyFinite : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ sigma : ℝ,
    1 / 2 < sigma ∧ sigma < 1 / 2 + ε ∧
      MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume

/-- All strict-right energies trivially contain a cofinal family of finite-energy lines. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_of_strictRightEnergyFinite
    (henergy : MobiusLaplaceStrictRightEnergyFinite) :
    MobiusLaplaceCofinalStrictRightEnergyFinite := by
  intro ε hε
  let sigma : ℝ := 1 / 2 + ε / 2
  have hsigmaHalf : (1 / 2 : ℝ) < sigma := by
    dsimp only [sigma]
    linarith
  have hsigmaUpper : sigma < 1 / 2 + ε := by
    dsimp only [sigma]
    linarith
  exact ⟨sigma, hsigmaHalf, hsigmaUpper, henergy sigma hsigmaHalf⟩

/-- A cofinal family already supplies every strict-right energy: choose one finite-energy base
line below the target and use the contractive right-shift law. -/
theorem mobiusLaplaceStrictRightEnergyFinite_of_cofinalStrictRightEnergyFinite
    (henergy : MobiusLaplaceCofinalStrictRightEnergyFinite) :
    MobiusLaplaceStrictRightEnergyFinite := by
  intro sigma hsigma
  obtain ⟨base, _hbaseHalf, hbaseUpper, hbase⟩ :=
    henergy (sigma - 1 / 2) (by linarith)
  have hbaseSigma : base < sigma := by linarith
  have hshift : 0 < sigma - base := sub_pos.mpr hbaseSigma
  convert mobiusLaplaceLogMellinLineSource_memLp_two_of_base
    (sigma := base) (r := sigma - base) hbase hshift using 1 ;
    ring_nf

/-- **Cofinal energy compression law.**  Sparse finite-energy control arbitrarily close to the
critical abscissa is exactly as strong as finite energy on every strict-right line. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_iff_strictRightEnergyFinite :
    MobiusLaplaceCofinalStrictRightEnergyFinite ↔
      MobiusLaplaceStrictRightEnergyFinite := by
  constructor
  · exact mobiusLaplaceStrictRightEnergyFinite_of_cofinalStrictRightEnergyFinite
  · exact mobiusLaplaceCofinalStrictRightEnergyFinite_of_strictRightEnergyFinite

/-- The first `N` positive-index terms of the concrete Möbius--Laplace series. -/
def mobiusDiscreteLaplaceFiniteSection (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, mobiusDiscreteLaplaceTerm x (n + 1)

/-- The complex finite section is exactly the real finite Gamma--Hankel Möbius pencil. -/
theorem mobiusDiscreteLaplaceFiniteSection_eq_finiteMobiusLaplacePencil
    (N : ℕ) (x : ℝ) :
    mobiusDiscreteLaplaceFiniteSection N x =
      (finiteMobiusLaplacePencil N x : ℂ) := by
  rw [mobiusDiscreteLaplaceFiniteSection, finiteMobiusLaplacePencil,
    finiteRealLaplacePencil]
  push_cast
  apply Finset.sum_congr rfl
  intro n _hn
  rw [mobiusDiscreteLaplaceTerm, shiftedMobiusRealCoefficient]
  congr 2
  push_cast
  ring

/-- Every finite Möbius--Laplace section is continuous. -/
theorem continuous_mobiusDiscreteLaplaceFiniteSection (N : ℕ) :
    Continuous (mobiusDiscreteLaplaceFiniteSection N) := by
  unfold mobiusDiscreteLaplaceFiniteSection mobiusDiscreteLaplaceTerm
  fun_prop

/-- At every positive scale, finite Möbius--Laplace sections converge to the concrete infinite
transform. -/
theorem tendsto_mobiusDiscreteLaplaceFiniteSection_atTop
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => mobiusDiscreteLaplaceFiniteSection N x) atTop
      (nhds (mobiusDiscreteLaplaceTransform x)) := by
  have hsum := summable_mobiusDiscreteLaplaceTerm hx
  have hshiftSum : Summable (fun n : ℕ => mobiusDiscreteLaplaceTerm x (n + 1)) :=
    hsum.comp_injective Nat.succ_injective
  have hshift : mobiusDiscreteLaplaceTransform x =
      ∑' n : ℕ, mobiusDiscreteLaplaceTerm x (n + 1) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    rw [mobiusDiscreteLaplaceTransform]
    simpa [mobiusDiscreteLaplaceTerm] using hsplit.symm
  rw [hshift]
  simpa only [mobiusDiscreteLaplaceFiniteSection] using
    hshiftSum.hasSum.tendsto_sum_nat

/-- Logarithmic Mellin-line source of one finite Möbius--Laplace section. -/
def mobiusLaplaceFiniteSectionLogMellinLineSource
    (N : ℕ) (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) •
    mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u))

theorem continuous_mobiusLaplaceFiniteSectionLogMellinLineSource
    (N : ℕ) (sigma : ℝ) :
    Continuous (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) := by
  unfold mobiusLaplaceFiniteSectionLogMellinLineSource
  have hscalar : Continuous (fun u : ℝ => Real.exp (-sigma * u)) := by fun_prop
  have hsection : Continuous (fun u : ℝ =>
      mobiusDiscreteLaplaceFiniteSection N (Real.exp (-u))) :=
    (continuous_mobiusDiscreteLaplaceFiniteSection N).comp (by fun_prop)
  exact hscalar.smul hsection

/-- Finite logarithmic sources converge pointwise to the actual logarithmic source. -/
theorem tendsto_mobiusLaplaceFiniteSectionLogMellinLineSource_atTop
    (sigma u : ℝ) :
    Tendsto (fun N : ℕ =>
      mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u) atTop
      (nhds (mobiusLaplaceLogMellinLineSource sigma u)) := by
  unfold mobiusLaplaceFiniteSectionLogMellinLineSource
    mobiusLaplaceLogMellinLineSource logMellinLineSource
  exact tendsto_const_nhds.smul
    (tendsto_mobiusDiscreteLaplaceFiniteSection_atTop (Real.exp_pos (-u)))

private theorem norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource_eq
    (N : ℕ) (sigma u : ℝ) :
    ‖mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u‖ ^ 2 =
      Real.exp (-(2 * sigma) * u) *
        finiteMobiusLaplacePencil N (Real.exp (-u)) ^ 2 := by
  rw [mobiusLaplaceFiniteSectionLogMellinLineSource,
    mobiusDiscreteLaplaceFiniteSection_eq_finiteMobiusLaplacePencil]
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _), Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, ← Real.exp_nat_mul]
  congr 1
  ring_nf

/-- Exact identification of finite logarithmic `L²` energy with the concrete Möbius
Gamma--Hankel quadratic form. -/
theorem integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource
    (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ u : ℝ,
      ‖mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u‖ ^ 2) =
      finiteMobiusGammaHankelEnergy N (2 * sigma) := by
  rw [← integral_log_finiteMobiusLaplacePencil_sq N
    (by linarith : 0 < 2 * sigma)]
  apply integral_congr_ae
  filter_upwards [] with u
  exact norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource_eq N sigma u

/-- Every finite logarithmic Möbius section is in `L²` on every positive Mellin line. -/
theorem mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two
    (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    MemLp (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_mobiusLaplaceFiniteSectionLogMellinLineSource N sigma).aestronglyMeasurable]
  apply (integrable_log_finiteMobiusLaplacePencil_sq N
    (by linarith : 0 < 2 * sigma)).congr
  filter_upwards with u
  exact (norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource_eq N sigma u).symm

/-- Finite, source-pure approximation frontier.  Arbitrarily close to `1/2`, the logarithmic
finite Gamma--Hankel sections have one common finite `L²` ceiling.  The ceiling may depend on the
chosen abscissa. -/
def MobiusLaplaceCofinalFiniteSectionEnergyBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ sigma : ℝ, ∃ C : ℝ≥0∞,
    1 / 2 < sigma ∧ sigma < 1 / 2 + ε ∧ C ≠ ∞ ∧
      ∀ N : ℕ,
        eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) 2 volume ≤ C

/-- Exact signed arithmetic frontier.  On Gamma exponents cofinal from the right at `1`, only a
one-sided upper ceiling on off-diagonal Möbius covariance is requested.  Diagonal mass and the
opposite sign are already unconditional. -/
def MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ sigma : ℝ,
    1 / 2 < sigma ∧ sigma < 1 / 2 + ε ∧
      MobiusGammaHankelOffDiagonalUpperBounded (2 * sigma)

/-- A cofinal one-sided off-diagonal covariance ceiling supplies uniform finite-section `L²`
ceilings through the exact log-coordinate Gamma--Hankel identity. -/
theorem mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_gammaHankelOffDiagonal
    (hoff : MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded) :
    MobiusLaplaceCofinalFiniteSectionEnergyBounded := by
  intro ε hε
  obtain ⟨sigma, hsigmaHalf, hsigmaUpper, hsigmaOff⟩ := hoff ε hε
  have hsigma : 0 < sigma := by linarith
  have hr : 1 < 2 * sigma := by linarith
  obtain ⟨C, hC⟩ :=
    (mobiusGammaHankelEnergyUniformlyBounded_iff_offDiagonalUpperBounded hr).2
      hsigmaOff
  have hC0 : 0 ≤ C := by
    linarith [finiteMobiusGammaHankelEnergy_nonneg 0
      (by linarith : 0 < 2 * sigma), hC 0]
  let C₂ : ℝ≥0∞ := ENNReal.ofReal (C ^ (2 : ℝ)⁻¹)
  refine ⟨sigma, C₂, hsigmaHalf, hsigmaUpper, ENNReal.ofReal_ne_top, ?_⟩
  intro N
  have hmem := mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two N hsigma
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, C₂]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow
  · exact integral_nonneg fun _ => sq_nonneg _
  · rw [integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource N hsigma]
    exact hC N
  · positivity

/-- The exact finite-section `L²` identity also recovers the signed arithmetic ceiling.
Consequently the analytic finite-section interface does not retain any information beyond the
Gamma--Hankel quadratic forms. -/
theorem mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_of_finiteSectionEnergy
    (hfinite : MobiusLaplaceCofinalFiniteSectionEnergyBounded) :
    MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded := by
  intro ε hε
  obtain ⟨sigma, C, hsigmaHalf, hsigmaUpper, hCtop, hbound⟩ := hfinite ε hε
  have hsigma : 0 < sigma := by linarith
  have hr : 1 < 2 * sigma := by linarith
  refine ⟨sigma, hsigmaHalf, hsigmaUpper, ?_⟩
  apply (mobiusGammaHankelEnergyUniformlyBounded_iff_offDiagonalUpperBounded hr).1
  refine ⟨C.toReal ^ 2, fun N => ?_⟩
  let E : ℝ :=
    ∫ u : ℝ, ‖mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u‖ ^ 2
  have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hmem :=
    mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two N hsigma
  have hN := hbound N
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top] at hN
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hN
  have hroot : E ^ (2 : ℝ)⁻¹ ≤ C.toReal := by
    have hreal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hCtop).2 hN
    simpa [E, ENNReal.toReal_ofReal (Real.rpow_nonneg hE0 _)] using hreal
  calc
    finiteMobiusGammaHankelEnergy N (2 * sigma) = E := by
      exact
        (integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource N hsigma).symm
    _ = (E ^ (2 : ℝ)⁻¹) ^ 2 := by
      exact (Real.rpow_inv_natCast_pow hE0 (by norm_num : (2 : ℕ) ≠ 0)).symm
    _ ≤ C.toReal ^ 2 := by
      have hroot0 : 0 ≤ E ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg hE0 _
      have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
      nlinarith

/-- Cofinal finite logarithmic `L²` ceilings are exactly cofinal one-sided upper ceilings on
signed Möbius Gamma--Hankel covariance. -/
theorem
    mobiusLaplaceCofinalFiniteSectionEnergyBounded_iff_gammaHankelOffDiagonalUpperBounded :
    MobiusLaplaceCofinalFiniteSectionEnergyBounded ↔
      MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded :=
  ⟨mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_of_finiteSectionEnergy,
    mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_gammaHankelOffDiagonal⟩

/-- Weaker bounded-return frontier.  Instead of a ceiling at every aperture, it asks only that
off-diagonal covariance return below one finite ceiling at arbitrarily large apertures. -/
def MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ sigma C : ℝ,
    1 / 2 < sigma ∧ sigma < 1 / 2 + ε ∧
      ∃ᶠ N : ℕ in atTop,
        finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ C

/-- Aperture-uniform off-diagonal control contains the bounded-return frontier.  This explicit
connector lets every consumer of the Fatou-subsequence criterion reuse the stronger cofinal
Gamma--Hankel ceiling directly. -/
theorem
    mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_of_upperBounded
    (hoff : MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded) :
    MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded := by
  intro ε hε
  obtain ⟨sigma, hsigmaHalf, hsigmaUpper, C, hC⟩ := hoff ε hε
  exact ⟨sigma, C, hsigmaHalf, hsigmaUpper,
    (Filter.Eventually.of_forall hC).frequently⟩

/-- A bounded-return subsequence of one signed off-diagonal covariance line gives actual `L²`
energy on that line. -/
theorem mobiusLaplaceLogMellinLineSource_memLp_two_of_frequently_offDiagonalUpperBound
    {sigma C : ℝ} (hsigmaHalf : 1 / 2 < sigma)
    (hfreqOff : ∃ᶠ N : ℕ in atTop,
      finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ C) :
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume := by
  have hsigma : 0 < sigma := by linarith
  have hr : 1 < 2 * sigma := by linarith
  let D : ℝ := ∑' n : ℕ, mobiusGammaHankelDiagonalMajorant (2 * sigma) n
  have hfreqEnergy : ∃ᶠ N : ℕ in atTop,
      finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ D + C := by
    exact hfreqOff.mono fun N hN => by
      rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
      exact add_le_add (finiteMobiusGammaHankelDiagonalEnergy_le_tsum N hr) hN
  obtain ⟨φ, hφmono, hφenergy⟩ := extraction_of_frequently_atTop hfreqEnergy
  have hDC0 : 0 ≤ D + C := by
    linarith [finiteMobiusGammaHankelEnergy_nonneg (φ 0)
      (by linarith : 0 < 2 * sigma), hφenergy 0]
  let C₂ : ℝ≥0∞ := ENNReal.ofReal ((D + C) ^ (2 : ℝ)⁻¹)
  have hbound : ∀ n : ℕ,
      eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource (φ n) sigma) 2 volume ≤ C₂ := by
    intro n
    have hmem := mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two (φ n) hsigma
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, C₂]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow
    · exact integral_nonneg fun _ => sq_nonneg _
    · rw [integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource (φ n) hsigma]
      exact hφenergy n
    · positivity
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (mobiusLaplaceFiniteSectionLogMellinLineSource (φ n) sigma) volume :=
    fun n =>
      (continuous_mobiusLaplaceFiniteSectionLogMellinLineSource
        (φ n) sigma).aestronglyMeasurable
  have htend : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun n : ℕ =>
        mobiusLaplaceFiniteSectionLogMellinLineSource (φ n) sigma u) atTop
        (nhds (mobiusLaplaceLogMellinLineSource sigma u)) :=
    Filter.Eventually.of_forall fun u =>
      (tendsto_mobiusLaplaceFiniteSectionLogMellinLineSource_atTop sigma u).comp
        hφmono.tendsto_atTop
  have hnorm := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (p := (2 : ℝ≥0∞)) (Filter.Eventually.of_forall hbound) hmeas htend
  refine ⟨(continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable, ?_⟩
  exact hnorm.trans_lt ENNReal.ofReal_lt_top

/-- **Off-diagonal escape law.**  A genuine zeta zero on or to the right of a line
`sigma ∈ (1/2, 1)` forces the finite Gamma--Hankel off-diagonal covariance on that line to
escape to `+∞`.  Indeed, failure of escape would provide arbitrarily large bounded returns;
the finite-section Fatou argument would then give line `L²` energy, contradicting the
closed-half-plane energy criterion. -/
theorem tendsto_finiteMobiusGammaHankelOffDiagonalCovariance_atTop_of_riemannZeta_zero
    {sigma : ℝ} (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    {rho : ℂ} (hrho : sigma ≤ rho.re) (hrhoOne : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    Tendsto
      (fun N : ℕ => finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma))
      atTop atTop := by
  rw [tendsto_atTop]
  intro C
  by_contra hescape
  have hfreq : ∃ᶠ N : ℕ in atTop,
      finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ C :=
    (not_eventually.mp hescape).mono fun _ hN => le_of_not_ge hN
  have hmem :=
    mobiusLaplaceLogMellinLineSource_memLp_two_of_frequently_offDiagonalUpperBound
      hsigmaHalf hfreq
  exact (riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed
    (by linarith) hsigmaOne hmem hrho hrhoOne) hzero

/-- **Bounded-return Fatou compression.**  Uniform aperture control is unnecessary.  Infinitely
many bounded off-diagonal returns along an unbounded aperture subsequence already pass to the
infinite source and supply cofinal strict-right energy. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_of_gammaHankelOffDiagonalFrequently
    (hoff : MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded) :
    MobiusLaplaceCofinalStrictRightEnergyFinite := by
  intro ε hε
  obtain ⟨sigma, C, hsigmaHalf, hsigmaUpper, hfreqOff⟩ := hoff ε hε
  exact ⟨sigma, hsigmaHalf, hsigmaUpper,
    mobiusLaplaceLogMellinLineSource_memLp_two_of_frequently_offDiagonalUpperBound
      hsigmaHalf hfreqOff⟩

/-- **Finite-section Fatou bridge.**  A uniform ceiling for finite Gamma--Hankel sections passes
to the actual Möbius--Laplace source by pointwise convergence and lower semicontinuity of the
`L²` norm. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_of_finiteSectionEnergyBounded
    (hfinite : MobiusLaplaceCofinalFiniteSectionEnergyBounded) :
    MobiusLaplaceCofinalStrictRightEnergyFinite := by
  intro ε hε
  obtain ⟨sigma, C, hsigmaHalf, hsigmaUpper, hCtop, hC⟩ := hfinite ε hε
  refine ⟨sigma, hsigmaHalf, hsigmaUpper, ?_⟩
  have hbound : ∀ᶠ N : ℕ in atTop,
      eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) 2 volume ≤ C :=
    Filter.Eventually.of_forall hC
  have hmeas : ∀ N : ℕ,
      AEStronglyMeasurable
        (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) volume :=
    fun N =>
      (continuous_mobiusLaplaceFiniteSectionLogMellinLineSource N sigma).aestronglyMeasurable
  have htend : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun N : ℕ =>
        mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u) atTop
        (nhds (mobiusLaplaceLogMellinLineSource sigma u)) :=
    Filter.Eventually.of_forall
      (tendsto_mobiusLaplaceFiniteSectionLogMellinLineSource_atTop sigma)
  have hnorm := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (p := (2 : ℝ≥0∞)) hbound hmeas htend
  refine ⟨(continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable, ?_⟩
  exact hnorm.trans_lt hCtop.lt_top

/-- Every strict half-power pointwise estimate supplies every strict-right logarithmic `L²`
energy.  The energy criterion is therefore no stronger than the established pointwise source:
choose an exponent `b` strictly between `1/2` and `sigma`; after `x=exp(-u)`, the positive
logarithmic tail decays like `exp(-(sigma-b)u)`, while the negative tail is unconditionally
superexponential. -/
theorem mobiusLaplaceStrictRightEnergyFinite_of_allStrictHalfPowerDecay
    (hdecay : MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceStrictRightEnergyFinite := by
  intro sigma hsigma
  let b : ℝ := ((1 / 2 : ℝ) + sigma) / 2
  have hb : (1 / 2 : ℝ) < b := by dsimp only [b]; linarith
  have hbsigma : b < sigma := by dsimp only [b]; linarith
  obtain ⟨C, hCpos, hCO⟩ := (hdecay b hb).exists_pos
  have hCnonneg : 0 ≤ C := hCpos.le
  have hevent : ∀ᶠ x : ℝ in 𝓝[>] 0,
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * ‖x ^ (-b)‖ :=
    hCO.bound
  have hevent' : ∀ᶠ x : ℝ in 𝓝 0, x ∈ Ioi 0 →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * ‖x ^ (-b)‖ :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨delta, hdelta, hsmall'⟩ := Metric.eventually_nhds_iff.mp hevent'
  have hsmall : ∀ {x : ℝ}, 0 < x → x < delta →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ C * ‖x ^ (-b)‖ := by
    intro x hx hxdelta
    apply hsmall'
    · simpa [Real.dist_eq, abs_of_pos hx] using hxdelta
    · exact hx
  let U : ℝ := max 0 (-Real.log delta)
  have hU : 0 ≤ U := le_max_left _ _
  have hxsmall : ∀ u : ℝ, U < u →
      ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖ ≤
        C * Real.exp (b * u) := by
    intro u hu
    have hdeltaExp : Real.exp (-u) < delta := by
      have hlog : -Real.log delta < u := lt_of_le_of_lt (le_max_right _ _) hu
      have hexp := Real.exp_lt_exp.mpr (by linarith : -u < Real.log delta)
      simpa [Real.exp_log hdelta] using hexp
    have hraw := hsmall (Real.exp_pos (-u)) hdeltaExp
    calc
      ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖ ≤
          C * ‖Real.exp (-u) ^ (-b)‖ := hraw
      _ = C * Real.exp (b * u) := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.exp_pos (-u)).le _),
          ← Real.exp_mul]
        congr 2
        ring_nf
  have htail : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) (Ioi U) := by
    let K : ℝ := C ^ 2
    have hmajor : IntegrableOn
        (fun u : ℝ => K * Real.exp ((-2 * (sigma - b)) * u)) (Ioi U) :=
      (integrableOn_exp_mul_Ioi (by linarith) U).const_mul K
    refine hmajor.mono'
      ((continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable.norm.pow 2
        |>.mono_measure Measure.restrict_le_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    unfold mobiusLaplaceLogMellinLineSource logMellinLineSource
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hphi := hxsmall u hu
    have hleft : 0 ≤ Real.exp (-sigma * u) *
        ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖ :=
      mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
    have hright : 0 ≤ Real.exp (-sigma * u) * (C * Real.exp (b * u)) :=
      mul_nonneg (Real.exp_nonneg _) (mul_nonneg hCnonneg (Real.exp_nonneg _))
    have hsquare :
        (Real.exp (-sigma * u) *
            ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖) ^ 2 ≤
          (Real.exp (-sigma * u) * (C * Real.exp (b * u))) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hphi (Real.exp_nonneg (-sigma * u))]
    calc
      (Real.exp (-sigma * u) *
          ‖mobiusDiscreteLaplaceTransform (Real.exp (-u))‖) ^ 2 ≤
          (Real.exp (-sigma * u) * (C * Real.exp (b * u))) ^ 2 := hsquare
      _ = K * Real.exp ((-2 * (sigma - b)) * u) := by
        dsimp only [K]
        have hexp : Real.exp (-sigma * u) * Real.exp (b * u) =
            Real.exp ((b - sigma) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
        rw [show Real.exp (-sigma * u) * (C * Real.exp (b * u)) =
            C * (Real.exp (-sigma * u) * Real.exp (b * u)) by ring,
          hexp, mul_pow, ← Real.exp_nat_mul]
        congr 1
        ring_nf
  have hcompact : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) (Ioc 0 U) := by
    exact ((continuous_mobiusLaplaceLogMellinLineSource sigma).norm.pow 2).integrableOn_Icc
      |>.mono_set Ioc_subset_Icc_self
  have hpos : IntegrableOn
      (fun u : ℝ => ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) (Ioi 0) := by
    have hunion := hcompact.union htail
    apply hunion.mono_set
    intro u hu
    by_cases huU : u ≤ U
    · exact Or.inl ⟨hu, huU⟩
    · exact Or.inr (lt_of_not_ge huU)
  have hneg := integrableOn_norm_sq_mobiusLaplaceLogMellinLineSource_Iic sigma
  have hmeas : AEStronglyMeasurable
      (mobiusLaplaceLogMellinLineSource sigma) volume :=
    (continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- Finite energy on every strict-right line produces the canonical Mellin continuation wall. -/
theorem mobiusLaplaceMellinContinuationWall_of_strictRightEnergyFinite
    (henergy : MobiusLaplaceStrictRightEnergyFinite) :
    MobiusLaplaceMellinContinuationWall := by
  apply mobiusLaplaceMellinContinuationWall_of_analyticOnNhd_mellin
  intro s hs
  let sigma : ℝ := ((1 / 2 : ℝ) + s.re) / 2
  have hsHalf : (1 / 2 : ℝ) < s.re := mem_rightHalf.mp hs
  have hsigmaHalf : (1 / 2 : ℝ) < sigma := by
    dsimp only [sigma]
    linarith
  have hsigmaS : sigma < s.re := by
    dsimp only [sigma]
    linarith
  exact analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_base
    (henergy sigma hsigmaHalf) s hsigmaS

/-- **Möbius--Laplace energy criterion for RH.**  The only remaining source obligation is finite
logarithmic energy on every line `Re s = sigma > 1/2`; all continuation and zero-exclusion steps
are unconditional theorems. -/
theorem mobiusLaplaceStrictRightEnergyFinite_implies_riemannHypothesis
    (henergy : MobiusLaplaceStrictRightEnergyFinite) : RiemannHypothesis :=
  mobiusLaplaceMellinContinuationWall_implies_riemannHypothesis
    (mobiusLaplaceMellinContinuationWall_of_strictRightEnergyFinite henergy)

/-- **Sparse Möbius--Laplace energy criterion for RH.**  It is enough to prove finite energy on
some strict-right line in every neighborhood of `1/2`; right-shift propagation fills the whole
half-plane before the Mellin continuation argument is applied. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
    (henergy : MobiusLaplaceCofinalStrictRightEnergyFinite) : RiemannHypothesis :=
  mobiusLaplaceStrictRightEnergyFinite_implies_riemannHypothesis
    (mobiusLaplaceStrictRightEnergyFinite_of_cofinalStrictRightEnergyFinite henergy)

/-- **Finite Gamma--Hankel section criterion for RH.**  Uniform `L²` ceilings for the concrete
finite Möbius sections on a cofinal family of strict-right lines pass to the infinite source by
Fatou and therefore force RH. -/
theorem mobiusLaplaceCofinalFiniteSectionEnergyBounded_implies_riemannHypothesis
    (hfinite : MobiusLaplaceCofinalFiniteSectionEnergyBounded) : RiemannHypothesis :=
  mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
    (mobiusLaplaceCofinalStrictRightEnergyFinite_of_finiteSectionEnergyBounded hfinite)

/-- **One-sided off-diagonal Möbius covariance criterion for RH.**  On Gamma exponents
arbitrarily close to `1` from the right, aperture-uniform upper control of signed off-diagonal
covariance alone forces RH.  Diagonal convergence and the lower covariance floor are theorems. -/
theorem mobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded_implies_riemannHypothesis
    (hoff : MobiusLaplaceCofinalGammaHankelOffDiagonalUpperBounded) :
    RiemannHypothesis :=
  mobiusLaplaceCofinalFiniteSectionEnergyBounded_implies_riemannHypothesis
    (mobiusLaplaceCofinalFiniteSectionEnergyBounded_of_gammaHankelOffDiagonal hoff)

/-- **Bounded-return one-sided covariance criterion for RH.**  It suffices that the signed
off-diagonal covariance have bounded returns at arbitrarily large apertures on cofinal Gamma
exponents.  An off-critical zero would therefore force positive covariance escape to `+∞`. -/
theorem
    mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_implies_riemannHypothesis
    (hoff : MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded) :
    RiemannHypothesis :=
  mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
    (mobiusLaplaceCofinalStrictRightEnergyFinite_of_gammaHankelOffDiagonalFrequently hoff)

/-- Exact energy/RH equivalence interface once the classical converse source
`RH → every strict half-power decay` is supplied. -/
theorem mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
    (hLittlewood : RiemannHypothesis → MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceStrictRightEnergyFinite ↔ RiemannHypothesis := by
  constructor
  · exact mobiusLaplaceStrictRightEnergyFinite_implies_riemannHypothesis
  · intro hRH
    exact mobiusLaplaceStrictRightEnergyFinite_of_allStrictHalfPowerDecay
      (hLittlewood hRH)

/-- Conditional exact equivalence for the cofinal compression, after supplying the classical
Littlewood converse. -/
theorem mobiusLaplaceCofinalStrictRightEnergyFinite_iff_riemannHypothesis_of_decay
    (hLittlewood : RiemannHypothesis → MobiusDiscreteLaplaceAllStrictHalfPowerDecay) :
    MobiusLaplaceCofinalStrictRightEnergyFinite ↔ RiemannHypothesis := by
  rw [mobiusLaplaceCofinalStrictRightEnergyFinite_iff_strictRightEnergyFinite]
  exact mobiusLaplaceStrictRightEnergyFinite_iff_riemannHypothesis_of_decay hLittlewood

end RHTower
