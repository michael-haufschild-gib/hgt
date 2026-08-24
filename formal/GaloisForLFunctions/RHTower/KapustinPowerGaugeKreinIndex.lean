import GaloisForLFunctions.RHTower.GammaVerticalPolar
import GaloisForLFunctions.HTGeometry.PhaseSignChain
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower
import GaloisForLFunctions.HTGeometry.EvenWeightedSignCarrier
import GaloisForLFunctions.HTGeometry.FullSectorPolarizationLaw
import GaloisForLFunctions.RHTower.FullSectorPolarizationEssentialNorm
import GaloisForLFunctions.RHTower.SuzukiRemainderFourierTransform
import GaloisForLFunctions.HTGeometry.DigammaSecondOrderVertical

open Complex Filter Topology intervalIntegral
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace RHTower

def kapustinPowerGaugePhase (β t : ℝ) : ℝ :=
  t * Real.log (2 * Real.pi) - gammaVerticalPhase (1 / 2) t -
    β * Real.arctan (2 * t)

theorem hasDerivAt_kapustinPowerGaugePhase (β t : ℝ) :
    HasDerivAt (kapustinPowerGaugePhase β)
      (Real.log (2 * Real.pi) -
        (Complex.digamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re -
        β * (2 / (1 + (2 * t) ^ 2))) t := by
  change HasDerivAt (fun u : ℝ =>
    u * Real.log (2 * Real.pi) - gammaVerticalPhase (1 / 2) u -
      β * Real.arctan (2 * u)) _ t
  have hlinear : HasDerivAt (fun u : ℝ => u * Real.log (2 * Real.pi))
      (Real.log (2 * Real.pi)) t := by
    simpa using (hasDerivAt_id t).mul_const (Real.log (2 * Real.pi))
  have hargLinear : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
    simpa using HasDerivAt.const_mul 2 (hasDerivAt_id t)
  have harg : HasDerivAt (fun u : ℝ => Real.arctan (2 * u))
      (2 / (1 + (2 * t) ^ 2)) t := by
    change HasDerivAt (Real.arctan ∘ fun u : ℝ => 2 * u)
      (2 / (1 + (2 * t) ^ 2)) t
    exact ((Real.hasDerivAt_arctan (2 * t)).comp t hargLinear).congr_deriv (by
      rw [div_eq_mul_inv]
      ring)
  have h := (hlinear.sub (hasDerivAt_gammaVerticalPhase
    (by norm_num : (0 : ℝ) < 1 / 2) t)).sub (HasDerivAt.const_mul β harg)
  exact h

theorem abs_re_digamma_criticalLine_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |(Complex.digamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re - Real.log t| ≤
      8 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  have hzsq : ‖z‖ ^ 2 = t ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z]
    ring
  have hznorm0 : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
  have hnormge : t ≤ ‖z‖ := by
    have hsquare : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [hzsq]; norm_num
    nlinarith [norm_nonneg z]
  have hupper0 : 0 < t + 1 / (8 * t) := by positivity
  have hnormle : ‖z‖ ≤ t + 1 / (8 * t) := by
    have hsquare : ‖z‖ ^ 2 ≤ (t + 1 / (8 * t)) ^ 2 := by
      rw [hzsq]
      field_simp [ht0.ne']
      nlinarith

    nlinarith [norm_nonneg z]
  have hlognonneg : 0 ≤ Real.log ‖z‖ - Real.log t := by
    exact sub_nonneg.mpr (Real.log_le_log ht0 hnormge)
  have hratio0 : 0 < ‖z‖ / t := div_pos hznorm0 ht0
  have hratiole : ‖z‖ / t ≤ 1 + 1 / (8 * t ^ 2) := by
    rw [div_le_iff₀ ht0]
    calc
      ‖z‖ ≤ t + 1 / (8 * t) := hnormle
      _ = (1 + 1 / (8 * t ^ 2)) * t := by field_simp [ht0.ne']
  have hlogupper : Real.log ‖z‖ - Real.log t ≤ 1 / (8 * t ^ 2) := by
    rw [← Real.log_div hznorm0.ne' ht0.ne']
    exact le_trans (Real.log_le_sub_one_of_pos hratio0) (by linarith)
  have hlogabs : |Real.log ‖z‖ - Real.log t| ≤ 1 / (8 * t ^ 2) := by
    rw [abs_of_nonneg hlognonneg]
    exact hlogupper
  have hrem := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_add_half_inv_le
    (by norm_num : (0 : ℝ) < 1 / 2) ht
  change ‖Complex.digamma z - Complex.log z + 1 / (2 * z)‖ ≤ (20 / 3) / t ^ 2 at hrem
  have hreRem : |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re| ≤
      (20 / 3) / t ^ 2 := le_trans (Complex.abs_re_le_norm _) hrem
  have hinvre : (1 / (2 * z) : ℂ).re = 1 / (1 + 4 * t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp [z]
    ring
  have hinvnonneg : 0 ≤ (1 / (2 * z) : ℂ).re := by rw [hinvre]; positivity
  have hinvle : |(1 / (2 * z) : ℂ).re| ≤ 1 / (4 * t ^ 2) := by
    rw [abs_of_nonneg hinvnonneg, hinvre]
    gcongr
    nlinarith
  have hdecomp :
      (Complex.digamma z).re - Real.log t =
        (Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
          (Real.log ‖z‖ - Real.log t) - (1 / (2 * z) : ℂ).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.log_re]
    ring
  rw [show (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = z from rfl]
  rw [hdecomp]
  calc
    |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
          (Real.log ‖z‖ - Real.log t) - (1 / (2 * z) : ℂ).re|
        ≤ |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re| +
            |Real.log ‖z‖ - Real.log t| + |(1 / (2 * z) : ℂ).re| := by
          calc
            _ ≤ |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
                  (Real.log ‖z‖ - Real.log t)| + |(1 / (2 * z) : ℂ).re| :=
              abs_sub _ _
            _ ≤ (|(Complex.digamma z - Complex.log z + 1 / (2 * z)).re| +
                  |Real.log ‖z‖ - Real.log t|) + |(1 / (2 * z) : ℂ).re| :=
              add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (20 / 3) / t ^ 2 + 1 / (8 * t ^ 2) + 1 / (4 * t ^ 2) := by
      gcongr
    _ ≤ 8 / t ^ 2 := by
      field_simp [ht0.ne']
      nlinarith

/-- Equation (3): the exact phase derivative differs from `log(2π/t)` by `O(t⁻²)`. -/
theorem abs_kapustinPowerGaugePhase_deriv_sub_log_le
    {β t : ℝ} (hβ : 0 ≤ β) (ht : 2 ≤ t) :
    |deriv (kapustinPowerGaugePhase β) t - Real.log ((2 * Real.pi) / t)| ≤
      (8 + β / 2) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [(hasDerivAt_kapustinPowerGaugePhase β t).deriv,
    Real.log_div (mul_pos (by norm_num) Real.pi_pos).ne' ht0.ne']
  let d : ℝ := (Complex.digamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re
  have hd : |d - Real.log t| ≤ 8 / t ^ 2 := by
    simpa [d] using abs_re_digamma_criticalLine_sub_log_le ht
  have hfrac0 : 0 ≤ 2 / (1 + (2 * t) ^ 2) := by positivity
  have hfrac : 2 / (1 + (2 * t) ^ 2) ≤ 1 / (2 * t ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hterm : |β * (2 / (1 + (2 * t) ^ 2))| ≤ β / (2 * t ^ 2) := by
    rw [abs_of_nonneg (mul_nonneg hβ hfrac0)]
    rw [show β / (2 * t ^ 2) = β * (1 / (2 * t ^ 2)) by ring]
    exact mul_le_mul_of_nonneg_left hfrac hβ
  have hrewrite :
      Real.log (2 * Real.pi) - d - β * (2 / (1 + (2 * t) ^ 2)) -
          (Real.log (2 * Real.pi) - Real.log t) =
        -(d - Real.log t) - β * (2 / (1 + (2 * t) ^ 2)) := by ring
  rw [hrewrite]
  calc
    |-(d - Real.log t) - β * (2 / (1 + (2 * t) ^ 2))| ≤
        |d - Real.log t| + |β * (2 / (1 + (2 * t) ^ 2))| := by
      calc
        _ ≤ |-(d - Real.log t)| + |β * (2 / (1 + (2 * t) ^ 2))| := abs_sub _ _
        _ = _ := by rw [abs_neg]
    _ ≤ 8 / t ^ 2 + β / (2 * t ^ 2) := add_le_add hd hterm
    _ = (8 + β / 2) / t ^ 2 := by field_simp [ht0.ne']

def kapustinPowerGaugeAmplitude (β t : ℝ) : ℝ :=
  Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi) -
    β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖) /
      ‖gammaVerticalValue (1 / 2) t‖

def kapustinPowerGaugeQ (β t : ℝ) : ℂ :=
  (kapustinPowerGaugeAmplitude β t : ℂ) *
    Complex.exp (I * (kapustinPowerGaugePhase β t : ℂ))

def kapustinPowerGaugeWeight (β t : ℝ) : ℝ :=
  (kapustinPowerGaugeQ β t).re

def kapustinPowerGaugeFormula (β t : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^
      (((-3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) /
    (Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ (β : ℂ))

private theorem kapustinCriticalPoint_ne_zero (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem kapustinCriticalPoint_arg (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).arg = Real.arctan (2 * t) := by
  have h := GaloisForLFunctions.HTGeometry.complexArg_eq_arctan_of_re_pos
    (z := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by norm_num)
  convert h using 1 <;> norm_num
  field_simp

theorem kapustinCriticalPoint_cpow (β t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ^ (β : ℂ) =
      (Real.exp (β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖) : ℂ) *
        Complex.exp (I * (β * Real.arctan (2 * t) : ℂ)) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I
  rw [Complex.cpow_def_of_ne_zero (kapustinCriticalPoint_ne_zero t)]
  have hlog : Complex.log z =
      (Real.log ‖z‖ : ℂ) + (z.arg : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im]
  rw [hlog, kapustinCriticalPoint_arg]
  rw [show ((Real.log ‖z‖ : ℂ) + (Real.arctan (2 * t) : ℂ) * I) * (β : ℂ) =
      (β * Real.log ‖z‖ : ℝ) + I * (β * Real.arctan (2 * t) : ℂ) by
        push_cast
        ring]
  rw [Complex.exp_add]
  simp [z]

theorem kapustinBaseCpow (t : ℝ) :
    (((2 * Real.pi : ℝ) : ℂ) ^
      (((-3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      (Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) : ℂ) *
        Complex.exp (I * (t * Real.log (2 * Real.pi) : ℂ)) := by
  rw [GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp
    (mul_pos (by norm_num) Real.pi_pos)]
  rw [show (Real.log (2 * Real.pi) : ℂ) *
      (((-3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (((-3 / 2 : ℝ) * Real.log (2 * Real.pi) : ℝ) : ℂ) +
        I * (t * Real.log (2 * Real.pi) : ℂ) by
          push_cast
          ring]
  rw [Complex.exp_add]
  simp

private theorem kapustinPowerGaugeAmplitude_factor (β t : ℝ) :
    kapustinPowerGaugeAmplitude β t =
      Real.exp ((-3 / 2 : ℝ) * Real.log (2 * Real.pi)) /
        (‖gammaVerticalValue (1 / 2) t‖ *
          Real.exp (β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖)) := by
  unfold kapustinPowerGaugeAmplitude
  rw [Real.exp_sub]
  have hgamma : ‖gammaVerticalValue (1 / 2) t‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) t)
  have hexp : Real.exp (β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖) ≠ 0 :=
    (Real.exp_pos _).ne'
  field_simp

private theorem kapustinPowerGaugePhase_factor (β t : ℝ) :
    Complex.exp (I * (kapustinPowerGaugePhase β t : ℂ)) =
      Complex.exp (I * (t * Real.log (2 * Real.pi) : ℂ)) /
        (Complex.exp (I * (gammaVerticalPhase (1 / 2) t : ℂ)) *
          Complex.exp (I * (β * Real.arctan (2 * t) : ℂ))) := by
  rw [show I * (kapustinPowerGaugePhase β t : ℂ) =
      I * (t * Real.log (2 * Real.pi) : ℂ) -
        I * (gammaVerticalPhase (1 / 2) t : ℂ) -
        I * (β * Real.arctan (2 * t) : ℂ) by
          unfold kapustinPowerGaugePhase
          push_cast
          ring]
  rw [Complex.exp_sub, Complex.exp_sub]
  field_simp

theorem kapustinPowerGaugeFormula_eq_Q (β t : ℝ) :
    kapustinPowerGaugeFormula β t = kapustinPowerGaugeQ β t := by
  rw [kapustinPowerGaugeFormula, kapustinBaseCpow, kapustinCriticalPoint_cpow]
  rw [show Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
    gammaVerticalValue (1 / 2) t from rfl]
  rw [gammaVerticalValue_eq_norm_mul_exp_phase (by norm_num : (0 : ℝ) < 1 / 2),
    kapustinPowerGaugeQ, kapustinPowerGaugeAmplitude_factor, kapustinPowerGaugePhase_factor]
  have hg : (↑‖gammaVerticalValue (1 / 2) t‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) t))
  have hd : (↑(Real.exp
      (β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_ne_zero _)
  field_simp [hg, hd]
  push_cast
  field_simp [hg, hd]

theorem kapustinPowerGaugeAmplitude_pos (β t : ℝ) :
    0 < kapustinPowerGaugeAmplitude β t := by
  unfold kapustinPowerGaugeAmplitude
  exact div_pos (Real.exp_pos _) (norm_pos_iff.mpr
    (gammaVerticalValue_ne_zero (by norm_num) t))

theorem kapustinPowerGaugeWeight_eq_cos (β t : ℝ) :
    kapustinPowerGaugeWeight β t =
      kapustinPowerGaugeAmplitude β t * Real.cos (kapustinPowerGaugePhase β t) := by
  simp [kapustinPowerGaugeWeight, kapustinPowerGaugeQ, Complex.exp_re]

theorem continuous_kapustinPowerGaugePhase (β : ℝ) :
    Continuous (kapustinPowerGaugePhase β) := by
  have hgammaDiff : Differentiable ℝ (gammaVerticalPhase (1 / 2)) :=
    fun t => (hasDerivAt_gammaVerticalPhase (σ := 1 / 2) (by norm_num) t).differentiableAt
  have hgamma := hgammaDiff.continuous
  unfold kapustinPowerGaugePhase
  fun_prop

theorem continuous_kapustinPowerGaugeAmplitude (β : ℝ) :
    Continuous (kapustinPowerGaugeAmplitude β) := by
  have hgammaDiff : Differentiable ℝ (gammaVerticalValue (1 / 2)) :=
    fun t => (hasDerivAt_gammaVerticalValue (σ := 1 / 2) (by norm_num) t).differentiableAt
  have hgamma := hgammaDiff.continuous
  have hgamma0 : ∀ t, ‖gammaVerticalValue (1 / 2) t‖ ≠ 0 := fun t =>
    norm_ne_zero_iff.mpr (gammaVerticalValue_ne_zero (by norm_num) t)
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hznorm : ‖((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hzcont : Continuous (fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
    fun_prop
  have hnormcont : ContinuousAt
      (fun u : ℝ => ‖((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I‖) t :=
    hzcont.continuousAt.norm
  have hlogcont : ContinuousAt
      (fun u : ℝ => Real.log ‖((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I‖) t :=
    hnormcont.log hznorm
  have hinner : ContinuousAt (fun u : ℝ =>
      (-3 / 2 : ℝ) * Real.log (2 * Real.pi) -
        β * Real.log ‖((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I‖) t :=
    continuousAt_const.sub (continuousAt_const.mul hlogcont)
  have hnum := Real.continuous_exp.continuousAt.comp hinner
  have hden : ContinuousAt (fun u : ℝ => ‖gammaVerticalValue (1 / 2) u‖) t :=
    hgamma.continuousAt.norm
  unfold kapustinPowerGaugeAmplitude
  exact hnum.div hden (hgamma0 t)

theorem continuous_kapustinPowerGaugeWeight (β : ℝ) :
    Continuous (kapustinPowerGaugeWeight β) := by
  rw [show kapustinPowerGaugeWeight β = fun t =>
    kapustinPowerGaugeAmplitude β t * Real.cos (kapustinPowerGaugePhase β t) from
      funext (kapustinPowerGaugeWeight_eq_cos β)]
  exact (continuous_kapustinPowerGaugeAmplitude β).mul
    (Real.continuous_cos.comp (continuous_kapustinPowerGaugePhase β))

theorem tendsto_kapustinPowerGaugePhase_div_scale (β : ℝ) :
    Tendsto (fun t : ℝ => kapustinPowerGaugePhase β t / (t * Real.log t))
      atTop (nhds (-1)) := by
  have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hscale : Tendsto (fun t : ℝ => t * Real.log t) atTop atTop :=
    Tendsto.atTop_mul_atTop₀ tendsto_id hlogtop
  have hinvscale : Tendsto (fun t : ℝ => (t * Real.log t)⁻¹) atTop (nhds 0) :=
    hscale.inv_tendsto_atTop
  have hinvlog : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (nhds 0) :=
    hlogtop.inv_tendsto_atTop
  have hlinear : Tendsto (fun t : ℝ =>
      (t * Real.log (2 * Real.pi)) / (t * Real.log t)) atTop (nhds 0) := by
    have h := hinvlog.const_mul (Real.log (2 * Real.pi))
    have h' : Tendsto (fun t : ℝ => Real.log (2 * Real.pi) * (Real.log t)⁻¹)
        atTop (nhds 0) := by simpa using h
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    field_simp [ht0, (Real.log_pos ht).ne']
  have htwo : Tendsto (fun t : ℝ => 2 * t) atTop atTop := by
    simpa [mul_comm] using tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2)
  have hatan : Tendsto (fun t : ℝ => Real.arctan (2 * t)) atTop
      (nhds (Real.pi / 2)) := by
    exact (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp htwo
  have hatanRatio : Tendsto (fun t : ℝ =>
      Real.arctan (2 * t) / (t * Real.log t)) atTop (nhds 0) := by
    have h := hatan.mul hinvscale
    simpa [div_eq_mul_inv] using h
  have hgamma := tendsto_gammaVerticalPhase_ratio (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomb := (hlinear.sub hgamma).sub (hatanRatio.const_mul β)
  simpa only [sub_neg_eq_add, zero_sub, mul_zero, sub_zero] using hcomb.congr'
    (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
      have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
      dsimp only [kapustinPowerGaugePhase]
      field_simp [ht0, hlog0])

theorem tendsto_kapustinPowerGaugePhase_atBot (β : ℝ) :
    Tendsto (kapustinPowerGaugePhase β) atTop atBot := by
  have hratio := tendsto_kapustinPowerGaugePhase_div_scale β
  have hratioBound : ∀ᶠ t : ℝ in atTop,
      kapustinPowerGaugePhase β t / (t * Real.log t) ≤ -(1 / 2 : ℝ) := by
    obtain ⟨T, hmetric⟩ := (Metric.tendsto_atTop.mp hratio) (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop T] with t htT
    have ht := hmetric t htT
    rw [Real.dist_eq] at ht
    have := (abs_lt.mp ht).2
    linarith
  have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hscale : Tendsto (fun t : ℝ => t * Real.log t) atTop atTop :=
    Tendsto.atTop_mul_atTop₀ tendsto_id hlogtop
  apply tendsto_atBot.mpr
  intro b
  have hlarge := (tendsto_atTop.mp hscale) (max 0 (-2 * b))
  filter_upwards [hratioBound, hlarge, eventually_gt_atTop (1 : ℝ)] with t hratio hlarge ht
  have hscale0 : 0 ≤ t * Real.log t := le_trans (le_max_left _ _) hlarge
  have hfactor : kapustinPowerGaugePhase β t =
      (kapustinPowerGaugePhase β t / (t * Real.log t)) * (t * Real.log t) := by
    field_simp [ne_of_gt (lt_trans zero_lt_one ht), (Real.log_pos ht).ne']
  rw [hfactor]
  have hupper := mul_le_mul_of_nonneg_right hratio hscale0
  by_cases hb : 0 ≤ b
  · nlinarith
  · have hbscale : -2 * b ≤ t * Real.log t :=
      le_trans (le_max_right 0 (-2 * b)) hlarge
    nlinarith

@[simp] theorem kapustinPowerGaugePhase_neg (β t : ℝ) :
    kapustinPowerGaugePhase β (-t) = -kapustinPowerGaugePhase β t := by
  simp [kapustinPowerGaugePhase]
  ring

@[simp] theorem kapustinPowerGaugeAmplitude_neg (β t : ℝ) :
    kapustinPowerGaugeAmplitude β (-t) = kapustinPowerGaugeAmplitude β t := by
  unfold kapustinPowerGaugeAmplitude gammaVerticalValue
  have hpoint : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I =
      (starRingEnd ℂ) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hpoint, Complex.norm_conj, Complex.Gamma_conj, Complex.norm_conj]

@[simp] theorem kapustinPowerGaugeWeight_neg (β t : ℝ) :
    kapustinPowerGaugeWeight β (-t) = kapustinPowerGaugeWeight β t := by
  rw [kapustinPowerGaugeWeight_eq_cos, kapustinPowerGaugeWeight_eq_cos,
    kapustinPowerGaugeAmplitude_neg, kapustinPowerGaugePhase_neg, Real.cos_neg]

abbrev KapustinPowerCarrier (β : ℝ) :=
  GaloisForLFunctions.HTGeometry.signedWeightEvenSubspace
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

abbrev KapustinPowerNegativeSector (β : ℝ) :=
  GaloisForLFunctions.HTGeometry.weightNegativeSector
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

abbrev KapustinPowerPositiveSector (β : ℝ) :=
  GaloisForLFunctions.HTGeometry.weightPositiveSector
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

def kapustinPowerFundamentalSymmetry (β : ℝ) :
    KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β :=
  GaloisForLFunctions.HTGeometry.weightFundamentalSymmetry
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

def kapustinPowerNegativeProjection (β : ℝ) :
    KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β :=
  GaloisForLFunctions.HTGeometry.weightNegativeProjection
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

def kapustinPowerPositiveProjection (β : ℝ) :
    KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β :=
  GaloisForLFunctions.HTGeometry.weightPositiveProjection
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

/-- Arbitrarily long alternating chains occur on the positive critical half-line.  Continuity then
places each chain node inside an open interval of the same strict sign. -/
theorem exists_kapustinPowerGauge_sign_chain (β : ℝ) (n : ℕ) :
    ∃ b : ℝ, ∃ g : ℕ → ℝ,
      0 ≤ b ∧
      (∀ i ≤ n, g i ∈ Set.Icc (0 : ℝ) b) ∧
      (∀ i < n, g i < g (i + 1)) ∧
      (∀ i < n,
        kapustinPowerGaugeWeight β (g i) *
          kapustinPowerGaugeWeight β (g (i + 1)) < 0) := by
  have hphaseTop : Tendsto (fun t => -kapustinPowerGaugePhase β t) atTop atTop :=
    tendsto_neg_atTop_iff.mpr (tendsto_kapustinPowerGaugePhase_atBot β)
  have hlevel : ∀ᶠ b : ℝ in atTop,
      ((n : ℝ) * Real.pi) ≤ -kapustinPowerGaugePhase β b :=
    tendsto_atTop.mp hphaseTop ((n : ℝ) * Real.pi)
  have hboth := hlevel.and (eventually_ge_atTop (0 : ℝ))
  obtain ⟨b, hbLevel, hb0⟩ := hboth.exists
  have hcont : ContinuousOn (fun t => -kapustinPowerGaugePhase β t) (Set.Icc 0 b) :=
    (continuous_kapustinPowerGaugePhase β).neg.continuousOn
  have hlow : -kapustinPowerGaugePhase β 0 ≤ ((0 : ℤ) : ℝ) * Real.pi := by
    simp [kapustinPowerGaugePhase, gammaVerticalPhase]
  obtain ⟨g, hgmem, hginc, hgsign⟩ :=
    exists_sign_chain_of_phase_increase
      (a := 0) (b := b) (φ := fun t => -kapustinPowerGaugePhase β t)
      (ρ := kapustinPowerGaugeAmplitude β) (m₀ := 0) (n := n)
      hb0 hcont (fun t _ => kapustinPowerGaugeAmplitude_pos β t) hlow (by simpa using hbLevel)
  refine ⟨b, g, hb0, hgmem, hginc, ?_⟩
  intro i hi
  simpa [kapustinPowerGaugeWeight_eq_cos, Real.cos_neg] using hgsign i hi

theorem exists_kapustinPowerGauge_positive_negative_points (β : ℝ) :
    ∃ tₚ tₙ : ℝ, 0 < tₚ ∧ 0 < tₙ ∧
      0 < kapustinPowerGaugeWeight β tₚ ∧ kapustinPowerGaugeWeight β tₙ < 0 := by
  obtain ⟨b, g, hb, hgmem, hginc, hgsign⟩ := exists_kapustinPowerGauge_sign_chain β 2
  have hg0 : 0 ≤ g 0 := (hgmem 0 (by norm_num)).1
  have hg1 : 0 < g 1 := lt_of_le_of_lt hg0 (hginc 0 (by norm_num))
  have hg2 : 0 < g 2 := lt_trans hg1 (hginc 1 (by norm_num))
  rcases (mul_neg_iff.mp (hgsign 1 (by norm_num))) with h | h
  · exact ⟨g 1, g 2, hg1, hg2, h.1, h.2⟩
  · exact ⟨g 2, g 1, hg2, hg1, h.2, h.1⟩

theorem exists_kapustinPowerGauge_positive_negative_Icc (β : ℝ) :
    ∃ aₚ bₚ aₙ bₙ : ℝ,
      0 < aₚ ∧ aₚ < bₚ ∧
      (∀ t ∈ Set.Icc aₚ bₚ, 0 < kapustinPowerGaugeWeight β t) ∧
      0 < aₙ ∧ aₙ < bₙ ∧
      (∀ t ∈ Set.Icc aₙ bₙ, kapustinPowerGaugeWeight β t < 0) := by
  obtain ⟨tₚ, tₙ, htₚ, htₙ, hwₚ, hwₙ⟩ :=
    exists_kapustinPowerGauge_positive_negative_points β
  obtain ⟨aₚ, bₚ, haₚ, habₚ, hpos⟩ :=
    GaloisForLFunctions.HTGeometry.exists_positive_Icc_of_continuous_of_pos
      (continuous_kapustinPowerGaugeWeight β) htₚ hwₚ
  obtain ⟨aₙ, bₙ, haₙ, habₙ, hneg⟩ :=
    GaloisForLFunctions.HTGeometry.exists_negative_Icc_of_continuous_of_neg
      (continuous_kapustinPowerGaugeWeight β) htₙ hwₙ
  exact ⟨aₚ, bₚ, aₙ, bₙ, haₚ, habₚ, hpos, haₙ, habₙ, hneg⟩

theorem kapustinPowerGauge_negativeSector_infinite (β : ℝ) :
    ¬ FiniteDimensional ℂ
      (GaloisForLFunctions.HTGeometry.weightNegativeSector
        (continuous_kapustinPowerGaugeWeight β).measurable
        (kapustinPowerGaugeWeight_neg β)) := by
  obtain ⟨aₚ, bₚ, aₙ, bₙ, _haₚ, _habₚ, _hpos, haₙ, habₙ, hneg⟩ :=
    exists_kapustinPowerGauge_positive_negative_Icc β
  exact GaloisForLFunctions.HTGeometry.weightNegativeSector_not_finiteDimensional_of_interval
    (continuous_kapustinPowerGaugeWeight β) (kapustinPowerGaugeWeight_neg β)
    haₙ habₙ hneg

theorem kapustinPowerGauge_positiveSector_infinite (β : ℝ) :
    ¬ FiniteDimensional ℂ
      (GaloisForLFunctions.HTGeometry.weightPositiveSector
        (continuous_kapustinPowerGaugeWeight β).measurable
        (kapustinPowerGaugeWeight_neg β)) := by
  obtain ⟨aₚ, bₚ, aₙ, bₙ, haₚ, habₚ, hpos, _haₙ, _habₙ, _hneg⟩ :=
    exists_kapustinPowerGauge_positive_negative_Icc β
  exact GaloisForLFunctions.HTGeometry.weightPositiveSector_not_finiteDimensional_of_interval
    (continuous_kapustinPowerGaugeWeight β) (kapustinPowerGaugeWeight_neg β)
    haₚ habₚ hpos

/-- For every `β > 0`, Kapustin's literal power-gauge carrier has Krein indices `(∞, ∞)`. -/
theorem kapustinPowerGauge_bilateral_infiniteKreinIndex (β : ℝ) (_hβ : 0 < β) :
    (¬ FiniteDimensional ℂ
      (GaloisForLFunctions.HTGeometry.weightPositiveSector
        (continuous_kapustinPowerGaugeWeight β).measurable
        (kapustinPowerGaugeWeight_neg β))) ∧
    (¬ FiniteDimensional ℂ
      (GaloisForLFunctions.HTGeometry.weightNegativeSector
        (continuous_kapustinPowerGaugeWeight β).measurable
        (kapustinPowerGaugeWeight_neg β))) :=
  ⟨kapustinPowerGauge_positiveSector_infinite β,
    kapustinPowerGauge_negativeSector_infinite β⟩

theorem kapustinPowerFundamentalSymmetry_negative (β : ℝ)
    (x : KapustinPowerCarrier β) (hx : x ∈ KapustinPowerNegativeSector β) :
    kapustinPowerFundamentalSymmetry β x = -x :=
  GaloisForLFunctions.HTGeometry.weightFundamentalSymmetry_negative
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β) x hx

theorem isClosed_kapustinPowerNegativeSector (β : ℝ) :
    IsClosed (KapustinPowerNegativeSector β : Set (KapustinPowerCarrier β)) :=
  GaloisForLFunctions.HTGeometry.isClosed_weightNegativeSector
    (continuous_kapustinPowerGaugeWeight β).measurable
    (kapustinPowerGaugeWeight_neg β)

/-- Quadratic-form version of `P₋ G P₋ ≥ P₋` on the literal power-gauge carrier. -/
theorem kapustinPowerGauge_negativeCompression_dominates_projection
    (β : ℝ) (_hβ : 0 < β) (G : KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β)
    (_hG : G.toLinearMap.IsSymmetric)
    (hpositive : ∀ x : KapustinPowerCarrier β,
      0 ≤ Complex.re ⟪(kapustinPowerFundamentalSymmetry β + G) x, x⟫_ℂ)
    (x : KapustinPowerCarrier β) :
    ‖kapustinPowerNegativeProjection β x‖ ^ 2 ≤
      Complex.re ⟪G (kapustinPowerNegativeProjection β x),
        kapustinPowerNegativeProjection β x⟫_ℂ := by
  apply GaloisForLFunctions.HTGeometry.fullSector_quadratic_lower_bound
    (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
    (kapustinPowerFundamentalSymmetry_negative β) hpositive
  exact ⟨x, rfl⟩

/-- Uniform positivity strengthens the compression floor from `1` to `1 + ε`. -/
theorem kapustinPowerGauge_negativeCompression_dominates_projection_of_uniform
    (β : ℝ) (_hβ : 0 < β) (G : KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β)
    (_hG : G.toLinearMap.IsSymmetric) (ε : ℝ)
    (hpositive : ∀ x : KapustinPowerCarrier β,
      ε * ‖x‖ ^ 2 ≤ Complex.re ⟪(kapustinPowerFundamentalSymmetry β + G) x, x⟫_ℂ)
    (x : KapustinPowerCarrier β) :
    (1 + ε) * ‖kapustinPowerNegativeProjection β x‖ ^ 2 ≤
      Complex.re ⟪G (kapustinPowerNegativeProjection β x),
        kapustinPowerNegativeProjection β x⟫_ℂ := by
  apply GaloisForLFunctions.HTGeometry.fullSector_quadratic_lower_bound_of_uniform
    (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β) ε
    (kapustinPowerFundamentalSymmetry_negative β) hpositive
  exact ⟨x, rfl⟩

/-- Every bounded self-adjoint correction making `Jβ + G` positive is infinite-rank,
noncompact, outside every finite Schatten class, and has essential norm at least one. -/
theorem kapustinPowerGauge_fullSector_correction_obstruction
    (β : ℝ) (hβ : 0 < β) (G : KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β)
    (_hG : G.toLinearMap.IsSymmetric)
    (hpositive : ∀ x : KapustinPowerCarrier β,
      0 ≤ Complex.re ⟪(kapustinPowerFundamentalSymmetry β + G) x, x⟫_ℂ) :
    (¬ IsCompactOperator G) ∧
    (¬ FiniteDimensional ℂ (LinearMap.range (G :
      KapustinPowerCarrier β →ₗ[ℂ] KapustinPowerCarrier β))) ∧
    1 ≤ essentialNorm G ∧
    (∀ p : ℝ, 0 < p → ¬ MemSchattenClass p G) ∧
    (∀ K : KapustinPowerCarrier β →L[ℂ] KapustinPowerCarrier β,
      IsCompactOperator K → 1 ≤ ‖G - K‖) := by
  have hSinfinite := (kapustinPowerGauge_bilateral_infiniteKreinIndex β hβ).2
  have hnegative := kapustinPowerFundamentalSymmetry_negative β
  have hclosed := isClosed_kapustinPowerNegativeSector β
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GaloisForLFunctions.HTGeometry.fullSector_not_isCompactOperator
      (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
      hclosed hSinfinite hnegative hpositive
  · exact GaloisForLFunctions.HTGeometry.fullSector_not_finiteDimensional_range
      (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
      hSinfinite hnegative hpositive
  · exact fullSector_one_le_essentialNorm
      (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
      hclosed hSinfinite hnegative hpositive
  · intro p hp
    exact fullSector_not_memSchattenClass
      (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
      hclosed hSinfinite hnegative hpositive hp
  · intro K hK
    exact GaloisForLFunctions.HTGeometry.fullSector_one_le_norm_sub_compact
      (kapustinPowerFundamentalSymmetry β) G (KapustinPowerNegativeSector β)
      hclosed hSinfinite hnegative hpositive K hK

end RHTower
