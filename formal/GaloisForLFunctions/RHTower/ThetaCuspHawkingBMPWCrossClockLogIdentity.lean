import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockMeanError
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockPrincipalGrowth
import Mathlib.Analysis.Complex.RealDeriv

/-! Exact logarithmic conjugation of the literal cross-branch cusp clock. -/

open Complex Filter Topology
open RHTower RHTower.D4BMModularCore RHTower.D4BMCuspResponse
open RHTower.D4BMMixedParticularCuspFlux
open RHTower.D4BMPWCrossClockMeanEquation
open RHTower.D4BMPWCrossClockMeanError RHTower.D4BMPWCrossClockPrincipalGrowth
open RHTower.D4BMLiteralCyclicPeierlsCrossBranchSource
open scoped ContDiff

namespace RHTower.D4BMPWCrossClockLogIdentity
noncomputable section
set_option autoImplicit false

/-- Double extreme cusp exponent of the actual two-branch product. -/
def rate (q : XiZeroCopy) : ℂ := 2 * sourcePower q 2

def normalizedMean (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-rate q*(t:ℂ)) * crossMean q (Real.exp t)

def normalizedForcing (q : XiZeroCopy) (t : ℝ) : ℂ :=
  Complex.exp (-rate q*(t:ℂ)) * forcingMean q (Real.exp t)

private theorem crossPlanar_smooth (q : XiZeroCopy) :
    ContDiffOn ℝ ∞ (crossPlanar q) {z : ℂ | 0 < z.im} :=
  ((fullAngular_smooth q true).planar_contDiffOn).mul
    ((fullAngular_smooth q false).planar_contDiffOn)

private theorem mean_first (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (crossMean q) (deriv (crossMean q) y) y :=
  (average_hasDerivAt (crossPlanar q) (crossPlanar_smooth q) hy).differentiableAt.hasDerivAt

private theorem mean_second (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (deriv (crossMean q)) (deriv (deriv (crossMean q)) y) y :=
  (average_second_hasDerivAt (crossPlanar q) (crossPlanar_smooth q) hy).differentiableAt.hasDerivAt

private theorem exp_rate_hasDerivAt (r : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (r*(s:ℂ)))
      (r*Complex.exp (r*(t:ℂ))) t := by
  have hc : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 t := by
    simpa only [id_eq,Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp
  apply ((hc.const_mul r).cexp).congr_deriv
  simp only [mul_one]
  ring

private theorem exp_cast_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp s:ℂ)) (Real.exp t:ℂ) t :=
  (Real.hasDerivAt_exp t).ofReal_comp

private theorem mean_comp_exp_first (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (fun s : ℝ => crossMean q (Real.exp s))
      ((Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t)) t := by
  have h := (mean_first q (Real.exp t) (Real.exp_pos t)).scomp t
    (Real.hasDerivAt_exp t)
  simpa only [Function.comp_def,Complex.real_smul] using h

private theorem mean_comp_exp_second (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (crossMean q) (Real.exp s))
      ((Real.exp t:ℂ)*deriv (deriv (crossMean q)) (Real.exp t)) t := by
  have h := (mean_second q (Real.exp t) (Real.exp_pos t)).scomp t
    (Real.hasDerivAt_exp t)
  simpa only [Function.comp_def,Complex.real_smul] using h

private theorem normalizedMean_first (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (normalizedMean q)
      (Complex.exp (-rate q*(t:ℂ)) *
        ((Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t) -
          rate q*crossMean q (Real.exp t))) t := by
  have hw := exp_rate_hasDerivAt (-rate q) t
  have hh := mean_comp_exp_first q t
  have h := hw.mul hh
  change HasDerivAt (normalizedMean q) _ t at h
  convert h using 1
  ring

private theorem normalizedMean_deriv (q : XiZeroCopy) :
    deriv (normalizedMean q) = fun (t : ℝ) =>
      Complex.exp (-rate q*(t:ℂ)) *
        ((Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t) -
          rate q*crossMean q (Real.exp t)) := by
  funext t
  exact (normalizedMean_first q t).deriv

private theorem normalizedMean_second (q : XiZeroCopy) (t : ℝ) :
    deriv (deriv (normalizedMean q)) t =
      Complex.exp (-rate q*(t:ℂ)) *
        ((Real.exp t:ℂ)^(2:ℕ)*deriv (deriv (crossMean q)) (Real.exp t) +
          (1-2*rate q)*(Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t) +
          rate q^(2:ℕ)*crossMean q (Real.exp t)) := by
  have hw := exp_rate_hasDerivAt (-rate q) t
  have hy := exp_cast_hasDerivAt t
  have hd := mean_comp_exp_second q t
  have hh := mean_comp_exp_first q t
  have ha := (hy.mul hd).sub (hh.const_mul (rate q))
  have h := hw.mul ha
  rw [normalizedMean_deriv]
  apply h.deriv.trans
  simp only [Pi.mul_apply,Pi.sub_apply]
  ring

/-- Exact log-height clock identity for the actual literal two-branch forcing,
without derivative bounds on either native L² response correction. -/
theorem normalizedForcing_eq_log_operator (q : XiZeroCopy) (t : ℝ) :
    normalizedForcing q t =
      deriv (deriv (normalizedMean q)) t +
        (2*rate q-1)*deriv (normalizedMean q) t +
        (rate q*(rate q-1)-20)*normalizedMean q t := by
  have hc := crossMean_clock_equation q (Real.exp_pos t)
  rw [crossBranchClockParameter_eq_twenty] at hc
  rw [normalizedMean_second, (normalizedMean_first q t).deriv]
  change Complex.exp (-rate q*(t:ℂ))*forcingMean q (Real.exp t) = _
  simp only [normalizedMean]
  linear_combination -Complex.exp (-rate q*(t:ℂ))*hc

theorem rate_re_bounds (q : XiZeroCopy) (hleft : (q.1 : ℂ).re < 1/2) :
    2 < (rate q).re ∧ (rate q).re < 4 := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  have hr : (rate q).re = 4 - 4*(q.1 : ℂ).re := by
    change (2*(2-2*(q.1:ℂ))).re = 4 - 4*(q.1:ℂ).re
    norm_num [Complex.mul_re,Complex.sub_re]
    ring
  constructor <;> rw [hr] <;> linarith

/-- The actual off-line leading product cannot resonate with the physical
clock root at `5` or `−4`. -/
theorem rate_clock_gap_ne_zero (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    rate q*(rate q-1)-20 ≠ 0 := by
  intro hg
  have hfactor : (rate q-5)*(rate q+4) = 0 := by
    calc
      _ = rate q*(rate q-1)-20 := by ring
      _ = 0 := hg
  rcases mul_eq_zero.mp hfactor with hfive | hnegfour
  · have hb := (rate_re_bounds q hleft).2
    rw [sub_eq_zero.mp hfive] at hb
    norm_num at hb
  · have hb := (rate_re_bounds q hleft).1
    have hr : rate q = -4 := (add_eq_zero_iff_eq_neg).mp hnegfour
    rw [hr] at hb
    norm_num at hb

/-- Exact principal product supplies the nonzero asymptotic datum for the
logarithmically conjugated source test. -/
theorem normalizedPrincipal_tendsto (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    Tendsto (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
      principalCross q (Real.exp t)) atTop
      (𝓝 (responseCoefficient q true 2 * responseCoefficient q false 2)) := by
  have h := (cuspResponse_cross_left_normalized_nonzero q hleft).2.comp
    Real.tendsto_exp_atTop
  apply h.congr'
  filter_upwards with t
  have hy : (Real.exp t:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  have hpow : ((Real.exp t:ℂ)^(-sourcePower q 2)) *
      ((Real.exp t:ℂ)^(-sourcePower q 2)) =
        Complex.exp (-rate q*(t:ℂ)) := by
    rw [← Complex.cpow_add _ _ hy,
      GaloisForLFunctions.HTGeometry.ofReal_cpow_eq_exp (Real.exp_pos t),
      Real.log_exp]
    congr 1
    dsimp [rate]
    ring
  dsimp only [principalCross,Function.comp_apply]
  rw [← hpow]
  ring

/-- Positive-height smoothness gives one further derivative of the actual cusp mean. -/
private theorem mean_third (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (deriv (deriv (crossMean q)))
      (deriv (deriv (deriv (crossMean q))) y) y := by
  have hf2 : ContDiffOn ℝ ∞ (vertical (vertical (crossPlanar q)))
      {z : ℂ | 0 < z.im} :=
    planar_derivative_contDiffOn
      (planar_derivative_contDiffOn (crossPlanar_smooth q) Complex.I) Complex.I
  have h := average_hasDerivAt (vertical (vertical (crossPlanar q))) hf2 hy
  have hh : HasDerivAt (deriv (deriv (crossMean q)))
      (average (vertical (vertical (vertical (crossPlanar q)))) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (average_second_hasDerivAt (crossPlanar q) (crossPlanar_smooth q) ht).deriv
  exact hh.differentiableAt.hasDerivAt

theorem normalizedMean_hasDerivAt (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (normalizedMean q) (deriv (normalizedMean q) t) t :=
  (normalizedMean_first q t).differentiableAt.hasDerivAt

theorem normalizedMean_deriv_hasDerivAt (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (deriv (normalizedMean q))
      (deriv (deriv (normalizedMean q)) t) t := by
  have hw := exp_rate_hasDerivAt (-rate q) t
  have hy := exp_cast_hasDerivAt t
  have hd := mean_comp_exp_second q t
  have hh := mean_comp_exp_first q t
  have ha := (hy.mul hd).sub (hh.const_mul (rate q))
  have h := hw.mul ha
  rw [normalizedMean_deriv]
  exact h.differentiableAt.hasDerivAt

theorem normalizedMean_second_continuous (q : XiZeroCopy) :
    Continuous (deriv (deriv (normalizedMean q))) := by
  have hc0 : Continuous (fun t : ℝ => crossMean q (Real.exp t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (mean_first q (Real.exp t) (Real.exp_pos t)).continuousAt.comp
        Real.continuous_exp.continuousAt)
  have hc1 : Continuous (fun t : ℝ => deriv (crossMean q) (Real.exp t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (mean_second q (Real.exp t) (Real.exp_pos t)).continuousAt.comp
        Real.continuous_exp.continuousAt)
  have hc2 : Continuous (fun t : ℝ => deriv (deriv (crossMean q)) (Real.exp t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (mean_third q (Real.exp t) (Real.exp_pos t)).continuousAt.comp
        Real.continuous_exp.continuousAt)
  have hy : Continuous (fun t : ℝ => (Real.exp t:ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_exp
  have hw : Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ))) := by fun_prop
  have hi : Continuous (fun t : ℝ =>
      (Real.exp t:ℂ)^(2:ℕ)*deriv (deriv (crossMean q)) (Real.exp t) +
      (1-2*rate q)*(Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t) +
      rate q^(2:ℕ)*crossMean q (Real.exp t)) :=
    (((hy.pow 2).mul hc2).add ((continuous_const.mul hy).mul hc1)).add
      (continuous_const.mul hc0)
  have heq : (fun t : ℝ => deriv (deriv (normalizedMean q)) t) =
      (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
        ((Real.exp t:ℂ)^(2:ℕ)*deriv (deriv (crossMean q)) (Real.exp t) +
          (1-2*rate q)*(Real.exp t:ℂ)*deriv (crossMean q) (Real.exp t) +
        rate q^(2:ℕ)*crossMean q (Real.exp t))) :=
    funext (normalizedMean_second q)
  change Continuous (fun t : ℝ => deriv (deriv (normalizedMean q)) t)
  rw [heq]
  exact hw.mul hi

end
end RHTower.D4BMPWCrossClockLogIdentity
