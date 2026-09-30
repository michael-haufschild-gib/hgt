import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section
namespace RHTower

def liClockCriticalScalarKernelComplex (w : ℂ) : ℂ :=
  ∑' m : ℕ, w^m / ((m.factorial : ℂ)^2)

def liClockCriticalPositiveKernel (w : ℝ) : ℝ :=
  ∑' m : ℕ, w^m / ((m.factorial : ℝ)^2)

def liClockCriticalOscillatoryKernel (w : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ)^m * w^m / ((m.factorial : ℝ)^2)

def liClockCriticalEvenKernel (w : ℝ) : ℝ :=
  ∑' j : ℕ, w^(2*j) / (((2*j).factorial : ℝ)^2)

private theorem ca_factorial_one_le (n : ℕ) : (1 : ℝ) ≤ n.factorial := by
  have hn : 1 ≤ n.factorial := by have := Nat.factorial_pos n; omega
  exact_mod_cast hn

private theorem ca_norm_term_le (w : ℂ) (n : ℕ) :
    ‖w^n / ((n.factorial : ℂ)^2)‖ ≤ ‖w‖^n / (n.factorial : ℝ) := by
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hf := ca_factorial_one_le n
  apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg w) n) (by positivity)
  nlinarith

theorem summable_norm_liClockCriticalScalarTermComplex (w : ℂ) :
  Summable (fun m : ℕ => ‖w^m / ((m.factorial : ℂ)^2)‖) := by
  exact (Real.summable_pow_div_factorial ‖w‖).of_nonneg_of_le
    (fun n => norm_nonneg _) (ca_norm_term_le w)

private theorem ca_summable_real (w : ℝ) :
    Summable (fun n : ℕ => w^n / ((n.factorial : ℝ)^2)) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (summable_norm_liClockCriticalScalarTermComplex (w : ℂ)).of_norm

private theorem ca_summable_even (w : ℝ) :
    Summable (fun j : ℕ => w^(2*j) / (((2*j).factorial : ℝ)^2)) := by
  exact (ca_summable_real w).comp_injective (fun x y h => by omega)

private theorem ca_oscillatory_eq_neg (w : ℝ) :
    liClockCriticalOscillatoryKernel w = liClockCriticalPositiveKernel (-w) := by
  unfold liClockCriticalOscillatoryKernel liClockCriticalPositiveKernel
  apply tsum_congr
  intro n
  rw [show (-w)^n = (-1 : ℝ)^n*w^n by
    simpa only [neg_one_mul] using mul_pow (-1 : ℝ) w n]

theorem liClockCriticalPositiveKernel_nonneg {w : ℝ} (hw : 0≤w) :
  0≤liClockCriticalPositiveKernel w := by
  exact tsum_nonneg (fun n => div_nonneg (pow_nonneg hw n) (sq_nonneg _))

theorem liClockCriticalEvenKernel_nonneg (w : ℝ) :
  0≤liClockCriticalEvenKernel w := by
  apply tsum_nonneg
  intro j
  exact div_nonneg (by rw [pow_mul]; positivity) (sq_nonneg _)

private theorem ca_complex_ofReal (w : ℝ) :
    liClockCriticalScalarKernelComplex (w : ℂ) =
      (liClockCriticalPositiveKernel w : ℂ) := by
  simp only [liClockCriticalScalarKernelComplex, liClockCriticalPositiveKernel,
    Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]

theorem liClockCriticalEvenKernel_eq_half (w : ℝ) :
  liClockCriticalEvenKernel w =
    (liClockCriticalPositiveKernel w + liClockCriticalOscillatoryKernel w)/2 := by
  have he : HasSum (fun j : ℕ =>
      w^(2*j) / (((2*j).factorial : ℝ)^2) +
        (-w)^(2*j) / (((2*j).factorial : ℝ)^2))
      (2*liClockCriticalEvenKernel w) := by
    apply ((ca_summable_even w).hasSum.mul_left 2).congr_fun
    intro j
    have hn : (-w)^(2*j) = w^(2*j) := by
      rw [pow_mul, pow_mul]
      congr 1
      ring
    rw [hn]
    ring
  have ho : HasSum (fun j : ℕ =>
      w^(2*j+1) / (((2*j+1).factorial : ℝ)^2) +
        (-w)^(2*j+1) / (((2*j+1).factorial : ℝ)^2)) (0 : ℝ) := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).congr_fun
    intro j
    have hn : (-w)^(2*j+1) = -(w^(2*j+1)) := by
      rw [pow_add, pow_add, pow_one, pow_one, pow_mul, pow_mul]
      have hs : (-w)^2 = w^2 := by ring
      rw [hs]
      ring
    rw [hn]
    ring
  have hh := ((ca_summable_real w).hasSum.add (ca_summable_real (-w)).hasSum).unique
    (he.even_add_odd ho)
  change liClockCriticalPositiveKernel w + liClockCriticalPositiveKernel (-w) =
    2*liClockCriticalEvenKernel w+0 at hh
  rw [ca_oscillatory_eq_neg]
  linarith

private theorem ca_continuous_complex : Continuous liClockCriticalScalarKernelComplex := by
  rw [continuous_iff_continuousAt]
  intro w
  let R : ℝ := ‖w‖+1
  have hc : ContinuousOn liClockCriticalScalarKernelComplex (Metric.closedBall 0 R) := by
    apply continuousOn_tsum (fun n => ((continuous_id.pow n).div_const _).continuousOn)
      (Real.summable_pow_div_factorial R)
    intro n z hz
    have hzR : ‖z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    calc
      ‖z^n / ((n.factorial : ℂ)^2)‖ ≤ ‖z‖^n / (n.factorial : ℝ) := ca_norm_term_le z n
      _ ≤ R^n / (n.factorial : ℝ) := by gcongr
  apply hc.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  simp [Metric.mem_ball, R]

theorem continuous_liClockCriticalPositiveKernel :
  Continuous liClockCriticalPositiveKernel := by
  have h := Complex.continuous_re.comp (ca_continuous_complex.comp Complex.continuous_ofReal)
  simpa only [Function.comp_def, ca_complex_ofReal, Complex.ofReal_re] using h

theorem continuous_liClockCriticalOscillatoryKernel :
  Continuous liClockCriticalOscillatoryKernel := by
  simpa only [Function.comp_def, ← ca_oscillatory_eq_neg] using
    continuous_liClockCriticalPositiveKernel.comp continuous_neg

theorem continuous_liClockCriticalEvenKernel :
  Continuous liClockCriticalEvenKernel := by
  have h := (continuous_liClockCriticalPositiveKernel.add
    continuous_liClockCriticalOscillatoryKernel).div_const (2 : ℝ)
  change Continuous (fun x => (liClockCriticalPositiveKernel x +
    liClockCriticalOscillatoryKernel x)/2) at h
  simpa only [← liClockCriticalEvenKernel_eq_half] using h

private theorem ca_cos_moment_even (j : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos θ^(2*j)) =
      (2*Real.pi)*((2*j).factorial : ℝ) / (4^j*(j.factorial : ℝ)^2) := by
  induction j with
  | zero => simp [two_mul]
  | succ j ih =>
    have hrec := integral_cos_pow (a := -Real.pi) (b := Real.pi) (2*j)
    simp only [Real.sin_pi, Real.sin_neg, neg_zero, mul_zero, sub_self, zero_div,
      zero_add] at hrec
    rw [show 2*(j+1)=2*j+2 by omega, hrec, ih]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    have h4 : (4 : ℝ)^j ≠ 0 := by positivity
    have hj : (j : ℝ)+1 ≠ 0 := by positivity
    have h2 : 2*(j : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

private theorem ca_cos_moment_odd (j : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos θ^(2*j+1)) = 0 := by
  induction j with
  | zero => simp [integral_cos]
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega, integral_cos_pow, ih]
    simp

private theorem ca_taylor_integral (q : ℂ) :
    HasSum (fun n : ℕ => ∫ θ in (-Real.pi)..Real.pi,
      (q*(Real.cos θ : ℂ))^n / (n.factorial : ℂ))
      (∫ θ in (-Real.pi)..Real.pi, Complex.exp (q*(Real.cos θ : ℂ))) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖q‖^n / (n.factorial : ℝ))
  · intro n
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · intro n
    filter_upwards [] with θ _
    simp only [norm_div, norm_pow, norm_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    have hcos := Real.abs_cos_le_one θ
    calc
      (‖q‖*|Real.cos θ|)^n / (n.factorial : ℝ) ≤
          (‖q‖*1)^n / (n.factorial : ℝ) := by gcongr
      _ = ‖q‖^n / (n.factorial : ℝ) := by rw [mul_one]
  · filter_upwards [] with θ _
    exact Real.summable_pow_div_factorial ‖q‖
  · exact intervalIntegrable_const
  · filter_upwards [] with θ _
    simpa only [Complex.exp_eq_exp_ℂ] using
      NormedSpace.expSeries_div_hasSum_exp (q*(Real.cos θ : ℂ))

private theorem ca_integrated_term (q : ℂ) (n : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, (q*(Real.cos θ : ℂ))^n / (n.factorial : ℂ)) =
      (q^n/(n.factorial : ℂ)) *
        ((∫ θ in (-Real.pi)..Real.pi, Real.cos θ^n : ℝ) : ℂ) := by
  calc
    _ = ∫ θ in (-Real.pi)..Real.pi,
        (q^n/(n.factorial : ℂ))*((Real.cos θ^n : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro θ _
      push_cast
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

theorem liClockCriticalAngularIntegral_exp (q : ℂ) :
  (∫ θ in (-Real.pi)..Real.pi,
    Complex.exp (q * (Real.cos θ : ℂ))) =
      (2*Real.pi : ℂ) * liClockCriticalScalarKernelComplex (q^2/4) := by
  have he : HasSum (fun j : ℕ => ∫ θ in (-Real.pi)..Real.pi,
      (q*(Real.cos θ : ℂ))^(2*j) / ((2*j).factorial : ℂ))
      ((2*Real.pi : ℂ)*liClockCriticalScalarKernelComplex (q^2/4)) := by
    apply (((summable_norm_liClockCriticalScalarTermComplex (q^2/4)).of_norm).hasSum.mul_left
      (2*Real.pi : ℂ)).congr_fun
    intro j
    rw [ca_integrated_term, ca_cos_moment_even]
    push_cast
    have hf : ((2*j).factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2*j)
    have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [div_pow, pow_mul]
    field_simp
  have ho : HasSum (fun j : ℕ => ∫ θ in (-Real.pi)..Real.pi,
      (q*(Real.cos θ : ℂ))^(2*j+1) / ((2*j+1).factorial : ℂ)) (0 : ℂ) := by
    apply (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0).congr_fun
    intro j
    rw [ca_integrated_term, ca_cos_moment_odd]
    simp
  have hh := (ca_taylor_integral q).unique (he.even_add_odd ho)
  simpa only [add_zero] using hh

theorem liClockCriticalAngularIntegral_real_exp (q : ℝ) :
  (∫ θ in (-Real.pi)..Real.pi, Real.exp (q*Real.cos θ)) =
    2*Real.pi * liClockCriticalPositiveKernel (q^2/4) := by
  apply Complex.ofReal_injective
  calc
    ((∫ θ in (-Real.pi)..Real.pi, Real.exp (q*Real.cos θ) : ℝ) : ℂ) =
        ∫ θ in (-Real.pi)..Real.pi, Complex.exp ((q : ℂ)*(Real.cos θ : ℂ)) := by
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro θ _
      push_cast
      rfl
    _ = (2*Real.pi : ℂ)*liClockCriticalScalarKernelComplex ((q : ℂ)^2/4) :=
      liClockCriticalAngularIntegral_exp (q : ℂ)
    _ = ((2*Real.pi*liClockCriticalPositiveKernel (q^2/4) : ℝ) : ℂ) := by
      rw [show (q : ℂ)^2/4 = ((q^2/4 : ℝ) : ℂ) by push_cast; rfl,
        ca_complex_ofReal]
      push_cast
      rfl

theorem liClockCriticalAngularIntegral_real_cos (q : ℝ) :
  (∫ θ in (-Real.pi)..Real.pi, Real.cos (q*Real.cos θ)) =
    2*Real.pi * liClockCriticalOscillatoryKernel (q^2/4) := by
  have hi : IntervalIntegrable
      (fun θ : ℝ => Complex.exp (((q : ℂ)*Complex.I)*(Real.cos θ : ℂ)))
      volume (-Real.pi) Real.pi := Continuous.intervalIntegrable (by fun_prop) _ _
  have hl : Complex.re
      (∫ θ in (-Real.pi)..Real.pi,
        Complex.exp (((q : ℂ)*Complex.I)*(Real.cos θ : ℂ))) =
      ∫ θ in (-Real.pi)..Real.pi, Real.cos (q*Real.cos θ) := by
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi,
          (Complex.exp (((q : ℂ)*Complex.I)*(Real.cos θ : ℂ))).re := by
        simpa only [Complex.reCLM_apply] using
          (Complex.reCLM.intervalIntegral_comp_comm hi).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re]
  have he := congrArg Complex.re
    (liClockCriticalAngularIntegral_exp ((q : ℂ)*Complex.I))
  rw [hl] at he
  have hq : ((q : ℂ)*Complex.I)^2/4 = ((-(q^2/4) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hq, ca_complex_ofReal, ← ca_oscillatory_eq_neg] at he
  simpa using he

theorem abs_liClockCriticalOscillatoryKernel_le_one {w : ℝ} (hw : 0≤w) :
  |liClockCriticalOscillatoryKernel w|≤1 := by
  have hq : (2*Real.sqrt w)^2/4 = w := by nlinarith [Real.sq_sqrt hw]
  have hi := liClockCriticalAngularIntegral_real_cos (2*Real.sqrt w)
  rw [hq] at hi
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ => Real.cos ((2*Real.sqrt w)*Real.cos θ))
    (fun θ _ => by simpa only [Real.norm_eq_abs] using
      Real.abs_cos_le_one ((2*Real.sqrt w)*Real.cos θ))
  rw [hi] at hb
  have hp : 0 < 2*Real.pi := by positivity
  have hlen : |Real.pi-(-Real.pi)| = 2*Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp, hlen, one_mul] at hb
  exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_one] using hb)

private theorem ca_positive_le_exp_sqrt {w : ℝ} (hw : 0≤w) :
    liClockCriticalPositiveKernel w ≤ Real.exp (2*Real.sqrt w) := by
  have hq : (2*Real.sqrt w)^2/4 = w := by nlinarith [Real.sq_sqrt hw]
  have hi := liClockCriticalAngularIntegral_real_exp (2*Real.sqrt w)
  rw [hq] at hi
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi) (C := Real.exp (2*Real.sqrt w))
    (f := fun θ : ℝ => Real.exp ((2*Real.sqrt w)*Real.cos θ))
    (fun θ _ => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      have hcos := (abs_le.mp (Real.abs_cos_le_one θ)).2
      calc
        (2*Real.sqrt w)*Real.cos θ ≤ (2*Real.sqrt w)*1 := by gcongr
        _ = 2*Real.sqrt w := by ring)
  rw [hi] at hb
  have hp : 0 < 2*Real.pi := by positivity
  have hlen : |Real.pi-(-Real.pi)| = 2*Real.pi := by
    rw [abs_of_pos (by linarith [Real.pi_pos])]
    ring
  rw [Real.norm_of_nonneg (mul_nonneg hp.le
    (liClockCriticalPositiveKernel_nonneg hw)), hlen] at hb
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ ≤ Real.exp (2*Real.sqrt w)*(2*Real.pi) := hb
    _ = (2*Real.pi)*Real.exp (2*Real.sqrt w) := by ring

private theorem ca_even_le_exp_sqrt {w : ℝ} (hw : 0≤w) :
    liClockCriticalEvenKernel w ≤ Real.exp (2*Real.sqrt w) := by
  have hh := ca_positive_le_exp_sqrt hw
  have hj := (le_abs_self (liClockCriticalOscillatoryKernel w)).trans
    (abs_liClockCriticalOscillatoryKernel_le_one hw)
  have he : 1 ≤ Real.exp (2*Real.sqrt w) := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 2*Real.sqrt w by positivity)
  rw [liClockCriticalEvenKernel_eq_half]
  linarith

private theorem ca_decay_majorant {a t r : ℝ} (ha : 0<a) (ht : 0≤t) (hr : 0<r) :
    ‖Real.exp (-a*r)*liClockCriticalEvenKernel (t*r)‖ ≤
      Real.exp (2*t/a)*Real.exp ((-a/2)*r) := by
  have htr : 0 ≤ t*r := mul_nonneg ht hr.le
  have hs := Real.sq_sqrt htr
  have hm : (a*r/2)*(2*t/a) = t*r := by field_simp
  have hsum : 0 ≤ a*r/2+2*t/a := by positivity
  have hy : 2*Real.sqrt (t*r) ≤ a*r/2+2*t/a := by
    nlinarith [sq_nonneg (a*r/2-2*t/a), Real.sqrt_nonneg (t*r)]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (liClockCriticalEvenKernel_nonneg _))]
  calc
    _ ≤ Real.exp (-a*r)*Real.exp (2*Real.sqrt (t*r)) :=
      mul_le_mul_of_nonneg_left (ca_even_le_exp_sqrt htr) (Real.exp_pos _).le
    _ = Real.exp (-a*r+2*Real.sqrt (t*r)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2*t/a+(-a/2)*r) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _

theorem integrableOn_liClockCriticalEvenKernel_decay
    {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
  IntegrableOn (fun r : ℝ => Real.exp (-a*r)*liClockCriticalEvenKernel (t*r))
    (Set.Ioi 0) := by
  have hb := (integrableOn_exp_mul_Ioi (a := -a/2) (by linarith) 0).const_mul
    (Real.exp (2*t/a))
  have hc : Continuous (fun r : ℝ => Real.exp (-a*r)*liClockCriticalEvenKernel (t*r)) :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-a*r))).mul
      (continuous_liClockCriticalEvenKernel.comp (by fun_prop))
  apply hb.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact ca_decay_majorant ha ht hr

private theorem ca_power_decay_integrable {a : ℝ} (ha : 0<a) (m : ℕ) :
    IntegrableOn (fun r : ℝ => r^m * Real.exp (-a*r)) (Set.Ioi 0) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hn : 0≤(m:ℝ) := by positivity
    linarith
  have h:=integrableOn_rpow_mul_exp_neg_mul_rpow
    (p:=1) (s:=(m:ℝ)) (b:=a) hm (by norm_num) ha
  simpa only [Real.rpow_one,Real.rpow_natCast] using h

private theorem ca_power_decay_integral {a : ℝ} (ha : 0<a) (m : ℕ) :
    (∫ r in Set.Ioi 0, r^m * Real.exp (-a*r)) = (m.factorial:ℝ)/a^(m+1) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hn : 0≤(m:ℝ) := by positivity
    linarith
  have hc : (m:ℝ)+1=((m+1:ℕ):ℝ) := by norm_num
  have h:=integral_rpow_mul_exp_neg_mul_rpow
    (p:=1) (q:=(m:ℝ)) (b:=a) (by norm_num) hm ha
  calc
    _=a^(-((m:ℝ)+1))*Real.Gamma ((m:ℝ)+1) := by
      simpa only [Real.rpow_one,Real.rpow_natCast,div_one,mul_one] using h
    _=(a^(m+1))⁻¹*(m.factorial:ℝ) := by
      rw [Real.rpow_neg ha.le,Real.Gamma_nat_eq_factorial,hc,Real.rpow_natCast]
    _=_ := by rw [div_eq_mul_inv]; ring

private theorem ca_decay_term_eq (a t : ℝ) (j : ℕ) (r : ℝ) :
    Real.exp (-a*r)*(t*r)^(2*j)/(((2*j).factorial : ℝ)^2) =
      (t^(2*j)/(((2*j).factorial : ℝ)^2))*(r^(2*j)*Real.exp (-a*r)) := by
  rw [mul_pow]
  ring

private theorem ca_decay_term_integrable {a : ℝ} (ha : 0<a) (t : ℝ) (j : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-a*r)*(t*r)^(2*j)/
      (((2*j).factorial : ℝ)^2)) (Set.Ioi 0) := by
  simp_rw [ca_decay_term_eq]
  exact (ca_power_decay_integrable ha (2*j)).const_mul _

private theorem ca_decay_term_integral {a : ℝ} (ha : 0<a) (t : ℝ) (j : ℕ) :
    (∫ r in Set.Ioi 0, Real.exp (-a*r)*(t*r)^(2*j)/
      (((2*j).factorial : ℝ)^2)) =
        (1/a)*((t/a)^(2*j)/((2*j).factorial : ℝ)) := by
  simp_rw [ca_decay_term_eq]
  rw [integral_const_mul, ca_power_decay_integral ha (2*j)]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hf : ((2*j).factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, show a^(2*j+1)=a^(2*j)*a by rw [pow_succ]]
  field_simp

theorem liClockCriticalEvenKernel_decay_integral
    {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
  (∫ r in Set.Ioi 0, Real.exp (-a*r)*liClockCriticalEvenKernel (t*r)) =
    (1/a)*Real.cosh (t/a) := by
  let f : ℕ → ℝ → ℝ := fun j r =>
    Real.exp (-a*r)*(t*r)^(2*j)/(((2*j).factorial : ℝ)^2)
  have hpos : ∀ j r, 0 ≤ f j r := by
    intro j r
    dsimp [f]
    rw [pow_mul]
    positivity
  have hs : ∀ r, HasSum (fun j => f j r)
      (Real.exp (-a*r)*liClockCriticalEvenKernel (t*r)) := by
    intro r
    apply ((ca_summable_even (t*r)).hasSum.mul_left (Real.exp (-a*r))).congr_fun
    intro j
    dsimp [f]
    ring
  have hb : Integrable (fun r => ∑' j, f j r) (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_liClockCriticalEvenKernel_decay ha ht).congr
      (Filter.Eventually.of_forall (fun r => (hs r).tsum_eq.symm))
  have he : HasSum (fun j => ∫ r in Set.Ioi 0, f j r)
      (∫ r in Set.Ioi 0, Real.exp (-a*r)*liClockCriticalEvenKernel (t*r)) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence f
    · intro j
      exact (ca_decay_term_integrable ha t j).aestronglyMeasurable
    · intro j
      filter_upwards [] with r
      exact le_of_eq (Real.norm_of_nonneg (hpos j r))
    · exact Filter.Eventually.of_forall (fun r => (hs r).summable)
    · exact hb
    · exact Filter.Eventually.of_forall hs
  have hv : HasSum (fun j => ∫ r in Set.Ioi 0, f j r) ((1/a)*Real.cosh (t/a)) := by
    apply ((Real.hasSum_cosh (t/a)).mul_left (1/a)).congr_fun
    intro j
    exact ca_decay_term_integral ha t j
  exact he.unique hv

end RHTower
end
