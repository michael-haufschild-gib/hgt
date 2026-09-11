import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSourceEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusFrullaniCurrent
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Literal Gamma/Möbius endpoint subtraction

For Re(z)>3/2 the full source correction M_z-C_z Q has an admitted Mellin integral
at s=-1/2, equal to the derivative of C_z=1/zeta(z-1/2). The complete Frullani
kernel supplies the logarithmic norm-integral majorant. For Re(z)>5/2 the first
normalized remainder tends to C_z-C_(z-1). Its retained integral has first-prime
asymptotic log(2) after scaling, hence eventually positive real part.

These are literal integral statements. They do not evaluate a totalized singular
Gamma product, assert a larger complete Mellin domain, or force spectral balance.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private abbrev muCoeff : ℕ → ℂ := fun m => ((moebius m : ℤ):ℂ)

def pwGammaMobiusEndpointSubtraction (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusTilt z x - (riemannZeta (z-1/2))⁻¹ * pwGammaRaySource x

def pwGammaMobiusEndpointRemainder (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusEndpointSubtraction z x / ((x:ℂ)*(Real.sqrt x:ℂ))

theorem pwGammaFrullaniKernel_norm_le {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    ‖pwGammaFrullaniKernel n x‖ ≤ (n:ℝ) := by
  rw [pwGammaFrullaniKernel_norm_eq hn hx, pwGammaFrullaniKernel_eq_real, Complex.ofReal_re,
    ← neg_div, neg_sub]
  apply (div_le_iff₀ hx).mpr
  have h1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
  have h2 := Real.add_one_le_exp (-((n:ℝ)*x))
  linarith

theorem pwGammaFrullaniKernel_tendsto_zero (n : ℕ) :
    Tendsto (pwGammaFrullaniKernel n) (𝓝[>] (0:ℝ)) (𝓝 ((1:ℂ)-n)) := by
  have hd := (GaloisForLFunctions.HTGeometry.hasDerivAt_cexp_neg_mul (n:ℂ) 0).sub
    (GaloisForLFunctions.HTGeometry.hasDerivAt_cexp_neg_mul 1 0)
  change Tendsto (fun x : ℝ =>
    (Complex.exp (-((n:ℂ)*(x:ℂ)))-Complex.exp (-(x:ℂ)))/(x:ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 ((1:ℂ)-n))
  simpa [div_eq_mul_inv, Complex.real_smul, mul_comm, sub_eq_add_neg, add_comm, mul_add] using
    hd.tendsto_slope_zero_right


theorem pwGammaMobiusEndpointTerm_mul_nat (z : ℂ) (n : ℕ) :
    LSeries.term muCoeff (z-1/2) n * (n:ℂ) = LSeries.term muCoeff (z-3/2) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [LSeries.term_def₀ (by simp [muCoeff]), LSeries.term_def₀ (by simp [muCoeff]),
    show -(z-3/2) = -(z-1/2)+1 by ring, Complex.cpow_add _ _ hnc, Complex.cpow_one]
  ring

theorem pwGammaMobiusEndpoint_firstMoment_summable {z : ℂ} (hz : (5/2:ℝ) < z.re) :
    Summable (fun n => ‖LSeries.term muCoeff (z-1/2) n‖*(n:ℝ)) := by
  have hs : LSeriesSummable muCoeff (z-3/2) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by
      simp only [Complex.sub_re, Complex.div_ofNat_re]
      change 1 < z.re - 3/2
      linarith)
  apply hs.norm.congr
  intro n
  rw [← pwGammaMobiusEndpointTerm_mul_nat z n, norm_mul, Complex.norm_natCast]

theorem pwGammaMobiusEndpoint_damped_summable {z : ℂ} (hz : (3/2:ℝ) < z.re)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n => LSeries.term muCoeff (z-1/2) n * (Real.exp (-((n:ℝ)*x)):ℂ)) := by
  have hs : LSeriesSummable muCoeff (z-1/2) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      linarith)
  apply Summable.of_norm
  refine hs.norm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg n) hx.le)))

theorem pwGammaMobiusEndpointRemainder_eq_tsum {z : ℂ} (hz : (3/2:ℝ) < z.re)
    {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusEndpointRemainder z x =
      ∑' n, LSeries.term muCoeff (z-1/2) n * pwGammaFrullaniKernel n x := by
  have hzeta : 1 < (z-(1:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  have hs := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hzeta
  have he : pwGammaMobiusEndpointRemainder z x =
      (pwGammaMobiusNormalizedSource z x - (riemannZeta (z-1/2))⁻¹ *
        (Real.exp (-x):ℂ))/(x:ℂ) := by
    rw [pwGammaMobiusEndpointRemainder, pwGammaMobiusEndpointSubtraction,
      pwGammaMobiusNormalizedSource, pwGammaRaySource_eq hx]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx.ne',
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne']
  rw [he, pwGammaMobiusNormalizedSource_eq_tsum z hx, riemannZeta_inv_eq_tsum_term hzeta,
    ← tsum_mul_right, ← (pwGammaMobiusEndpoint_damped_summable hz hx).tsum_sub
      (hs.mul_right (Real.exp (-x):ℂ)), ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [pwGammaFrullaniKernel_eq_real]
  push_cast
  ring

theorem pwGammaMobiusEndpointRemainder_tendsto {z : ℂ} (hz : (5/2:ℝ) < z.re) :
    Tendsto (pwGammaMobiusEndpointRemainder z) (𝓝[>] (0:ℝ))
      (𝓝 ((riemannZeta (z-1/2))⁻¹-(riemannZeta (z-3/2))⁻¹)) := by
  have hz1 : (3/2:ℝ) < z.re := by linarith
  have hza : 1 < (z-(1:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  have hzb : 1 < (z-(3:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re]
    change 1 < z.re - 3/2
    linarith
  have ha := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hza
  have hb := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hzb
  have ht := tendsto_tsum_of_dominated_convergence (pwGammaMobiusEndpoint_firstMoment_summable hz)
    (fun n => (pwGammaFrullaniKernel_tendsto_zero n).const_mul (LSeries.term muCoeff (z-1/2) n))
    (show ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), ∀ n,
      ‖LSeries.term muCoeff (z-1/2) n * pwGammaFrullaniKernel n x‖ ≤
        ‖LSeries.term muCoeff (z-1/2) n‖*(n:ℝ) from by
      filter_upwards [self_mem_nhdsWithin] with x hx n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (pwGammaFrullaniKernel_norm_le hn hx) (norm_nonneg _))
  have he : (∑' n, LSeries.term muCoeff (z-1/2) n * ((1:ℂ)-n)) =
      (riemannZeta (z-1/2))⁻¹-(riemannZeta (z-3/2))⁻¹ := by
    calc
      _ = ∑' n, (LSeries.term muCoeff (z-1/2) n - LSeries.term muCoeff (z-3/2) n) := by
        apply tsum_congr
        intro n
        rw [← pwGammaMobiusEndpointTerm_mul_nat z n]
        ring
      _ = _ := by rw [ha.tsum_sub hb, ← riemannZeta_inv_eq_tsum_term hza,
        ← riemannZeta_inv_eq_tsum_term hzb]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (pwGammaMobiusEndpointRemainder_eq_tsum hz1 hx).symm

def pwGammaMobiusEndpointFrullaniAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  LSeries.term muCoeff (z-1/2) n * pwGammaFrullaniKernel n x

private theorem endpoint_logTerm (z : ℂ) (n : ℕ) :
    LSeries.term muCoeff (z-1/2) n * (Real.log (n:ℝ):ℂ) =
      LSeries.term (LSeries.logMul muCoeff) (z-1/2) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', LSeries.logMul,
    ← Complex.natCast_log]
  ring

private theorem endpoint_logAbscissa {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    LSeries.abscissaOfAbsConv muCoeff < (z-(1:ℂ)/2).re := by
  rw [ArithmeticFunction.abscissaOfAbsConv_moebius]
  have hza : 1 < (z-(1:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  exact_mod_cast hza

theorem pwGammaMobiusEndpointFrullaniAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusEndpointFrullaniAtom z n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change IntegrableOn (fun x : ℝ => LSeries.term muCoeff (z-1/2) 0 * pwGammaFrullaniKernel 0 x) (Ioi 0)
    simp only [LSeries.term_zero, zero_mul]
    exact integrable_zero _ _ _
  exact (pwGammaFrullaniKernel_integrable hn).const_mul _

theorem pwGammaMobiusEndpointFrullaniAtom_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointFrullaniAtom z n x) =
      -(LSeries.term (LSeries.logMul muCoeff) (z-1/2) n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusEndpointFrullaniAtom]
  change (∫ x in Ioi (0:ℝ), LSeries.term muCoeff (z-1/2) n * pwGammaFrullaniKernel n x) = _
  rw [integral_const_mul, pwGammaFrullaniKernel_integral hn, mul_neg, endpoint_logTerm]

theorem pwGammaMobiusEndpointFrullaniAtom_norm_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0:ℝ), ‖pwGammaMobiusEndpointFrullaniAtom z n x‖) =
      ‖LSeries.term (LSeries.logMul muCoeff) (z-1/2) n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusEndpointFrullaniAtom]
  simp only [pwGammaMobiusEndpointFrullaniAtom, norm_mul, integral_const_mul,
    pwGammaFrullaniKernel_norm_integral hn]
  rw [← endpoint_logTerm z n, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n)]

theorem pwGammaMobiusEndpointFrullaniAtom_norm_integrals_summable {z : ℂ}
    (hz : (3/2:ℝ) < z.re) :
    Summable (fun n => ∫ x in Ioi (0:ℝ), ‖pwGammaMobiusEndpointFrullaniAtom z n x‖) := by
  simpa only [pwGammaMobiusEndpointFrullaniAtom_norm_integral] using
    (LSeriesSummable_logMul_of_lt_re (endpoint_logAbscissa hz)).norm

theorem pwGammaMobiusEndpointRemainder_integrable {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    IntegrableOn (pwGammaMobiusEndpointRemainder z) (Ioi 0) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusEndpointFrullaniAtom_integrable z)
    (pwGammaMobiusEndpointFrullaniAtom_norm_integrals_summable hz)
  exact IntegrableOn.congr_fun hs (fun x hx => (pwGammaMobiusEndpointRemainder_eq_tsum hz hx).symm)
    measurableSet_Ioi

theorem pwGammaMobiusEndpointRemainder_integral {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointRemainder z x) =
      -LSeries (LSeries.logMul muCoeff) (z-1/2) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusEndpointRemainder_eq_tsum hz hx)]
  change (∫ x in Ioi (0:ℝ), ∑' n, pwGammaMobiusEndpointFrullaniAtom z n x) = _
  rw [← integral_tsum_of_summable_integral_norm
    (pwGammaMobiusEndpointFrullaniAtom_integrable z)
    (pwGammaMobiusEndpointFrullaniAtom_norm_integrals_summable hz)]
  simp only [pwGammaMobiusEndpointFrullaniAtom_integral, tsum_neg, LSeries]

theorem pwGammaMobiusEndpointCoefficient_hasDerivAt {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    HasDerivAt (fun w : ℂ => (riemannZeta (w-1/2))⁻¹)
      (-LSeries (LSeries.logMul muCoeff) (z-1/2)) z := by
  have hd := (LSeries_hasDerivAt (endpoint_logAbscissa hz)).comp z
    ((hasDerivAt_id z).sub_const ((1:ℂ)/2))
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  have hr : ∀ᶠ w : ℂ in 𝓝 z, (3/2:ℝ) < w.re :=
    (Complex.continuous_re.tendsto z).eventually_const_lt hz
  filter_upwards [hr] with w hw
  have hwa : 1 < (w-(1:ℂ)/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  exact riemannZeta_inv_eq_tsum_term hwa

theorem pwGammaMobiusEndpointRemainder_integral_eq_deriv {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointRemainder z x) =
      deriv (fun w : ℂ => (riemannZeta (w-1/2))⁻¹) z := by
  rw [pwGammaMobiusEndpointRemainder_integral hz, (pwGammaMobiusEndpointCoefficient_hasDerivAt hz).deriv]

theorem pwGammaMobiusEndpointSubtraction_pole_integrand (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(-(1:ℂ)/2-1)*pwGammaMobiusEndpointSubtraction z x =
      pwGammaMobiusEndpointRemainder z x := by
  have hxc : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hq : (Real.sqrt x:ℂ) = (x:ℂ)^((1:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
    push_cast
    rfl
  have hp : (x:ℂ)*(Real.sqrt x:ℂ) = (x:ℂ)^((3:ℂ)/2) := by
    rw [hq, show (3:ℂ)/2 = 1+1/2 by ring, Complex.cpow_add _ _ hxc, Complex.cpow_one]
  rw [pwGammaMobiusEndpointRemainder, hp, show -(1:ℂ)/2-1 = -(3/2) by ring, Complex.cpow_neg]
  simp only [div_eq_mul_inv]
  ring

theorem pwGammaMobiusEndpointSubtraction_pole_mellinConvergent {z : ℂ}
    (hz : (3/2:ℝ) < z.re) :
    MellinConvergent (pwGammaMobiusEndpointSubtraction z) (-(1:ℂ)/2) := by
  exact IntegrableOn.congr_fun (pwGammaMobiusEndpointRemainder_integrable hz)
    (fun x hx => (pwGammaMobiusEndpointSubtraction_pole_integrand z hx).symm) measurableSet_Ioi

theorem pwGammaMobiusEndpointSubtraction_pole_mellin {z : ℂ} (hz : (3/2:ℝ) < z.re) :
    mellin (pwGammaMobiusEndpointSubtraction z) (-(1:ℂ)/2) =
      deriv (fun w : ℂ => (riemannZeta (w-1/2))⁻¹) z := by
  simp only [mellin, smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pwGammaMobiusEndpointSubtraction_pole_integrand z hx),
    pwGammaMobiusEndpointRemainder_integral_eq_deriv hz]

theorem pwGammaMobiusEndpointRemainder_integral_leading :
    Tendsto (fun r : ℝ => (2:ℂ)^(r:ℂ) *
      (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointRemainder ((r:ℂ)+1/2) x))
      atTop (𝓝 (Real.log 2:ℂ)) := by
  have hf : ∀ m ≤ 1, LSeries.logMul muCoeff m = 0 := by
    intro m hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;>
      simp [LSeries.logMul, muCoeff]
  have ha : LSeries.abscissaOfAbsConv (LSeries.logMul muCoeff) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul, ArithmeticFunction.abscissaOfAbsConv_moebius]
    exact EReal.coe_lt_top (1:ℝ)
  have hf2 : LSeries.logMul muCoeff 2 = -(Real.log 2:ℂ) := by
    simp [LSeries.logMul, muCoeff, moebius_apply_prime Nat.prime_two]
  have ht := (LSeries.tendsto_cpow_mul_atTop hf ha).neg
  simp only [hf2, neg_neg] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with r hr
  have hz : (3/2:ℝ) < ((r:ℂ)+(1:ℂ)/2).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  rw [pwGammaMobiusEndpointRemainder_integral hz, add_sub_cancel_right, mul_neg]
  congr 2
  ring

theorem pwGammaMobiusEndpointRemainder_integral_eventually_pos :
    ∀ᶠ r : ℝ in atTop,
      0 < (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointRemainder ((r:ℂ)+1/2) x).re := by
  have ht := (Complex.continuous_re.tendsto (Real.log 2:ℂ)).comp
    pwGammaMobiusEndpointRemainder_integral_leading
  have hlog : (0:ℝ) < (Real.log 2:ℂ).re := by
    exact Real.log_pos one_lt_two
  have hh := ht.eventually_const_lt hlog
  filter_upwards [hh] with r hr
  change 0 < ((2:ℂ)^(r:ℂ) *
    (∫ x in Ioi (0:ℝ), pwGammaMobiusEndpointRemainder ((r:ℂ)+1/2) x)).re at hr
  have hp : (2:ℂ)^(r:ℂ) = (((2:ℝ)^r:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_cpow (y := r) (by positivity : (0:ℝ) ≤ 2)).symm
  rw [hp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos two_pos r)).mp hr


end
end RHTower
