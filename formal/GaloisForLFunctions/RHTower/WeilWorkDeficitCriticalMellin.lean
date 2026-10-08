import GaloisForLFunctions.RHTower.WeilWorkDeficitProductKernelInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Critical-line recovery of the actual derivative product kernel

The beta integral bounds the critical Gamma factor by the sigma-four
factor at every real height. This gives absolute critical-line Mellin
integration for the actual finite Bessel kernel, including every natural
height moment. Mellin inversion then recovers the kernel at every positive
argument with continuity and convergence proved internally.

This is a classical analytic bridge. Uniform saddle asymptotics and the
spectral-deficit upper bound remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Complex
open GaloisForLFunctions.HTGeometry
open RHTower.WeilWorkDeficitPrimeKernel RHTower.WeilWorkDeficitMellin
open RHTower.WeilWorkDeficitGlobalAmplitude
namespace RHTower.WeilWorkDeficitCriticalMellin

private theorem beta_norm_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (y : ℝ) :
    ‖Complex.betaIntegral ((a:ℂ) + y*I) b‖ ≤
      (Complex.betaIntegral (a:ℂ) b).re := by
  have hf := Complex.betaIntegral_convergent (u := (a:ℂ)) (v := (b:ℂ))
    (by simpa using ha) (by simpa using hb)
  have he : (∫ x : ℝ in 0..1, ‖(x:ℂ)^((a:ℂ)+y*I-1) * (1-(x:ℂ))^((b:ℂ)-1)‖) =
      ∫ x : ℝ in 0..1, (((x:ℂ)^((a:ℂ)-1) * (1-(x:ℂ))^((b:ℂ)-1))).re := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have h1 : 0 < 1-x := sub_pos.mpr hx.2
    dsimp only
    rw [norm_mul, show (1:ℂ)-(x:ℂ) = ((1-x:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
      Complex.norm_cpow_eq_rpow_re_of_pos h1]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, one_re]
    rw [show (a:ℂ)-1 = ((a-1:ℝ):ℂ) by push_cast; rfl,
      show (b:ℂ)-1 = ((b-1:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hx.1.le, ← Complex.ofReal_cpow h1.le]
    simp
  calc
    _ ≤ ∫ x : ℝ in 0..1, ‖(x:ℂ)^((a:ℂ)+y*I-1) * (1-(x:ℂ))^((b:ℂ)-1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = _ := he.trans (Complex.reCLM.intervalIntegral_comp_comm hf)

private theorem gamma_norm_compare (y : ℝ) :
    ‖Complex.Gamma ((1/4:ℂ)+y*I)‖ ≤
      Real.Gamma (1/4) * ‖Complex.Gamma ((2:ℂ)+y*I)‖ := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (1/4:ℂ)+y*I) (t := (7/4:ℂ)) (by norm_num) (by norm_num)
  have hr := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (1/4:ℂ)) (t := (7/4:ℂ)) (by norm_num) (by norm_num)
  have hb := beta_norm_le (1/4) (7/4) (by norm_num) (by norm_num) y
  have hpos : 0 < Real.Gamma (7/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hpos' : 0 < Real.Gamma (1/4) := Real.Gamma_pos_of_pos (by norm_num)
  have hg1 : Complex.Gamma (1/4:ℂ) = (Real.Gamma (1/4):ℂ) := by
    convert Complex.Gamma_ofReal (1/4) using 1; norm_num
  have hg7 : Complex.Gamma (7/4:ℂ) = (Real.Gamma (7/4):ℂ) := by
    convert Complex.Gamma_ofReal (7/4) using 1; norm_num
  norm_num at hr
  have hb' : ‖Complex.betaIntegral ((1/4:ℂ)+y*I) (7/4)‖ ≤
      Real.Gamma (1/4) * Real.Gamma (7/4) := by
    convert hb using 1 <;> norm_num
    rw [← hr, hg1, hg7]
    simp
  have hab : (1/4:ℂ)+y*I+7/4 = 2+y*I := by ring
  rw [hab] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_mul] at hn
  have hg : ‖Complex.Gamma (7/4:ℂ)‖ = Real.Gamma (7/4) := by
    rw [hg7, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
  rw [hg] at hn
  have hm := mul_le_mul_of_nonneg_left hb' (norm_nonneg (Complex.Gamma ((2:ℂ)+y*I)))
  rw [← hn] at hm
  nlinarith

private theorem norm_mellin (k : ℕ) (σ t : ℝ) (hσ : 0 < σ) :
    ‖∫ x in Ioi (0:ℝ), (x:ℂ)^((σ+(t:ℂ)*I)-1)*(productKernel k x:ℂ)‖ =
      ((σ-1/2)^2+t^2)^k * (σ^2+t^2) * ((σ-1)^2+t^2) *
        Real.pi^(-σ) * ‖Complex.Gamma (((σ:ℂ)+t*I)/2)‖^2 / 4 := by
  have hs : 0 < ((σ:ℂ)+t*I).re := by simpa using hσ
  have hn (a : ℝ) : ‖(a:ℂ)+t*I‖^2 = a^2+t^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have h1 : (σ:ℂ)+t*I-1/2 = ((σ-1/2:ℝ):ℂ)+t*I := by push_cast; ring
  have h2 : (σ:ℂ)+t*I-1 = ((σ-1:ℝ):ℂ)+t*I := by push_cast; ring
  rw [productKernel_mellin k hs]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_ofNat, h1, h2]
  rw [pow_mul, hn, hn, hn, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp

/-- Literal critical-line Mellin transform of the derivative product kernel. -/
def criticalMellin (k : ℕ) (t : ℝ) : ℂ :=
  ∫ x in Ioi (0:ℝ), (x:ℂ)^((1/2+(t:ℂ)*I)-1)*(productKernel k x:ℂ)

private theorem critical_eq (k : ℕ) (t : ℝ) :
    criticalMellin k t = (-1:ℂ)^k * ((1/2:ℂ)+t*I-1/2)^(2*k) *
      ((1/2:ℂ)+t*I)^2 * ((1/2:ℂ)+t*I-1)^2 *
      (Real.pi:ℂ)^(-((1/2:ℂ)+t*I)) * Complex.Gamma (((1/2:ℂ)+t*I)/2)^2 / 4 :=
  productKernel_mellin k (by norm_num)

/-- All-height domination by the already-integrable sigma-four transform. -/
theorem norm_criticalMellin_le (k : ℕ) (t : ℝ) :
    ‖criticalMellin k t‖ ≤
      Real.pi^(7/2:ℝ) * Real.Gamma (1/4)^2 * ‖verticalMellin k t‖ := by
  have hcrit : ((1/2:ℂ)+t*I)/2 = 1/4+(t/2:ℝ)*I := by push_cast; ring
  have hfour : ((4:ℂ)+t*I)/2 = 2+(t/2:ℝ)*I := by push_cast; ring
  have hg := gamma_norm_compare (t/2)
  have hp : Real.pi^(-(1/2:ℝ)) = Real.pi^(7/2:ℝ)*Real.pi^(-4:ℝ) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    norm_num
  unfold criticalMellin verticalMellin
  have hn1 := norm_mellin k (1/2) t (by norm_num)
  have hn4 := norm_mellin k 4 t (by norm_num)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hn1 hn4
  rw [hn1, hn4]
  norm_num only [sub_self, zero_pow, zero_add]
  rw [hp, hcrit, hfour]
  calc
    _ ≤ (49/4+t^2)^k * (4^2+t^2) * ((4-1)^2+t^2) *
        (Real.pi^(7/2:ℝ)*Real.pi^(-4:ℝ)) *
        (Real.Gamma (1/4)*‖Complex.Gamma (2+(t/2:ℝ)*I)‖)^2 / 4 := by
      gcongr <;> first | exact hg | norm_num
    _ = _ := by ring

private theorem continuous_critical (k : ℕ) : Continuous (criticalMellin k) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hg : ContinuousAt (fun u : ℝ => Complex.Gamma (((1/2:ℂ)+u*I)/2)) t := by
    apply (Complex.continuousAt_Gamma _ _).comp
    · fun_prop
    · intro m h
      have hr := congrArg Complex.re h
      norm_num at hr
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hp : ContinuousAt (fun u : ℝ => (Real.pi:ℂ)^(-((1/2:ℂ)+u*I))) t :=
    (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp (by fun_prop)
  have he := funext (critical_eq k)
  rw [he]
  fun_prop

/-- Absolute integrability of the literal critical Mellin transform, at every order. -/
theorem integrable_criticalMellin (k : ℕ) : Integrable (criticalMellin k) := by
  exact ((integrable_verticalMellin k).norm.const_mul
    (Real.pi^(7/2:ℝ)*Real.Gamma (1/4)^2)).mono'
      (continuous_critical k).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_criticalMellin_le k))

/-- Raising derivative order is exactly multiplication by an even critical height power. -/
theorem criticalMellin_add (k m : ℕ) (t : ℝ) :
    criticalMellin (k+m) t = (t:ℂ)^(2*m)*criticalMellin k t := by
  rw [critical_eq, critical_eq]
  have he : (1/2:ℂ)+t*I-1/2 = t*I := by ring
  rw [he]
  simp only [mul_add, pow_add, mul_pow, pow_mul, Complex.I_sq]
  have hm : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; simp
  have hk : (-1:ℂ)^k*(-1)^k = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((t:ℂ)^2)^m * (((t:ℂ)^2)^k *
      (((1/2:ℂ)+t*I)^2 * ((1/2:ℂ)+t*I-1)^2 *
        (Real.pi:ℂ)^(-((1/2:ℂ)+t*I)) * Complex.Gamma (((1/2:ℂ)+t*I)/2)^2 / 4)) *
        ((-1:ℂ)^m*(-1)^m) * ((-1:ℂ)^k*(-1)^k) := by ring
    _ = _ := by rw [hm, hk]; linear_combination -(((t:ℂ)^2)^m * (((t:ℂ)^2)^k *
      (((1/2:ℂ)+t*I)^2 * ((1/2:ℂ)+t*I-1)^2 *
        (Real.pi:ℂ)^(-((1/2:ℂ)+t*I)) * Complex.Gamma (((1/2:ℂ)+t*I)/2)^2 / 4))) * hk

/-- Every even height moment of the actual transform is absolutely integrable. -/
theorem integrable_even_height (k m : ℕ) :
    Integrable (fun t : ℝ => (t:ℂ)^(2*m)*criticalMellin k t) := by
  simpa only [← criticalMellin_add] using integrable_criticalMellin (k+m)

/-- Every natural height moment of the actual transform is absolutely integrable. -/
theorem integrable_height (k m : ℕ) :
    Integrable (fun t : ℝ => (t:ℂ)^m*criticalMellin k t) := by
  have hc : Continuous (fun t : ℝ => (t:ℂ)^m*criticalMellin k t) :=
    (by fun_prop : Continuous (fun t : ℝ => (t:ℂ)^m)).mul (continuous_critical k)
  apply ((integrable_criticalMellin k).norm.add (integrable_even_height k m).norm).mono'
    hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.add_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h : |t|^m ≤ 1+|t|^(2*m) := by
    rw [mul_comm 2 m, pow_mul]
    nlinarith [sq_nonneg (|t|^m-1)]
  nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (criticalMellin k t))]

/-- Absolute critical inverse integration, including every natural height moment. -/
theorem integrable_critical_inverse_height (k m : ℕ) (x : Ioi (0:ℝ)) :
    Integrable (fun t : ℝ =>
      (x:ℂ)^(-((1/2:ℂ)+(t:ℂ)*I))*((t:ℂ)^m*criticalMellin k t)) := by
  have hc : Continuous (fun t : ℝ => (x:ℂ)^(-((1/2:ℂ)+(t:ℂ)*I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_const_cpow (by exact_mod_cast x.property.ne')).comp (by fun_prop)
  apply ((integrable_height k m).norm.const_mul ((x:ℝ)^(-(1/2:ℝ)))).mono'
  · exact hc.aestronglyMeasurable.mul (integrable_height k m).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos x.property]
    norm_num

private theorem continuous_bessel {x : ℝ} (hx : 0 < x) (nu : ℝ) :
    ContinuousAt (fun y : ℝ => realModifiedBesselKOrder y nu) x := by
  have hc := (d4BM_hasDerivAt_modifiedBesselKOrder_argument hx (nu:ℂ)).continuousAt
  apply (Complex.continuous_re.continuousAt.comp hc).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  dsimp only [Function.comp_apply]
  rw [modifiedBesselKOrder_ofReal hy]
  rfl

private theorem continuous_kernel (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y : ℝ => (productKernel k y:ℂ)) x := by
  have hb (j l : ℕ) : ContinuousAt (fun y : ℝ =>
      realModifiedBesselKOrder (2*Real.pi*y) ((j:ℝ)-l)) x :=
    (continuous_bessel (by positivity) _).comp (by fun_prop)
  unfold productKernel
  fun_prop

private theorem mellin_convergent (k : ℕ) :
    MellinConvergent (fun x : ℝ => (productKernel k x:ℂ)) ((1/2:ℝ):ℂ) := by
  have h := productKernel_mellin_integrable k (s := (1/2:ℂ)) (by norm_num)
  simpa only [MellinConvergent, smul_eq_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using! h

private theorem vertical_integrable (k : ℕ) :
    VerticalIntegrable (mellin (fun x : ℝ => (productKernel k x:ℂ))) (1/2) := by
  simpa only [VerticalIntegrable, mellin, criticalMellin, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using!
      integrable_criticalMellin k

/-- Critical inverse Mellin recovery of the actual kernel, with all analytic gates paid. -/
theorem productKernel_critical_inversion (k : ℕ) (x : Ioi (0:ℝ)) :
    (1/(2*Real.pi):ℝ) •
      (∫ t : ℝ, (x:ℂ)^(-((1/2:ℂ)+(t:ℂ)*I))*criticalMellin k t) =
        (productKernel k x:ℂ) := by
  have h := mellinInv_mellin_eq (1/2) (fun y : ℝ => (productKernel k y:ℂ)) x.property
    (mellin_convergent k) (vertical_integrable k) (continuous_kernel k x.property)
  simpa only [mellinInv, mellin, smul_eq_mul, criticalMellin,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

end RHTower.WeilWorkDeficitCriticalMellin
