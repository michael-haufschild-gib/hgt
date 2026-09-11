import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusFrullaniJointAdmission

/-!
# Actual reflected Frullani generator and all-parameter global admission

Source-fixed inverse-gain reflection turns weighted additive translation into
weighted reciprocal motion. Its actual reflected arithmetic family, complete
coefficient current and two-variable Frullani response are globally integrable
at every complex coefficient parameter. Explicit polynomial Gamma moments bound
all reflected atom norm series. Source fixation and this complete global domain
do not make the current vanish or identify a Xi spectral parameter.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- Existing source-fixed inverse-gain reflection in the original ray coordinate. -/
def pwGammaRayInverseReflection (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (pwGammaRaySource x / pwGammaRaySource x⁻¹)*f x⁻¹

theorem pwGammaRayInverseReflection_eq_gain (f : ℝ → ℂ) (x : ℝ) :
    pwGammaRayInverseReflection f x =
      (pwLogSingularGain (Real.log x) : ℂ)⁻¹*f x⁻¹ := by
  have hq := pwGammaSource_gain_transport (Real.log x)
  have heq : pwGammaRaySource x⁻¹ =
      (pwLogSingularGain (Real.log x) : ℂ)*pwGammaRaySource x := by
    simpa only [pwGammaRaySource, Real.log_inv] using hq.symm
  rw [pwGammaRayInverseReflection, heq]
  field_simp [pwGammaRaySource_ne_zero x]

theorem pwGammaRayInverseReflection_log_transport (f : ℝ → ℂ) (t : ℝ) :
    pwGammaRayInverseReflection f (Real.exp t) =
      pwLogInverseGainReflection (fun u => f (Real.exp u)) t := by
  rw [pwGammaRayInverseReflection_eq_gain, Real.log_exp, pwLogInverseGainReflection,
    Real.exp_neg]

theorem pwGammaRayInverseReflection_involutive :
    Function.Involutive pwGammaRayInverseReflection := by
  intro f
  funext x
  simp only [pwGammaRayInverseReflection, inv_inv]
  field_simp [pwGammaRaySource_ne_zero x, pwGammaRaySource_ne_zero x⁻¹]

theorem pwGammaRayInverseReflection_source_fixed :
    pwGammaRayInverseReflection pwGammaRaySource = pwGammaRaySource := by
  funext x
  exact div_mul_cancel₀ _ (pwGammaRaySource_ne_zero x⁻¹)

theorem pwGammaWeightedTranslation_source_ratio (f : ℝ → ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaWeightedTranslation h f x =
      (Real.exp (-h) : ℂ)*pwGammaRaySource x*(f (x+h)/pwGammaRaySource (x+h)) := by
  have hq := pwGammaWeightedTranslation_ray_atom (n := 1) zero_lt_one hh hx
  simp only [Nat.cast_one, one_mul] at hq
  change (((Real.sqrt x/Real.sqrt (x+h) : ℝ) : ℂ)*pwGammaRaySource (x+h)) = _ at hq
  rw [← hq, pwGammaWeightedTranslation]
  field_simp [pwGammaRaySource_ne_zero (x+h)]

/-- Reflected translation, defined by the already identified inverse-gain conjugation. -/
def pwGammaReflectedTranslation (h : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  pwGammaRayInverseReflection (pwGammaWeightedTranslation h (pwGammaRayInverseReflection f))

theorem pwGammaReflectedTranslation_eq (f : ℝ → ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaReflectedTranslation h f x =
      (Real.exp (-h) : ℂ)*pwGammaRaySource x*
        (f (x/(1+h*x))/pwGammaRaySource (x/(1+h*x))) := by
  have hi : 0 < x⁻¹ := inv_pos.mpr hx
  have hm : (x⁻¹+h)⁻¹ = x/(1+h*x) := by field_simp
  change (pwGammaRaySource x/pwGammaRaySource x⁻¹)*
    pwGammaWeightedTranslation h (pwGammaRayInverseReflection f) x⁻¹ = _
  rw [pwGammaWeightedTranslation_source_ratio _ hh hi, pwGammaRayInverseReflection, hm]
  field_simp [pwGammaRaySource_ne_zero]

theorem pwGammaReflectedTranslation_on_reflected (f : ℝ → ℂ) (h x : ℝ) :
    pwGammaReflectedTranslation h (pwGammaRayInverseReflection f) x =
      pwGammaRayInverseReflection (pwGammaWeightedTranslation h f) x := by
  rw [pwGammaReflectedTranslation, pwGammaRayInverseReflection_involutive f]

/-- Complete response of the literal reflected arithmetic family under the reflected translation. -/
def pwGammaMobiusReflectedFrullaniResponse (z : ℂ) (x h : ℝ) : ℂ :=
  (pwGammaReflectedTranslation h (pwGammaRayInverseReflection (pwGammaMobiusTilt z)) x-
    (Real.exp (-h) : ℂ)*pwGammaRayInverseReflection (pwGammaMobiusTilt z) x)/(h : ℂ)

theorem pwGammaMobiusReflectedFrullaniResponse_eq (z : ℂ) (x h : ℝ) :
    pwGammaMobiusReflectedFrullaniResponse z x h =
      (pwGammaRaySource x/pwGammaRaySource x⁻¹)*pwGammaMobiusFrullaniResponse z x⁻¹ h := by
  rw [pwGammaMobiusReflectedFrullaniResponse, pwGammaReflectedTranslation_on_reflected]
  simp only [pwGammaRayInverseReflection, pwGammaMobiusFrullaniResponse]
  ring

theorem pwGammaMobiusReflectedFrullaniResponse_integrable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (pwGammaMobiusReflectedFrullaniResponse z x) (Ioi 0) := by
  have hi := (pwGammaMobiusFrullaniResponse_integrable z (inv_pos.mpr hx)).const_mul
    (pwGammaRaySource x/pwGammaRaySource x⁻¹)
  exact hi.congr (Filter.Eventually.of_forall (fun h => (pwGammaMobiusReflectedFrullaniResponse_eq z x h).symm))

theorem pwGammaMobiusReflectedFrullaniResponse_integral (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusReflectedFrullaniResponse z x h) =
      pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x := by
  simp only [pwGammaMobiusReflectedFrullaniResponse_eq, integral_const_mul,
    pwGammaMobiusFrullaniResponse_integral z (inv_pos.mpr hx), pwGammaRayInverseReflection]

theorem pwGammaRayInverseReflection_ray_atom {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    pwGammaRayInverseReflection (fun y => pwGammaRaySource ((n : ℝ)*y)) x =
      ((Real.sqrt (n : ℝ)*Real.exp (-(((n : ℝ)-1)/x)) : ℝ) : ℂ)*pwGammaRaySource x := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := inv_pos.mpr hx
  rw [pwGammaRayInverseReflection, pwGammaRaySource_eq (mul_pos hnr hi),
    pwGammaRaySource_eq hi, Real.sqrt_mul hnr.le]
  have hs : (Real.sqrt x⁻¹ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hi).ne'
  have he : Real.exp (-((n : ℝ)*x⁻¹)) =
      Real.exp (-(x⁻¹))*Real.exp (-(((n : ℝ)-1)/x)) := by
    rw [← Real.exp_add]
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [he]
  push_cast
  have hs' : (Real.sqrt (1/x) : ℂ) ≠ 0 := by simpa only [one_div] using hs
  field_simp [hs, hs', Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-(x⁻¹)))]

/-- Actual reflected arithmetic atom; its parameter and every coefficient are retained. -/
def pwGammaMobiusReflectedAtom (z : ℂ) (n : ℕ) : ℝ → ℂ :=
  pwGammaRayInverseReflection (pwGammaMobiusGlobalAtom z n)

theorem pwGammaMobiusReflectedAtom_eq (z : ℂ) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    pwGammaMobiusReflectedAtom z n x =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        (((Real.sqrt (n : ℝ)*Real.exp (-(((n : ℝ)-1)/x)) : ℝ) : ℂ)*pwGammaRaySource x) := by
  have hh := pwGammaRayInverseReflection_ray_atom hn hx
  simp only [pwGammaRayInverseReflection] at hh
  simp only [pwGammaMobiusReflectedAtom, pwGammaRayInverseReflection, pwGammaMobiusGlobalAtom]
  calc
    _ = (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))*
        ((pwGammaRaySource x/pwGammaRaySource x⁻¹)*pwGammaRaySource ((n : ℝ)*x⁻¹)) := by ring
    _ = _ := by rw [hh]

theorem pwGammaMobiusReflectedAtom_zero (z : ℂ) : pwGammaMobiusReflectedAtom z 0 = 0 := by
  funext x
  simp [pwGammaMobiusReflectedAtom, pwGammaRayInverseReflection, pwGammaMobiusGlobalAtom]

theorem pwGammaMobiusReflectedAtom_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => pwGammaMobiusReflectedAtom z n x) :=
  (pwGammaMobiusTilt_summable z (inv_pos.mpr hx)).mul_left _

theorem pwGammaMobiusTilt_reflection_eq_tsum (z : ℂ) (x : ℝ) :
    pwGammaRayInverseReflection (pwGammaMobiusTilt z) x = ∑' n, pwGammaMobiusReflectedAtom z n x := by
  simp only [pwGammaRayInverseReflection, pwGammaMobiusTilt_eq_global_atoms,
    pwGammaMobiusReflectedAtom, tsum_mul_left]

private theorem pwGammaReflected_exp_neg_le (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ (k.factorial : ℝ)/y^k := by
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hh := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hy k)).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hh)

private theorem pwGammaReflected_moment_eq (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x^k*‖pwGammaRaySource x‖ = Real.exp (-x)*x^(((k : ℝ)+3/2)-1) := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.sqrt_eq_rpow]
  calc
    _ = Real.exp (-x)*(x^(k : ℝ)*x^(1/2 : ℝ)) := by rw [Real.rpow_natCast]; ring
    _ = _ := by rw [← Real.rpow_add hx]; congr 2; ring

theorem pwGammaRaySource_integrable_polynomial_moment (k : ℕ) :
    IntegrableOn (fun x : ℝ => x^k*‖pwGammaRaySource x‖) (Ioi 0) :=
  IntegrableOn.congr_fun (Real.GammaIntegral_convergent (s := (k : ℝ)+3/2) (by positivity))
    (fun x hx => (pwGammaReflected_moment_eq k hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_polynomial_moment_integral (k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^k*‖pwGammaRaySource x‖) = Real.Gamma ((k : ℝ)+3/2) := by
  rw [Real.Gamma_eq_integral (by positivity : 0 < (k : ℝ)+3/2)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaReflected_moment_eq k hx)

private theorem pwGammaReflected_coefficient_bound {N n : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (hn : 0 < n) :
    ‖Complex.exp (-z*(Real.log (n : ℝ) : ℂ))‖ ≤ (n : ℝ)^N := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hre : -z.re ≤ (N : ℝ) :=
    (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp ((N : ℝ)*Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (Real.log_nonneg hn1))
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hnr]

/-- Uniform polynomially weighted atom bound; the reciprocal exponential retains the full tail. -/
theorem pwGammaMobiusReflectedAtom_polynomial_bound {N : ℕ} {z : ℂ}
    (hz : ‖z‖ ≤ (N : ℝ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ((n+2 : ℕ) : ℝ)^k*‖pwGammaMobiusReflectedAtom z (n+2) x‖ ≤
      (2^(N+k+1)*((N+k+3).factorial : ℝ))*(1/((n : ℝ)+1)^2)*
        (x^(N+k+3)*‖pwGammaRaySource x‖) := by
  have hn : 0 < n+2 := by omega
  have hn1 : (1 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+2 by omega)
  have hm : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hmu : ‖((moebius (n+2) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |moebius (n+2)| ≤ 1 from abs_moebius_le_one)
  have hc := pwGammaReflected_coefficient_bound hz hn
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  have he := pwGammaReflected_exp_neg_le (N+k+3) (div_pos hm hx)
  rw [pwGammaMobiusReflectedAtom_eq z hn hx]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity :
    0 ≤ Real.sqrt (((n+2 : ℕ) : ℝ))*Real.exp (-(((((n+2 : ℕ) : ℝ))-1)/x)))]
  calc
    _ ≤ ((n+2 : ℕ) : ℝ)^k * ((1*((n+2 : ℕ) : ℝ)^N)*
        (((((n+2 : ℕ) : ℝ))*Real.exp (-(((((n+2 : ℕ) : ℝ))-1)/x)))*‖pwGammaRaySource x‖)) := by
      gcongr
    _ = (((n : ℝ)+2)^(N+k+1)*Real.exp (-(((n : ℝ)+1)/x)))*‖pwGammaRaySource x‖ := by
      push_cast
      rw [pow_add, pow_add, pow_one]
      ring
    _ ≤ ((2*((n : ℝ)+1))^(N+k+1)*(((N+k+3).factorial : ℝ)/(((n : ℝ)+1)/x)^(N+k+3)))*
        ‖pwGammaRaySource x‖ := by
      gcongr
      · linarith
    _ = _ := by
      rw [mul_pow, div_pow, show N+k+3 = (N+k+1)+2 by omega, pow_add]
      field_simp
      ring

private theorem pwGammaMobiusReflectedAtom_measurable (z : ℂ) (n : ℕ) :
    Measurable (pwGammaMobiusReflectedAtom z n) := by
  unfold pwGammaMobiusReflectedAtom pwGammaRayInverseReflection pwGammaMobiusGlobalAtom
    pwGammaRaySource GaloisForLFunctions.expShift
  fun_prop

theorem pwGammaMobiusReflectedAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusReflectedAtom z n) (Ioi 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  rcases n with _ | n
  · rw [pwGammaMobiusReflectedAtom_zero]; exact integrable_zero _ _ _
  rcases n with _ | n
  · have heq : pwGammaMobiusReflectedAtom z 1 = pwGammaRaySource := by
      funext x
      simp [pwGammaMobiusReflectedAtom, pwGammaMobiusGlobalAtom,
        pwGammaRayInverseReflection, pwGammaRaySource_ne_zero]
    rw [heq]
    exact pwGammaRaySource_integrable
  have hg := (pwGammaRaySource_integrable_polynomial_moment (N+0+3)).const_mul
    ((2^(N+0+1)*((N+0+3).factorial : ℝ))*(1/((n : ℝ)+1)^2))
  apply Integrable.mono' hg (pwGammaMobiusReflectedAtom_measurable z (n+2)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [pow_zero, one_mul] using pwGammaMobiusReflectedAtom_polynomial_bound hN 0 n hx

theorem pwGammaMobiusReflectedAtom_polynomial_norm_integrals_summable (z : ℂ) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^k*(∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedAtom z n x‖)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  have hsq : Summable (fun n : ℕ => 1/((n : ℝ)+1)^2) := by
    have ht := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
    change Summable (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)^2) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have htail : Summable (fun n : ℕ => ((n+2 : ℕ) : ℝ)^k*
      (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedAtom z (n+2) x‖)) := by
    have hs := hsq.mul_left ((2^(N+k+1)*((N+k+3).factorial : ℝ))*Real.Gamma (((N+k+3 : ℕ) : ℝ)+3/2))
    refine hs.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (integral_nonneg (fun x => norm_nonneg _))) ?_
    intro n
    rw [← integral_const_mul]
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ),
          (2^(N+k+1)*((N+k+3).factorial : ℝ))*(1/((n : ℝ)+1)^2)*
            (x^(N+k+3)*‖pwGammaRaySource x‖) := by
        apply integral_mono_ae ((pwGammaMobiusReflectedAtom_integrable z (n+2)).norm.const_mul _)
          ((pwGammaRaySource_integrable_polynomial_moment (N+k+3)).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact pwGammaMobiusReflectedAtom_polynomial_bound hN k n hx
      _ = _ := by rw [integral_const_mul, pwGammaRaySource_polynomial_moment_integral]; ring
  exact (summable_nat_add_iff 2).mp htail

theorem pwGammaMobiusReflectedAtom_norm_integrals_summable (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedAtom z n x‖) := by
  simpa only [pow_zero, one_mul] using pwGammaMobiusReflectedAtom_polynomial_norm_integrals_summable z 0

theorem pwGammaMobiusTilt_reflection_integrable (z : ℂ) :
    IntegrableOn (pwGammaRayInverseReflection (pwGammaMobiusTilt z)) (Ioi 0) := by
  have hh := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusReflectedAtom_integrable z) (pwGammaMobiusReflectedAtom_norm_integrals_summable z)
  exact hh.congr (Eventually.of_forall (fun x => (pwGammaMobiusTilt_reflection_eq_tsum z x).symm))

theorem pwGammaMobiusTilt_reflection_integral (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaRayInverseReflection (pwGammaMobiusTilt z) x) =
      ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), pwGammaMobiusReflectedAtom z n x := by
  simp only [pwGammaMobiusTilt_reflection_eq_tsum]
  exact (integral_tsum_of_summable_integral_norm
    (pwGammaMobiusReflectedAtom_integrable z) (pwGammaMobiusReflectedAtom_norm_integrals_summable z)).symm

def pwGammaMobiusReflectedCurrentAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  -(Real.log (n : ℝ) : ℂ)*pwGammaMobiusReflectedAtom z n x

private theorem pwGammaReflected_log_norm_le (n : ℕ) : ‖(Real.log (n : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1)]
  linarith [Real.log_le_sub_one_of_pos hnr]

theorem pwGammaMobiusReflectedCurrentAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusReflectedCurrentAtom z n) (Ioi 0) :=
  (pwGammaMobiusReflectedAtom_integrable z n).const_mul _

theorem pwGammaMobiusReflectedCurrentAtom_norm_integrals_summable (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedCurrentAtom z n x‖) := by
  have hs := pwGammaMobiusReflectedAtom_polynomial_norm_integrals_summable z 1
  simp only [pow_one] at hs
  refine hs.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) ?_
  intro n
  simp only [pwGammaMobiusReflectedCurrentAtom, norm_mul, norm_neg, integral_const_mul]
  exact mul_le_mul_of_nonneg_right (pwGammaReflected_log_norm_le n) (integral_nonneg fun x => norm_nonneg _)

theorem pwGammaMobiusTiltCurrent_reflection_eq_tsum (z : ℂ) (x : ℝ) :
    pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x =
      ∑' n, pwGammaMobiusReflectedCurrentAtom z n x := by
  simp only [pwGammaRayInverseReflection, pwGammaMobiusTiltCurrent_eq_global_atoms,
    pwGammaMobiusReflectedCurrentAtom, pwGammaMobiusReflectedAtom, pwGammaMobiusGlobalCurrentAtom]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem pwGammaMobiusTiltCurrent_reflection_integrable (z : ℂ) :
    IntegrableOn (pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z)) (Ioi 0) := by
  have hh := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusReflectedCurrentAtom_integrable z) (pwGammaMobiusReflectedCurrentAtom_norm_integrals_summable z)
  exact hh.congr (Eventually.of_forall (fun x => (pwGammaMobiusTiltCurrent_reflection_eq_tsum z x).symm))

theorem pwGammaMobiusTiltCurrent_reflection_integral (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x) =
      ∑' n : ℕ, ∫ x in Ioi (0 : ℝ), pwGammaMobiusReflectedCurrentAtom z n x := by
  simp only [pwGammaMobiusTiltCurrent_reflection_eq_tsum]
  exact (integral_tsum_of_summable_integral_norm (pwGammaMobiusReflectedCurrentAtom_integrable z)
    (pwGammaMobiusReflectedCurrentAtom_norm_integrals_summable z)).symm

/-- Actual two-variable atom of the reflected nonlocal source. -/
def pwGammaMobiusReflectedFrullaniAtom (z : ℂ) (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  pwGammaFrullaniKernel n p.1*pwGammaMobiusReflectedAtom z n p.2

theorem pwGammaMobiusReflectedFrullaniAtom_integrable (z : ℂ) (n : ℕ) :
    Integrable (pwGammaMobiusReflectedFrullaniAtom z n)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have heq : pwGammaMobiusReflectedFrullaniAtom z 0 = 0 := by
      funext p
      simp [pwGammaMobiusReflectedFrullaniAtom, pwGammaMobiusReflectedAtom_zero]
    rw [heq]; exact integrable_zero _ _ _
  exact (pwGammaFrullaniKernel_integrable hn).mul_prod (pwGammaMobiusReflectedAtom_integrable z n)

theorem pwGammaMobiusReflectedFrullaniAtom_norm_integral (z : ℂ) (n : ℕ) :
    (∫ p, ‖pwGammaMobiusReflectedFrullaniAtom z n p‖
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
        ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusReflectedCurrentAtom z n x‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusReflectedFrullaniAtom, pwGammaMobiusReflectedCurrentAtom,
      pwGammaMobiusReflectedAtom_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [pwGammaMobiusReflectedFrullaniAtom, pwGammaMobiusReflectedCurrentAtom, norm_mul, norm_neg,
    integral_const_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1)]
  rw [integral_prod_mul (fun h : ℝ => ‖pwGammaFrullaniKernel n h‖)
    (fun x : ℝ => ‖pwGammaMobiusReflectedAtom z n x‖), pwGammaFrullaniKernel_norm_integral hn]

theorem pwGammaMobiusReflectedFrullaniAtom_norm_integrals_summable (z : ℂ) :
    Summable (fun n : ℕ => ∫ p, ‖pwGammaMobiusReflectedFrullaniAtom z n p‖
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by
  simp only [pwGammaMobiusReflectedFrullaniAtom_norm_integral]
  exact pwGammaMobiusReflectedCurrentAtom_norm_integrals_summable z

theorem pwGammaMobiusReflectedFrullaniResponse_eq_tsum (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaMobiusReflectedFrullaniResponse z x h =
      ∑' n, pwGammaMobiusReflectedFrullaniAtom z n (h,x) := by
  rw [pwGammaMobiusReflectedFrullaniResponse_eq,
    pwGammaMobiusFrullaniResponse_eq_tsum z hh (inv_pos.mpr hx), ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [pwGammaMobiusReflectedFrullaniAtom, pwGammaMobiusReflectedAtom,
    pwGammaRayInverseReflection, pwGammaMobiusFrullaniAtom]
  ring

theorem pwGammaMobiusReflectedFrullaniResponse_joint_integrable (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => pwGammaMobiusReflectedFrullaniResponse z p.2 p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusReflectedFrullaniAtom_integrable z) (pwGammaMobiusReflectedFrullaniAtom_norm_integrals_summable z)
  apply Integrable.congr hs
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact (pwGammaMobiusReflectedFrullaniResponse_eq_tsum z hp.1.le hp.2).symm

theorem pwGammaMobiusReflectedFrullaniResponse_integral_interchange (z : ℂ) :
    (∫ h in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), pwGammaMobiusReflectedFrullaniResponse z x h) =
      ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusReflectedFrullaniResponse z x h :=
  integral_integral_swap (pwGammaMobiusReflectedFrullaniResponse_joint_integrable z)

theorem pwGammaMobiusReflectedFrullaniResponse_joint_integral (z : ℂ) :
    (∫ p, pwGammaMobiusReflectedFrullaniResponse z p.2 p.1
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
      ∫ x in Ioi (0 : ℝ), pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x := by
  rw [integral_prod _ (pwGammaMobiusReflectedFrullaniResponse_joint_integrable z),
    pwGammaMobiusReflectedFrullaniResponse_integral_interchange]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusReflectedFrullaniResponse_integral z hx)

theorem pwGammaMobiusLogCurrent_reflection_not_zero :
    ¬ ∀ x : ℝ, 0 < x → pwGammaRayInverseReflection pwGammaMobiusLogCurrent x = 0 := by
  intro hh
  have hz : ∀ x : ℝ, 0 < x → pwGammaMobiusLogCurrent x = 0 := by
    intro x hx
    have hi := hh x⁻¹ (inv_pos.mpr hx)
    simp only [pwGammaRayInverseReflection, inv_inv] at hi
    exact (mul_eq_zero.mp hi).resolve_left (div_ne_zero
      (pwGammaRaySource_ne_zero x⁻¹) (pwGammaRaySource_ne_zero x))
  have hm := pwGammaMobiusLogCurrent_integral
  rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero] at hm
  exact Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3/2)).ne' hm.symm

theorem pwGammaMobiusTilt_reflection_hasDerivAt (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun b : ℂ => pwGammaRayInverseReflection (pwGammaMobiusTilt b) x)
      (pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x) z :=
  (pwGammaMobiusTilt_hasDerivAt z (inv_pos.mpr hx)).const_mul _

/-- Closed actual reflected generator: all coefficient parameters admitted, with nonzero source. -/
theorem pwGammaMobiusReflectedFrullani_closed :
    Function.Involutive pwGammaRayInverseReflection ∧
    pwGammaRayInverseReflection pwGammaRaySource = pwGammaRaySource ∧
    (∀ z : ℂ, IntegrableOn (pwGammaRayInverseReflection (pwGammaMobiusTilt z)) (Ioi 0) ∧
      IntegrableOn (pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z)) (Ioi 0) ∧
      Integrable (fun p : ℝ × ℝ => pwGammaMobiusReflectedFrullaniResponse z p.2 p.1)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
      (∀ x : ℝ, 0 < x → (∫ h in Ioi (0 : ℝ), pwGammaMobiusReflectedFrullaniResponse z x h) =
        pwGammaRayInverseReflection (pwGammaMobiusTiltCurrent z) x)) ∧
    ¬ (∀ x : ℝ, 0 < x → pwGammaRayInverseReflection pwGammaMobiusLogCurrent x = 0) :=
  ⟨pwGammaRayInverseReflection_involutive, pwGammaRayInverseReflection_source_fixed,
    fun z => ⟨pwGammaMobiusTilt_reflection_integrable z, pwGammaMobiusTiltCurrent_reflection_integrable z,
      pwGammaMobiusReflectedFrullaniResponse_joint_integrable z,
      fun _x hx => pwGammaMobiusReflectedFrullaniResponse_integral z hx⟩,
    pwGammaMobiusLogCurrent_reflection_not_zero⟩

end
end RHTower
