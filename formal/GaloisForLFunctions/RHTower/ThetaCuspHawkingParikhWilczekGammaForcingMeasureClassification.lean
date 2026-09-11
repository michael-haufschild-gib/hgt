import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusLogarithmicCurrent

/-!
# Actual Gamma forcing: ray mass, log-domain obstruction, complete response

Both raw differential forcings have admitted affine ray masses, with distinct
zero-defect shifts relative to the complete arithmetic current. Their log-line
normalized tails are nonzero at every shift, excluding separate integrability.
The potential terms are also nonintegrable separately. Both complete connection
sums are the admitted source derivative and have zero log-line mass for every
shift. The same derivative has ray mass -Gamma(3/2), leaving exact arithmetic
mass defect 2*Gamma(3/2). All source terms and measures are retained.
No physical spectral parameter, independent Ward balance, or RH is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaRaySource_inv_moment_eq {x : ℝ} (hx : 0 < x) :
    pwGammaRaySource x / (x : ℂ) =
      ((Real.exp (-x) * x ^ ((1/2 : ℝ)-1) : ℝ) : ℂ) := by
  rw [pwGammaRaySource_eq hx, Real.rpow_sub_one hx.ne', Real.sqrt_eq_rpow]
  push_cast
  ring

theorem pwGammaRaySource_inv_moment_integrable :
    IntegrableOn (fun x : ℝ => pwGammaRaySource x / (x : ℂ)) (Ioi 0) := by
  refine IntegrableOn.congr_fun
    ((Real.GammaIntegral_convergent (s := 1/2) (by positivity)).ofReal)
    (fun x hx => (pwGammaRaySource_inv_moment_eq hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_inv_moment_integral :
    (∫ x in Ioi (0 : ℝ), pwGammaRaySource x / (x : ℂ)) = (Real.Gamma (1/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ), pwGammaRaySource x / (x : ℂ)) =
      ∫ x in Ioi (0 : ℝ), ((Real.exp (-x)*x^((1/2 : ℝ)-1) : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaRaySource_inv_moment_eq hx
  rw [he, integral_complex_ofReal, ← Real.Gamma_eq_integral (by positivity)]

private theorem pwGammaRaySource_mul_moment_eq {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * pwGammaRaySource x = ((x * ‖pwGammaRaySource x‖ : ℝ) : ℂ) := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  push_cast
  rfl

theorem pwGammaRaySource_mul_moment_integrable :
    IntegrableOn (fun x : ℝ => (x : ℂ) * pwGammaRaySource x) (Ioi 0) := by
  exact IntegrableOn.congr_fun pwGammaRaySource_first_moment_integrable.ofReal
    (fun x hx => (pwGammaRaySource_mul_moment_eq hx).symm) measurableSet_Ioi

theorem pwGammaRaySource_mul_moment_integral :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) * pwGammaRaySource x) = (Real.Gamma (5/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ), (x : ℂ) * pwGammaRaySource x) =
      ∫ x in Ioi (0 : ℝ), ((x * ‖pwGammaRaySource x‖ : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaRaySource_mul_moment_eq hx
  rw [he, integral_complex_ofReal, pwGammaRaySource_first_moment_integral]

theorem pwGammaInverseConnectionForcing_ray_decomposition (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaInverseConnectionForcing z (Real.log x) =
      (1/2 : ℂ) * (pwGammaRaySource x / (x : ℂ) - (x : ℂ)*pwGammaRaySource x) -
        z * pwGammaRaySource x := by
  change (-(Real.sinh (Real.log x) : ℂ)-z) * pwGammaRaySource x = _
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hx]
  push_cast
  ring

theorem pwGammaConnectionForcing_ray_decomposition (z : ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaConnectionForcing z (Real.log x) =
      (1-z) * pwGammaRaySource x - (3/2 : ℂ)*((x : ℂ)*pwGammaRaySource x) -
        (1/2 : ℂ)*(pwGammaRaySource x / (x : ℂ)) := by
  change (((1-Real.exp (Real.log x)-Real.cosh (Real.log x) : ℝ) : ℂ)-z)*pwGammaRaySource x = _
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hx]
  push_cast
  ring

theorem pwGammaInverseConnectionForcing_ray_integrable (z : ℂ) :
    IntegrableOn (fun x => pwGammaInverseConnectionForcing z (Real.log x)) (Ioi 0) := by
  have hs := ((pwGammaRaySource_inv_moment_integrable.sub
    pwGammaRaySource_mul_moment_integrable).const_mul (1/2 : ℂ)).sub
    (pwGammaRaySource_integrable.const_mul z)
  exact IntegrableOn.congr_fun hs
    (fun x hx => (pwGammaInverseConnectionForcing_ray_decomposition z hx).symm) measurableSet_Ioi

theorem pwGammaConnectionForcing_ray_integrable (z : ℂ) :
    IntegrableOn (fun x => pwGammaConnectionForcing z (Real.log x)) (Ioi 0) := by
  have hs := ((pwGammaRaySource_integrable.const_mul (1-z)).sub
    (pwGammaRaySource_mul_moment_integrable.const_mul (3/2 : ℂ))).sub
    (pwGammaRaySource_inv_moment_integrable.const_mul (1/2 : ℂ))
  exact IntegrableOn.congr_fun hs
    (fun x hx => (pwGammaConnectionForcing_ray_decomposition z hx).symm) measurableSet_Ioi

private theorem pwGamma_half_moments :
    (Real.Gamma (1/2) : ℂ) = 2 * (Real.Gamma (3/2) : ℂ) ∧
    (Real.Gamma (5/2) : ℂ) = (3/2 : ℂ) * (Real.Gamma (3/2) : ℂ) := by
  have h1 := Real.Gamma_add_one (s := 1/2) (by positivity)
  have h3 := Real.Gamma_add_one (s := 3/2) (by positivity)
  rw [show (1/2 : ℝ)+1=3/2 by ring] at h1
  rw [show (3/2 : ℝ)+1=5/2 by ring] at h3
  constructor
  · have hr : Real.Gamma (1/2)=2*Real.Gamma (3/2) := by linarith
    exact_mod_cast hr
  · rw [h3]
    push_cast
    ring

theorem pwGammaInverseConnectionForcing_ray_integral (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaInverseConnectionForcing z (Real.log x)) =
      (1/4-z)*(Real.Gamma (3/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ), pwGammaInverseConnectionForcing z (Real.log x)) =
      ∫ x in Ioi (0 : ℝ), (1/2 : ℂ) *
        (pwGammaRaySource x / (x : ℂ) - (x : ℂ)*pwGammaRaySource x) - z*pwGammaRaySource x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaInverseConnectionForcing_ray_decomposition z hx
  have hi : IntegrableOn (fun x : ℝ => pwGammaRaySource x / (x : ℂ) - (x : ℂ)*pwGammaRaySource x) (Ioi 0) :=
    pwGammaRaySource_inv_moment_integrable.sub pwGammaRaySource_mul_moment_integrable
  have hh : IntegrableOn (fun x : ℝ => (1/2 : ℂ) *
      (pwGammaRaySource x / (x : ℂ) - (x : ℂ)*pwGammaRaySource x)) (Ioi 0) := hi.const_mul _
  rw [he, integral_sub hh (pwGammaRaySource_integrable.const_mul z),
    integral_const_mul, integral_const_mul,
    integral_sub pwGammaRaySource_inv_moment_integrable pwGammaRaySource_mul_moment_integrable,
    pwGammaRaySource_inv_moment_integral, pwGammaRaySource_mul_moment_integral,
    pwGammaRaySource_integral, pwGamma_half_moments.1, pwGamma_half_moments.2]
  ring

theorem pwGammaConnectionForcing_ray_integral (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaConnectionForcing z (Real.log x)) =
      (-9/4-z)*(Real.Gamma (3/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ), pwGammaConnectionForcing z (Real.log x)) =
      ∫ x in Ioi (0 : ℝ), (1-z)*pwGammaRaySource x -
        (3/2 : ℂ)*((x : ℂ)*pwGammaRaySource x) - (1/2 : ℂ)*(pwGammaRaySource x / (x : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaConnectionForcing_ray_decomposition z hx
  have hh : IntegrableOn (fun x : ℝ => (1-z)*pwGammaRaySource x -
      (3/2 : ℂ)*((x : ℂ)*pwGammaRaySource x)) (Ioi 0) :=
    (pwGammaRaySource_integrable.const_mul (1-z)).sub
      (pwGammaRaySource_mul_moment_integrable.const_mul (3/2 : ℂ))
  rw [he, integral_sub hh (pwGammaRaySource_inv_moment_integrable.const_mul (1/2 : ℂ)),
    integral_sub (pwGammaRaySource_integrable.const_mul (1-z))
      (pwGammaRaySource_mul_moment_integrable.const_mul (3/2 : ℂ)),
    integral_const_mul, integral_const_mul, integral_const_mul,
    pwGammaRaySource_integral, pwGammaRaySource_inv_moment_integral,
    pwGammaRaySource_mul_moment_integral, pwGamma_half_moments.1, pwGamma_half_moments.2]
  ring

theorem pwGammaMobius_inverse_forcing_mass_defect (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
      pwGammaInverseConnectionForcing z (Real.log x)) = (z+3/4)*(Real.Gamma (3/2) : ℂ) := by
  rw [integral_sub pwGammaMobiusLogCurrent_integrable (pwGammaInverseConnectionForcing_ray_integrable z),
    pwGammaMobiusLogCurrent_integral, pwGammaInverseConnectionForcing_ray_integral]
  ring

theorem pwGammaMobius_positive_forcing_mass_defect (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
      pwGammaConnectionForcing z (Real.log x)) = (z+13/4)*(Real.Gamma (3/2) : ℂ) := by
  rw [integral_sub pwGammaMobiusLogCurrent_integrable (pwGammaConnectionForcing_ray_integrable z),
    pwGammaMobiusLogCurrent_integral, pwGammaConnectionForcing_ray_integral]
  ring

theorem pwGammaMobius_inverse_mass_balance_iff (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
      pwGammaInverseConnectionForcing z (Real.log x)) = 0 ↔ z = -3/4 := by
  have hg : (Real.Gamma (3/2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [pwGammaMobius_inverse_forcing_mass_defect, mul_eq_zero, or_iff_left hg]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

theorem pwGammaMobius_positive_mass_balance_iff (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
      pwGammaConnectionForcing z (Real.log x)) = 0 ↔ z = -13/4 := by
  have hg : (Real.Gamma (3/2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [pwGammaMobius_positive_forcing_mass_defect, mul_eq_zero, or_iff_left hg]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

private theorem pwGamma_log_half_scaled_source (t : ℝ) :
    (Real.exp (t/2) : ℂ) * (GaloisForLFunctions.expShift (1/2) 0 t : ℂ) =
      (Real.exp t : ℂ) * (Real.exp (-Real.exp t) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  simp only [GaloisForLFunctions.expShift, Nat.cast_zero, add_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem pwGammaInverseConnectionForcing_scaled_eq (z : ℂ) (t : ℝ) :
    (Real.exp (t/2) : ℂ)*pwGammaInverseConnectionForcing z t =
      ((1/2 : ℂ) - (1/2 : ℂ)*(Real.exp t : ℂ)^2 - z*(Real.exp t : ℂ)) *
        (Real.exp (-Real.exp t) : ℂ) := by
  unfold pwGammaInverseConnectionForcing
  calc
    _ = (-(Real.sinh t : ℂ)-z) * ((Real.exp (t/2) : ℂ)*
        (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) := by ring
    _ = _ := by
      rw [pwGamma_log_half_scaled_source, Real.sinh_eq, Real.exp_neg]
      push_cast
      have he : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
      field_simp
      ring

theorem pwGammaConnectionForcing_scaled_eq (z : ℂ) (t : ℝ) :
    (Real.exp (t/2) : ℂ)*pwGammaConnectionForcing z t =
      ((-1/2 : ℂ) + (1-z)*(Real.exp t : ℂ) - (3/2 : ℂ)*(Real.exp t : ℂ)^2) *
        (Real.exp (-Real.exp t) : ℂ) := by
  unfold pwGammaConnectionForcing
  calc
    _ = (((1-Real.exp t-Real.cosh t : ℝ) : ℂ)-z) * ((Real.exp (t/2) : ℂ)*
        (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) := by ring
    _ = _ := by
      rw [pwGamma_log_half_scaled_source, Real.cosh_eq, Real.exp_neg]
      push_cast
      have he : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
      field_simp
      ring

theorem pwGammaInverseConnectionForcing_scaled_limit (z : ℂ) :
    Tendsto (fun t : ℝ => (Real.exp (t/2) : ℂ)*pwGammaInverseConnectionForcing z t)
      atBot (𝓝 (1/2 : ℂ)) := by
  have he := Real.tendsto_exp_atBot.ofReal
  have hgr : Tendsto (fun t : ℝ => Real.exp (-Real.exp t)) atBot (𝓝 1) := by
    have hh := (Real.continuous_exp.tendsto (-(0 : ℝ))).comp Real.tendsto_exp_atBot.neg
    simpa only [neg_zero, Real.exp_zero, Function.comp_def] using hh
  have hg := hgr.ofReal
  have hp := ((tendsto_const_nhds (x := (1/2 : ℂ))).sub
    ((he.pow 2).const_mul (1/2 : ℂ))).sub (he.const_mul z)
  have hl : Tendsto (fun t : ℝ =>
      ((1/2 : ℂ) - (1/2 : ℂ)*(Real.exp t : ℂ)^2 - z*(Real.exp t : ℂ)) *
        (Real.exp (-Real.exp t) : ℂ)) atBot (𝓝 (1/2 : ℂ)) := by
    simpa using hp.mul hg
  exact hl.congr fun t => (pwGammaInverseConnectionForcing_scaled_eq z t).symm

theorem pwGammaConnectionForcing_scaled_limit (z : ℂ) :
    Tendsto (fun t : ℝ => (Real.exp (t/2) : ℂ)*pwGammaConnectionForcing z t)
      atBot (𝓝 (-1/2 : ℂ)) := by
  have he := Real.tendsto_exp_atBot.ofReal
  have hgr : Tendsto (fun t : ℝ => Real.exp (-Real.exp t)) atBot (𝓝 1) := by
    have hh := (Real.continuous_exp.tendsto (-(0 : ℝ))).comp Real.tendsto_exp_atBot.neg
    simpa only [neg_zero, Real.exp_zero, Function.comp_def] using hh
  have hg := hgr.ofReal
  have hp := ((tendsto_const_nhds (x := (-1/2 : ℂ))).add
    (he.const_mul (1-z))).sub ((he.pow 2).const_mul (3/2 : ℂ))
  have hl : Tendsto (fun t : ℝ =>
      ((-1/2 : ℂ) + (1-z)*(Real.exp t : ℂ) - (3/2 : ℂ)*(Real.exp t : ℂ)^2) *
        (Real.exp (-Real.exp t) : ℂ)) atBot (𝓝 (-1/2 : ℂ)) := by
    simpa using hp.mul hg
  exact hl.congr fun t => (pwGammaConnectionForcing_scaled_eq z t).symm

private theorem pwGamma_forcing_not_integrable_of_scaled_limit {f : ℝ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hf : Tendsto (fun t => (Real.exp (t/2) : ℂ)*f t) atBot (𝓝 c)) :
    ¬ Integrable f := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hhalf : 0 < ‖c‖/2 := by positivity
  have he : Tendsto (fun t : ℝ => Real.exp (t/2)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by positivity))
  have hlow : ∀ᶠ t : ℝ in atBot, ‖c‖/2 < ‖(Real.exp (t/2) : ℂ)*f t‖ :=
    hf.norm.eventually (eventually_gt_nhds (by linarith : ‖c‖/2 < ‖c‖))
  have hsmall : ∀ᶠ t : ℝ in atBot, Real.exp (t/2) < ‖c‖/2 :=
    he.eventually (eventually_lt_nhds hhalf)
  have hbound : ∀ᶠ t : ℝ in atBot, 1 ≤ ‖f t‖ := by
    filter_upwards [hlow, hsmall] with t ht heq
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at ht
    by_contra h
    have hn : ‖f t‖ < 1 := lt_of_not_ge h
    have hh := mul_lt_mul_of_pos_left hn (Real.exp_pos (t/2))
    rw [mul_one] at hh
    linarith
  obtain ⟨a, ha⟩ := eventually_atBot.mp hbound
  intro hint
  exact not_integrableOn_Iic_of_le zero_lt_one (fun t ht => ha t ht) hint.norm.integrableOn

theorem pwGammaInverseConnectionForcing_not_integrable (z : ℂ) :
    ¬ Integrable (pwGammaInverseConnectionForcing z) :=
  pwGamma_forcing_not_integrable_of_scaled_limit (div_ne_zero one_ne_zero two_ne_zero)
    (pwGammaInverseConnectionForcing_scaled_limit z)

theorem pwGammaConnectionForcing_not_integrable (z : ℂ) :
    ¬ Integrable (pwGammaConnectionForcing z) :=
  pwGamma_forcing_not_integrable_of_scaled_limit (div_ne_zero (neg_ne_zero.mpr one_ne_zero) two_ne_zero)
    (pwGammaConnectionForcing_scaled_limit z)


private theorem pwGammaSource_log_integrable :
    Integrable (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) := by
  change Integrable (GaloisForLFunctions.expShiftC (1/2))
  simpa only [iteratedDeriv_zero] using
    GaloisForLFunctions.integrable_iteratedDeriv_expShiftC (σ := 1/2) (by positivity) 0

private theorem pwGammaSource_log_derivative_integrable :
    Integrable (deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ))) := by
  change Integrable (deriv (GaloisForLFunctions.expShiftC (1/2)))
  simpa only [iteratedDeriv_one] using
    GaloisForLFunctions.integrable_iteratedDeriv_expShiftC (σ := 1/2) (by positivity) 1

theorem pwGamma_complete_positive_connection_integrable (z : ℂ) :
    Integrable (fun t : ℝ =>
      ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
        pwGammaConnectionForcing z t) := by
  refine pwGammaSource_log_derivative_integrable.congr ?_
  filter_upwards with t
  exact (pwGammaConnectionForcing_hasDerivAt z t).deriv

theorem pwGamma_complete_inverse_connection_integrable (z : ℂ) :
    Integrable (fun t : ℝ =>
      (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
        pwGammaInverseConnectionForcing z t) := by
  refine pwGammaSource_log_derivative_integrable.congr ?_
  filter_upwards with t
  exact (pwGammaInverseConnectionForcing_hasDerivAt z t).deriv

theorem pwGamma_complete_positive_connection_integral (z : ℂ) :
    (∫ t : ℝ,
      ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
        pwGammaConnectionForcing z t) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (pwGammaConnectionForcing_hasDerivAt z)
    (pwGamma_complete_positive_connection_integrable z) pwGammaSource_log_integrable

theorem pwGamma_complete_inverse_connection_integral (z : ℂ) :
    (∫ t : ℝ,
      (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
        pwGammaInverseConnectionForcing z t) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (pwGammaInverseConnectionForcing_hasDerivAt z)
    (pwGamma_complete_inverse_connection_integrable z) pwGammaSource_log_integrable

/-- The potential term cannot be integrated separately from its complete forcing. -/
theorem pwGamma_positive_potential_source_not_integrable (z : ℂ) :
    ¬ Integrable (fun t : ℝ =>
      ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) := by
  intro h
  apply pwGammaConnectionForcing_not_integrable z
  have hs := (pwGamma_complete_positive_connection_integrable z).sub h
  refine hs.congr ?_
  filter_upwards with t
  change (((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
    pwGammaConnectionForcing z t) -
      ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) = _
  ring

theorem pwGamma_inverse_potential_source_not_integrable (z : ℂ) :
    ¬ Integrable (fun t : ℝ =>
      (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) := by
  intro h
  apply pwGammaInverseConnectionForcing_not_integrable z
  have hs := (pwGamma_complete_inverse_connection_integrable z).sub h
  refine hs.congr ?_
  filter_upwards with t
  change ((-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
    pwGammaInverseConnectionForcing z t) -
      (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) = _
  ring

/-- The full connection response, after cancellation, retains the source derivative. -/
theorem pwGammaSource_log_derivative_ray_eq {x : ℝ} (hx : 0 < x) :
    deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) (Real.log x) =
      (1/2 : ℂ)*pwGammaRaySource x - (x : ℂ)*pwGammaRaySource x := by
  rw [(pwGammaConnectionForcing_hasDerivAt 0 (Real.log x)).deriv]
  change ((pwLogSingularConnectionPotential (Real.log x) : ℂ)+0)*pwGammaRaySource x +
    (((1-Real.exp (Real.log x)-Real.cosh (Real.log x) : ℝ) : ℂ)-0)*pwGammaRaySource x = _
  rw [pwLogSingularConnectionPotential, Real.exp_log hx]
  push_cast
  ring

theorem pwGammaSource_log_derivative_ray_integrable :
    IntegrableOn (fun x : ℝ =>
      deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) (Real.log x)) (Ioi 0) := by
  have hh : IntegrableOn (fun x : ℝ => (1/2 : ℂ)*pwGammaRaySource x - (x : ℂ)*pwGammaRaySource x) (Ioi 0) :=
    (pwGammaRaySource_integrable.const_mul (1/2 : ℂ)).sub pwGammaRaySource_mul_moment_integrable
  exact IntegrableOn.congr_fun hh (fun x hx => (pwGammaSource_log_derivative_ray_eq hx).symm) measurableSet_Ioi

theorem pwGammaSource_log_derivative_ray_integral :
    (∫ x in Ioi (0 : ℝ),
      deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) (Real.log x)) =
        -(Real.Gamma (3/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ),
      deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) (Real.log x)) =
        ∫ x in Ioi (0 : ℝ), (1/2 : ℂ)*pwGammaRaySource x - (x : ℂ)*pwGammaRaySource x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaSource_log_derivative_ray_eq hx
  rw [he, integral_sub (pwGammaRaySource_integrable.const_mul (1/2 : ℂ)) pwGammaRaySource_mul_moment_integrable,
    integral_const_mul, pwGammaRaySource_integral, pwGammaRaySource_mul_moment_integral, pwGamma_half_moments.2]
  ring

/-- The arithmetic current differs in total ray mass even from the complete response. -/
theorem pwGammaMobius_complete_response_mass_defect :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
      deriv (fun t : ℝ => (GaloisForLFunctions.expShift (1/2) 0 t : ℂ)) (Real.log x)) =
        2*(Real.Gamma (3/2) : ℂ) := by
  rw [integral_sub pwGammaMobiusLogCurrent_integrable pwGammaSource_log_derivative_ray_integrable,
    pwGammaMobiusLogCurrent_integral, pwGammaSource_log_derivative_ray_integral]
  ring

/-- Complete unconditional classification: ray masses, log-domain obstruction and admitted total law. -/
theorem pwGammaForcingMeasureClassification_closed :
    ∀ z : ℂ,
      IntegrableOn (fun x => pwGammaInverseConnectionForcing z (Real.log x)) (Ioi 0) ∧
      IntegrableOn (fun x => pwGammaConnectionForcing z (Real.log x)) (Ioi 0) ∧
      ((∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
        pwGammaInverseConnectionForcing z (Real.log x)) = 0 ↔ z = -3/4) ∧
      ((∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x -
        pwGammaConnectionForcing z (Real.log x)) = 0 ↔ z = -13/4) ∧
      (¬ Integrable (pwGammaInverseConnectionForcing z)) ∧
      (¬ Integrable (pwGammaConnectionForcing z)) ∧
      Integrable (fun t : ℝ =>
        (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
          pwGammaInverseConnectionForcing z t) ∧
      Integrable (fun t : ℝ =>
        ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
          pwGammaConnectionForcing z t) ∧
      (∫ t : ℝ,
        (-(pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
          pwGammaInverseConnectionForcing z t) = 0 ∧
      (∫ t : ℝ,
        ((pwLogSingularConnectionPotential t : ℂ)+z)*(GaloisForLFunctions.expShift (1/2) 0 t : ℂ) +
          pwGammaConnectionForcing z t) = 0 :=
  fun z => ⟨pwGammaInverseConnectionForcing_ray_integrable z, pwGammaConnectionForcing_ray_integrable z,
    pwGammaMobius_inverse_mass_balance_iff z, pwGammaMobius_positive_mass_balance_iff z,
    pwGammaInverseConnectionForcing_not_integrable z, pwGammaConnectionForcing_not_integrable z,
    pwGamma_complete_inverse_connection_integrable z, pwGamma_complete_positive_connection_integrable z,
    pwGamma_complete_inverse_connection_integral z, pwGamma_complete_positive_connection_integral z⟩

end
end RHTower
