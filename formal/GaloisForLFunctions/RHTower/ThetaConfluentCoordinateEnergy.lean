import GaloisForLFunctions.RHTower.ThetaConfluentCoordinateCurrent
import GaloisForLFunctions.RHTower.ThetaTailConfluentCenterGram
import GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurFarTail

/-! Strict center and joint-center coordinate-energy signs, retaining the logarithmic
boundary flux and the complete inverse-Gram correction. -/

noncomputable section
open MeasureTheory Filter Topology Set
namespace RHTower.ThetaCoordinate

local notation "k" => thetaCuspFullSource
local notation "k₁" => deriv thetaCuspFullSource
local notation "k₂" => deriv (deriv thetaCuspFullSource)
local notation "k₃" => deriv (deriv (deriv thetaCuspFullSource))
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "q" => thetaCuspLogCurvature 0
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "S" => thetaCuspSingleAtomReflectionScale 1

private abbrev source := thetaCuspSchwartzReal
private abbrev dsource := SchwartzMap.derivCLM ℝ ℝ source
private abbrev ddsource := SchwartzMap.derivCLM ℝ ℝ dsource
private abbrev dddsource := SchwartzMap.derivCLM ℝ ℝ ddsource

private theorem source_hasDerivAt (t : ℝ) : HasDerivAt k (k₁ t) t :=
  source.hasDerivAt t

private theorem first_hasDerivAt (t : ℝ) : HasDerivAt k₁ (k₂ t) t :=
  dsource.hasDerivAt t

private theorem second_hasDerivAt (t : ℝ) : HasDerivAt k₂ (k₃ t) t :=
  ddsource.hasDerivAt t

private theorem first_eq (t : ℝ) : k₁ t = -p t*k t := by
  have h : iteratedDeriv 1 thetaCuspLogSource t = k₁ t/k t := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

private theorem second_eq (t : ℝ) : k₂ t = (p t^2-c t)*k t := by
  have he : k₁ = fun t => -p t*k t := funext first_eq
  have h := (((hasDerivAt_thetaCuspLogDecaySlope t).neg).mul (source_hasDerivAt t)).deriv
  change deriv (fun t => -p t*k t) t = -c t*k t+ -p t*k₁ t at h
  rw [← he, first_eq] at h
  rw [h]
  ring

/-- The center curvature retains the literal source mass. -/
theorem source_second_center : k₂ 0 = -q*k 0 := by
  have hp : p 0 = 0 := by
    simp only [thetaCuspLogDecaySlope,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]
  rw [second_eq, hp]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_sub]

private theorem third_eq (t : ℝ) : k₃ t = (-p t^3+3*p t*c t-v t)*k t := by
  have he : k₂ = fun t => (p t^2-c t)*k t := funext second_eq
  have hd : HasDerivAt (fun t => (p t^2-c t)*k t)
      ((2*p t*c t-v t)*k t+(p t^2-c t)*k₁ t) t := by
    convert! ((((hasDerivAt_thetaCuspLogDecaySlope t).pow 2).sub
      (hasDerivAt_thetaCuspLogCurvature t)).mul (source_hasDerivAt t)) using 1
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  have h := hd.deriv
  rw [← he, first_eq] at h
  rw [h]
  ring

private theorem first_zero : k₁ 0 = 0 := by
  simpa only [iteratedDeriv_one] using
    iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) ⟨0,rfl⟩

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private theorem product_integrable (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => f t*g t) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable

private theorem weighted_product_integrable (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => t*f t*g t) := by
  simpa only [weighted_apply] using product_integrable (weighted f) g

private theorem weighted_product_zero (f g : SchwartzMap ℝ ℝ) :
    Tendsto (fun t : ℝ => t*f t*g t) atTop (𝓝 0) := by
  simpa only [weighted_apply, mul_zero] using
    ((weighted f).tendsto_cocompact.mono_left atTop_le_cocompact).mul
      (g.tendsto_cocompact.mono_left atTop_le_cocompact)

private theorem scale_ne (t : ℝ) : S t ≠ 0 := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

private theorem slope_scaled_limit : Tendsto (fun t => p t/S t) atTop (𝓝 2) := by
  have h := (thetaCuspFullSource_deriv_div_firstAtom_scale_tendsto.div
    thetaCuspFullSource_div_firstAtom_tendsto_one (by norm_num : (1:ℝ) ≠ 0)).neg
  have h' : Tendsto (fun t => -(k₁ t/(thetaCuspSourceTerm t 1*S t)/
      (k t/thetaCuspSourceTerm t 1))) atTop (𝓝 2) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [first_eq]
  field_simp [(thetaCuspSourceTerm_pos_of_pos_of_nat_pos ht (by norm_num : 0 < (1:ℕ))).ne',
    (thetaCuspFullSource_pos_all t).ne', scale_ne t]

private theorem curvature_slope_ratio_limit :
    Tendsto (fun t => c t/p t^2) atTop (𝓝 0) := by
  have hc : Tendsto (fun t => c t/S t) atTop (𝓝 4) :=
    thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four
  have h := (hc.div (slope_scaled_limit.pow 2) (by norm_num : (2:ℝ)^2 ≠ 0)).mul
    thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have h' : Tendsto (fun t => (c t/S t/(p t/S t)^2)*(S t)⁻¹) atTop (𝓝 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have hp : p t ≠ 0 := (neg_iteratedDeriv_one_thetaCuspLogSource_pos ht).ne'
  field_simp [scale_ne t, hp]

/-- The extra logarithmic flux whose boundary must be audited separately. -/
def logarithmicFlux (t : ℝ) : ℝ := t*k₁ t^3/k t

/-- The quotient flux vanishes by actual source asymptotics and a Schwartz product. -/
theorem logarithmicFlux_limit : Tendsto logarithmicFlux atTop (𝓝 0) := by
  have hr : Tendsto (fun t => 1-c t/p t^2) atTop (𝓝 (1:ℝ)) := by
    simpa using curvature_slope_ratio_limit.const_sub 1
  have hw : Tendsto (fun t => t*k₁ t*k₂ t) atTop (𝓝 0) :=
    weighted_product_zero dsource ddsource
  have h := hw.div hr (by norm_num : (1:ℝ) ≠ 0)
  have h' : Tendsto (fun t => (t*k₁ t*k₂ t)/(1-c t/p t^2)) atTop (𝓝 0) := by
    change Tendsto (fun t => (t*k₁ t*k₂ t)/(1-c t/p t^2)) atTop (𝓝 (0/(1:ℝ))) at h
    simpa only [zero_div] using h
  apply h'.congr'
  filter_upwards [(tendsto_order.1 hr).1 0 (by norm_num), eventually_gt_atTop (0:ℝ)] with t hr ht
  have hp : p t ≠ 0 := (neg_iteratedDeriv_one_thetaCuspLogSource_pos ht).ne'
  have hk := (thetaCuspFullSource_pos_all t).ne'
  have he : p t^2-c t ≠ 0 := by
    intro he
    have hc : c t = p t^2 := by linarith
    simp only [hc, div_self (pow_ne_zero 2 hp), sub_self, lt_self_iff_false] at hr
  unfold logarithmicFlux
  rw [first_eq, second_eq]
  field_simp [hp, hk, he]

/-- Weighted second-derivative mass of the literal source. -/
def secondMass : ℝ := ∫ t in Ioi 0, t*k₂ t^2

/-- The cubic coefficient controlling the center confluent coordinate residual. -/
def coordinateEnergy : ℝ := secondMass-3*q*ThetaConfluent.derivativeMass+q*k 0^2

/-- Polynomial Schwartz remainder after removing the logarithmic flux derivative. -/
def polynomialCurrent (t : ℝ) : ℝ :=
  3*(t*k₂ t^2)-t*k₁ t*k₃ t+k₁ t*k₂ t-
    6*q*(t*k₁ t^2)+6*q*(t*k t*k₂ t)-2*q*(k t*k₁ t)

private theorem second_square_integrable : Integrable (fun t => t*k₂ t^2) := by
  have h : Integrable (fun t => t*k₂ t*k₂ t) := weighted_product_integrable ddsource ddsource
  simpa only [pow_two, mul_assoc] using h

private theorem mixed_third_integrable : Integrable (fun t => t*k₁ t*k₃ t) :=
  weighted_product_integrable dsource dddsource

private theorem mixed_second_integrable : Integrable (fun t => t*k t*k₂ t) :=
  weighted_product_integrable source ddsource

private theorem first_second_integrable : Integrable (fun t => k₁ t*k₂ t) :=
  product_integrable dsource ddsource

theorem polynomialCurrent_integrable : Integrable polynomialCurrent :=
  (((((second_square_integrable.const_mul 3).sub mixed_third_integrable).add
    first_second_integrable).sub
    (ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.const_mul (6*q))).add
    (mixed_second_integrable.const_mul (6*q))).sub
    (ThetaGeometricBoundaryAudit.source_times_derivative_integrable.const_mul (2*q))

theorem first_second_integral : (∫ t in Ioi 0, k₁ t*k₂ t) = 0 := by
  have hd (t : ℝ) : HasDerivAt (fun t => k₁ t^2/2) (k₁ t*k₂ t) t := by
    convert! ((first_hasDerivAt t).pow 2).div_const 2 using 1
    ring
  have hl : Tendsto (fun t => k₁ t^2/2) atTop (𝓝 0) := by
    have h : Tendsto k₁ atTop (𝓝 0) := dsource.tendsto_cocompact.mono_left atTop_le_cocompact
    simpa using (h.pow 2).div_const 2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) first_second_integrable.integrableOn hl
  simpa only [first_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using h

theorem mixed_third_integral : (∫ t in Ioi 0, t*k₁ t*k₃ t) = -secondMass := by
  have hd (t : ℝ) : HasDerivAt (fun t => t*k₁ t*k₂ t)
      (k₁ t*k₂ t+t*k₂ t^2+t*k₁ t*k₃ t) t := by
    convert! ((hasDerivAt_id t).mul (first_hasDerivAt t)).mul
      (second_hasDerivAt t) using 1
    simp only [id_eq, Pi.mul_apply]
    ring
  have hiab : Integrable (fun t => k₁ t*k₂ t+t*k₂ t^2) :=
    first_second_integrable.add second_square_integrable
  have hi := hiab.add mixed_third_integrable
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun t _ => hd t) hi.integrableOn (weighted_product_zero dsource ddsource)
  simp only [zero_mul, sub_zero] at h
  rw [integral_add hiab.integrableOn
    mixed_third_integrable.integrableOn,
    integral_add first_second_integrable.integrableOn second_square_integrable.integrableOn,
    first_second_integral] at h
  change 0+secondMass+(∫ t in Ioi 0, t*k₁ t*k₃ t) = 0 at h
  linarith

/-- Exact integrated polynomial identity, containing no logarithmic quotient. -/
theorem polynomialCurrent_integral : (∫ t in Ioi 0, polynomialCurrent t) = 4*coordinateEnergy := by
  have hi1 : Integrable (fun t => 3*(t*k₂ t^2)-t*k₁ t*k₃ t) :=
    (second_square_integrable.const_mul 3).sub mixed_third_integrable
  have hi2 : Integrable (fun t => 3*(t*k₂ t^2)-t*k₁ t*k₃ t+k₁ t*k₂ t) :=
    hi1.add first_second_integrable
  have hi3 : Integrable (fun t => 3*(t*k₂ t^2)-t*k₁ t*k₃ t+k₁ t*k₂ t-6*q*(t*k₁ t^2)) :=
    hi2.sub (ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.const_mul (6*q))
  have hi4 : Integrable (fun t => 3*(t*k₂ t^2)-t*k₁ t*k₃ t+k₁ t*k₂ t-
      6*q*(t*k₁ t^2)+6*q*(t*k t*k₂ t)) :=
    hi3.add (mixed_second_integrable.const_mul (6*q))
  unfold polynomialCurrent
  rw [integral_sub hi4.integrableOn
      (ThetaGeometricBoundaryAudit.source_times_derivative_integrable.const_mul (2*q)).integrableOn,
    integral_add hi3.integrableOn (mixed_second_integrable.const_mul (6*q)).integrableOn,
    integral_sub hi2.integrableOn
      (ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.const_mul (6*q)).integrableOn,
    integral_add hi1.integrableOn first_second_integrable.integrableOn,
    integral_sub (second_square_integrable.const_mul 3).integrableOn mixed_third_integrable.integrableOn,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    mixed_third_integral, first_second_integral, ThetaConfluent.weighted_second_integral,
    ThetaGeometricBoundaryAudit.source_times_derivative_tail]
  dsimp only [coordinateEnergy, secondMass, ThetaConfluent.derivativeMass]
  ring

/-- Exact differential balance; the logarithmic terms are audited through this flux. -/
theorem logarithmicFlux_hasDerivAt (t : ℝ) :
    HasDerivAt logarithmicFlux (polynomialCurrent t-coordinateCurrent t*k t^2) t := by
  convert! (((hasDerivAt_id t).mul ((first_hasDerivAt t).pow 3)).div
    (source_hasDerivAt t) (thetaCuspFullSource_pos_all t).ne') using 1
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply]
  unfold polynomialCurrent coordinateCurrent
  rw [first_eq, second_eq, third_eq]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

private theorem polynomialCurrent_continuous : Continuous polynomialCurrent := by
  have h0 : Continuous k := source.continuous
  have h1 : Continuous k₁ := dsource.continuous
  have h2 : Continuous k₂ := ddsource.continuous
  have h3 : Continuous k₃ := dddsource.continuous
  unfold polynomialCurrent
  fun_prop

private theorem integral_pos_of_logarithmicFlux {f g : ℝ → ℝ}
    (hfi : Integrable f) (hfc : Continuous f)
    (hflux : ∀ t, HasDerivAt logarithmicFlux (f t-g t*k t^2) t)
    (hg : ∀ t, 0 < t → 0 < g t) : 0 < ∫ t in Ioi 0, f t := by
  let F (b : ℝ) := (∫ t in 0..b, f t)-logarithmicFlux b
  have hd (b : ℝ) : HasDerivAt F (g b*k b^2) b := by
    convert! (intervalIntegral.integral_hasDerivAt_right hfi.intervalIntegrable
      (hfc.stronglyMeasurableAtFilter volume (𝓝 b)) hfc.continuousAt).sub (hflux b) using 1
    ring
  have hz : F 0=0 := by
    simp only [F, intervalIntegral.integral_same, logarithmicFlux, zero_mul, zero_div, sub_zero]
  have hm : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro t _; exact (hd t).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hd t).deriv]
      exact mul_pos (hg t (by simpa only [interior_Ici,mem_Ioi] using ht))
        (sq_pos_of_pos (thetaCuspFullSource_pos_all t))
  have hl : Tendsto F atTop (𝓝 (∫ t in Ioi 0, f t)) := by
    simpa only [F,id_eq,sub_zero] using
      (intervalIntegral_tendsto_integral_Ioi 0 hfi.integrableOn tendsto_id).sub logarithmicFlux_limit
  have hp : 0 < F 1 := by
    have h := hm (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by norm_num)
      (by norm_num : (0:ℝ) < 1)
    rwa [hz] at h
  have hle : F 1 ≤ ∫ t in Ioi 0, f t := by
    apply ge_of_tendsto hl
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact hm.monotoneOn (by norm_num) (show t ∈ Ici 0 by change 0 ≤ t; linarith) ht
  exact hp.trans_le hle

/-- Strict positivity of the actual cubic center coordinate-energy invariant. -/
theorem coordinateEnergy_pos : 0 < coordinateEnergy := by
  have h := integral_pos_of_logarithmicFlux polynomialCurrent_integrable
    polynomialCurrent_continuous logarithmicFlux_hasDerivAt (fun _ ht => coordinateCurrent_pos ht)
  rw [polynomialCurrent_integral] at h
  linarith

private theorem center_mass_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

private theorem center_mass_eq : J = 2*(∫ t in Ioi 0, t*k t^2) := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut,ThetaSourceWard.thetaPrimeGammaCutEnergy_eq_tail]
  have he : (fun t : ℝ => 2*t*k t^2)=(fun t : ℝ => 2*(t*k t^2)) := by
    funext t
    ring
  rw [he,integral_const_mul]

private theorem weighted_source_square_integrable : Integrable (fun t => t*k t^2) := by
  have h : Integrable (fun t => t*k t*k t) := weighted_product_integrable source source
  simpa only [pow_two,mul_assoc] using h

private def jointGapPolynomial (t : ℝ) : ℝ :=
  t*k₁ t^2-t*k t*k₂ t+3*(k t*k₁ t)+2*q*(t*k t^2)

private theorem jointGapPolynomial_eq (t : ℝ) :
    jointGapPolynomial t = (t*c t-3*p t+2*q*t)*k t^2 := by
  unfold jointGapPolynomial
  rw [first_eq,second_eq]
  ring

private theorem jointGapPolynomial_integrable : Integrable jointGapPolynomial :=
  (((ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.sub mixed_second_integrable).add
    (ThetaGeometricBoundaryAudit.source_times_derivative_integrable.const_mul 3)).add
    (weighted_source_square_integrable.const_mul (2*q)))

private theorem jointGapPolynomial_integral : (∫ t in Ioi 0, jointGapPolynomial t) =
    2*ThetaConfluent.derivativeMass-2*k 0^2+q*J := by
  have hi : Integrable (fun t => t*k₁ t^2-t*k t*k₂ t) :=
    ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.sub mixed_second_integrable
  have hi' : Integrable (fun t => t*k₁ t^2-t*k t*k₂ t+3*(k t*k₁ t)) :=
    hi.add (ThetaGeometricBoundaryAudit.source_times_derivative_integrable.const_mul 3)
  unfold jointGapPolynomial
  rw [integral_add hi'.integrableOn (weighted_source_square_integrable.const_mul (2*q)).integrableOn,
    integral_add hi.integrableOn (ThetaGeometricBoundaryAudit.source_times_derivative_integrable.const_mul 3).integrableOn,
    integral_sub ThetaGeometricBoundaryAudit.weighted_derivative_square_integrable.integrableOn
      mixed_second_integrable.integrableOn,
    integral_const_mul,integral_const_mul,ThetaConfluent.weighted_second_integral,
    ThetaGeometricBoundaryAudit.source_times_derivative_tail,center_mass_eq]
  change ThetaConfluent.derivativeMass-(k 0^2/2-ThetaConfluent.derivativeMass)+
    3*(-k 0^2/2)+(2*q)*(∫ t in Ioi 0, t*k t^2) = _
  ring

/-- The linear energy paid by the stronger actual source current. -/
def jointCoordinateEnergy : ℝ :=
  2*secondMass-12*q*ThetaConfluent.derivativeMass+8*q*k 0^2-3*q^2*J

private def jointPolynomialCurrent (t : ℝ) : ℝ :=
  polynomialCurrent t-6*q*jointGapPolynomial t

private theorem jointPolynomialCurrent_integrable : Integrable jointPolynomialCurrent :=
  polynomialCurrent_integrable.sub (jointGapPolynomial_integrable.const_mul (6*q))

private theorem jointPolynomialCurrent_continuous : Continuous jointPolynomialCurrent := by
  have h0 : Continuous k := source.continuous
  have h1 : Continuous k₁ := dsource.continuous
  have h2 : Continuous k₂ := ddsource.continuous
  have hj : Continuous jointGapPolynomial := by
    unfold jointGapPolynomial
    fun_prop
  exact polynomialCurrent_continuous.sub (hj.const_mul (6*q))

private theorem jointPolynomialCurrent_integral :
    (∫ t in Ioi 0, jointPolynomialCurrent t) = 2*jointCoordinateEnergy := by
  unfold jointPolynomialCurrent
  rw [integral_sub polynomialCurrent_integrable.integrableOn
    (jointGapPolynomial_integrable.const_mul (6*q)).integrableOn,
    integral_const_mul,polynomialCurrent_integral,jointGapPolynomial_integral]
  unfold coordinateEnergy jointCoordinateEnergy
  ring

private theorem joint_logarithmicFlux_hasDerivAt (t : ℝ) :
    HasDerivAt logarithmicFlux (jointPolynomialCurrent t-jointCoordinateCurrent t*k t^2) t := by
  convert! logarithmicFlux_hasDerivAt t using 1
  unfold jointPolynomialCurrent jointCoordinateCurrent coordinateCurrent
  rw [jointGapPolynomial_eq]
  ring

/-- Strict source sign paying the entire linear part of joint-center compensation. -/
theorem jointCoordinateEnergy_pos : 0 < jointCoordinateEnergy := by
  have h := integral_pos_of_logarithmicFlux jointPolynomialCurrent_integrable
    jointPolynomialCurrent_continuous joint_logarithmicFlux_hasDerivAt
    (fun _ ht => jointCoordinateCurrent_pos ht)
  rw [jointPolynomialCurrent_integral] at h
  linarith

/-- The actual joint-center compensation includes the complete inverse-Gram correction. -/
def jointCoordinateCompensation : ℝ :=
  secondMass/6-2*q*ThetaConfluent.derivativeMass+2*q*k 0^2/3+
    ThetaConfluent.derivativeMass^2/J

theorem jointCoordinateCompensation_decomposition :
    jointCoordinateCompensation = jointCoordinateEnergy/12+
      (ThetaConfluent.derivativeMass-q*J/2)^2/J := by
  unfold jointCoordinateCompensation jointCoordinateEnergy
  field_simp [center_mass_pos.ne']
  ring

/-- The necessary joint-center sign is strict for the literal theta source. -/
theorem jointCoordinateCompensation_pos : 0 < jointCoordinateCompensation := by
  rw [jointCoordinateCompensation_decomposition]
  exact add_pos_of_pos_of_nonneg (div_pos jointCoordinateEnergy_pos (by norm_num))
    (div_nonneg (sq_nonneg _) center_mass_pos.le)

end RHTower.ThetaCoordinate
