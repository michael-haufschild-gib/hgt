import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import Mathlib.Analysis.Convolution

/-!
# Exact theta dilation correlations

The logarithmic half-density of the dyadic theta seed has Fourier--Laplace transform
`(2 - exp(-log(2)/2) * exp(I*z*log(2))) * xiCent(rho + 1/2 - 2*I*z)`.
Every exponential twist is integrable. The autocorrelation and reflected convolution
therefore have exact product transforms throughout the complex plane, with their own
integrability proved by the Bochner convolution theorem.

At an actual Xi divisor copy, the native mean moment vanishes while the source transform
at half the zero ordinate is nonzero. The autocorrelation has strictly positive real
transform at that ordinate. These are identities of the literal theta dilation profiles;
no modular periodization norm identity or spectral occurrence estimate is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Convolution
namespace RHTower.SelbergThetaDilationTransform
noncomputable section

/-- Logarithmic half-density of one dilated complete theta source. -/
def baseProfile (rho : ℂ) (t : ℝ) : ℂ :=
  (1/2 : ℂ) * (thetaCuspFullSource (t/2) : ℂ) *
    Complex.exp ((rho+1/2) * ((t/2 : ℝ) : ℂ))

/-- Exponential twist with angular-frequency convention, without a factor of `2*pi`. -/
def fourierIntegrand (f : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-I*z*(t:ℂ)) * f t

/-- The raw Fourier--Laplace integral. -/
def transform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, fourierIntegrand f z t

/-- The exact centered Xi argument after the logarithmic half-density change of variables. -/
def sourceArgument (rho z : ℂ) : ℂ := rho+1/2-2*I*z

private theorem base_integrand (rho z : ℂ) (t : ℝ) :
    fourierIntegrand (baseProfile rho) z t =
      (1/2 : ℂ) * ((thetaCuspFullSource (t/2) : ℂ) *
        Complex.exp (sourceArgument rho z * ((t/2 : ℝ) : ℂ))) := by
  unfold fourierIntegrand baseProfile sourceArgument
  calc
    _ = (1/2 : ℂ) * (thetaCuspFullSource (t/2) : ℂ) *
      (Complex.exp (-I*z*(t:ℂ)) * Complex.exp ((rho+1/2)*((t/2:ℝ):ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      have he : -I*z*(t:ℂ)+(rho+1/2)*((t/2:ℝ):ℂ) =
          (rho+1/2-2*I*z)*((t/2:ℝ):ℂ) := by push_cast; ring
      rw [he]
      ring

/-- Every complex exponential twist of the base theta profile is integrable. -/
theorem base_integrable (rho z : ℂ) :
    Integrable (fourierIntegrand (baseProfile rho) z) := by
  have h := (integrable_bilateralLaplace thetaCuspTiltSource (sourceArgument rho z)).comp_mul_left'
    (R := (1/2 : ℝ)) (by norm_num)
  refine (h.const_mul (1/2 : ℂ)).congr (Filter.Eventually.of_forall fun t => ?_)
  rw [base_integrand]
  simp only [thetaCuspTiltSource_k, show (1/2 : ℝ)*t = t/2 by ring]

/-- The complete theta source supplies the base transform on the whole complex plane. -/
theorem transform_base (rho z : ℂ) :
    transform (baseProfile rho) z = xiCent (sourceArgument rho z) := by
  unfold transform
  simp_rw [base_integrand]
  rw [MeasureTheory.integral_const_mul]
  let F : ℝ → ℂ := fun x => (thetaCuspFullSource x : ℂ) *
    Complex.exp (sourceArgument rho z * (x:ℂ))
  change (1/2 : ℂ) * (∫ t : ℝ, F (t/2)) = _
  rw [Measure.integral_comp_div]
  have h : (∫ x : ℝ, F x) = xiCent (sourceArgument rho z) :=
    bilateralLaplace_thetaCuspTiltSource_eq_xiCent _
  rw [h]
  norm_num
  ring

private theorem shifted_integrand (rho z : ℂ) (L t : ℝ) :
    fourierIntegrand (fun x => baseProfile rho (x+L)) z t =
      Complex.exp (I*z*(L:ℂ)) * fourierIntegrand (baseProfile rho) z (t+L) := by
  unfold fourierIntegrand
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- Real translation preserves integrability of every complex twist of the theta profile. -/
theorem shifted_base_integrable (rho z : ℂ) (L : ℝ) :
    Integrable (fourierIntegrand (fun x => baseProfile rho (x+L)) z) := by
  exact ((base_integrable rho z).comp_add_right L).const_mul
    (Complex.exp (I*z*(L:ℂ))) |>.congr
      (Filter.Eventually.of_forall fun t => (shifted_integrand rho z L t).symm)

/-- A real dilation shift gives its exact exponential multiplier. -/
theorem transform_shifted_base (rho z : ℂ) (L : ℝ) :
    transform (fun x => baseProfile rho (x+L)) z =
      Complex.exp (I*z*(L:ℂ)) * xiCent (sourceArgument rho z) := by
  unfold transform
  simp_rw [shifted_integrand]
  rw [MeasureTheory.integral_const_mul, integral_add_right_eq_self]
  exact congrArg (fun x => Complex.exp (I*z*(L:ℂ))*x) (transform_base rho z)

/-- The real half-density coefficient of dilation by two. -/
def dyadicWeight : ℝ := Real.exp (-Real.log 2/2)

/-- The dyadic half-density coefficient is strictly positive. -/
theorem dyadicWeight_pos : 0 < dyadicWeight := Real.exp_pos _

/-- The dyadic half-density coefficient is at most one. -/
theorem dyadicWeight_le_one : dyadicWeight ≤ 1 := by
  rw [dyadicWeight, Real.exp_le_one_iff]
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The literal dyadic theta half-density, retaining both dilation terms. -/
def profile (rho : ℂ) (t : ℝ) : ℂ :=
  2 * baseProfile rho t - (dyadicWeight:ℂ) * baseProfile rho (t+Real.log 2)

/-- The complete multiplier of the two retained dilation terms. -/
def dyadicFactor (z : ℂ) : ℂ :=
  2 - (dyadicWeight:ℂ) * Complex.exp (I*z*(Real.log 2:ℂ))

private theorem profile_integrand (rho z : ℂ) (t : ℝ) :
    fourierIntegrand (profile rho) z t =
      2 * fourierIntegrand (baseProfile rho) z t -
        (dyadicWeight:ℂ) * fourierIntegrand (fun x => baseProfile rho (x+Real.log 2)) z t := by
  unfold fourierIntegrand profile
  ring

/-- The complete dyadic profile is integrable against every complex exponential twist. -/
theorem profile_integrable (rho z : ℂ) : Integrable (fourierIntegrand (profile rho) z) := by
  refine ((base_integrable rho z).const_mul 2 |>.sub
    ((shifted_base_integrable rho z (Real.log 2)).const_mul (dyadicWeight:ℂ))).congr
    (Filter.Eventually.of_forall fun t => (profile_integrand rho z t).symm)

/-- Exact whole-plane arithmetic transform of the dyadic theta profile. -/
theorem transform_profile (rho z : ℂ) :
    transform (profile rho) z = dyadicFactor z * xiCent (sourceArgument rho z) := by
  unfold transform
  simp_rw [profile_integrand]
  rw [integral_sub ((base_integrable rho z).const_mul 2)
    ((shifted_base_integrable rho z (Real.log 2)).const_mul (dyadicWeight:ℂ)),
    integral_const_mul, integral_const_mul]
  change 2 * transform (baseProfile rho) z -
    (dyadicWeight:ℂ) * transform (fun x => baseProfile rho (x+Real.log 2)) z = _
  rw [transform_base, transform_shifted_base, dyadicFactor]
  ring

/-- The constant dyadic term strictly dominates the oscillatory term on the real line. -/
theorem dyadicFactor_ne_zero_ofReal (t : ℝ) : dyadicFactor (t:ℂ) ≠ 0 := by
  intro h
  have he : (2:ℂ) = (dyadicWeight:ℂ) * Complex.exp (I*(t:ℂ)*(Real.log 2:ℂ)) :=
    sub_eq_zero.mp h
  have hn := congrArg norm he
  have hp : ‖Complex.exp (I*(t:ℂ)*(Real.log 2:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
      Real.exp_zero]
  rw [norm_mul, hp, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos dyadicWeight_pos] at hn
  norm_num at hn
  linarith [dyadicWeight_le_one]

/-- Half the ordinate of an actual Xi divisor copy. -/
def xiFrequency (q : XiZeroCopy) : ℝ := (q.1:ℂ).im/2

/-- At the source ordinate the centered Xi argument lies on the positive real exterior ray. -/
theorem sourceArgument_xiFrequency (q : XiZeroCopy) :
    sourceArgument (q.1:ℂ) (xiFrequency q : ℂ) = ((q.1:ℂ).re:ℂ)+1/2 := by
  apply Complex.ext
  · simp [sourceArgument, xiFrequency]
  · simp [sourceArgument, xiFrequency]
    ring

/-- The source transform at its ordinate retains its explicit exterior Xi factor. -/
theorem transform_profile_xiFrequency (q : XiZeroCopy) :
    transform (profile (q.1:ℂ)) (xiFrequency q : ℂ) =
      dyadicFactor (xiFrequency q : ℂ) * xiCent (((q.1:ℂ).re:ℂ)+1/2) := by
  rw [transform_profile, sourceArgument_xiFrequency]

/-- The actual source transform does not vanish at its own real ordinate. -/
theorem transform_profile_xiFrequency_ne_zero (q : XiZeroCopy) :
    transform (profile (q.1:ℂ)) (xiFrequency q : ℂ) ≠ 0 := by
  rw [transform_profile_xiFrequency]
  refine mul_ne_zero (dyadicFactor_ne_zero_ofReal _) (xiCent_ne_zero_of_half_lt_re ?_)
  have h := (xi_divisor_support_re_mem_open_unit q.1).1
  simpa using h

/-- The half-density weight and translation phase combine into one exponential. -/
theorem dyadicFactor_eq_exp (z : ℂ) :
    dyadicFactor z = 2 - Complex.exp ((I*z-1/2)*(Real.log 2:ℂ)) := by
  unfold dyadicFactor dyadicWeight
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The dyadic multiplier preserves the native mean moment exactly. -/
theorem dyadicFactor_mean : dyadicFactor (-I/2) = 1 := by
  rw [dyadicFactor_eq_exp]
  have he : I*(-I/2)-(1/2:ℂ) = 0 := by linear_combination -I_sq/2
  rw [he]
  norm_num

/-- The native mean moment of the complete dyadic source is exactly `xi rho`. -/
theorem transform_profile_mean (rho : ℂ) :
    transform (profile rho) (-I/2) = xi rho := by
  rw [transform_profile, dyadicFactor_mean, one_mul]
  have he : sourceArgument rho (-I/2) = rho-1/2 := by
    unfold sourceArgument
    linear_combination I_sq
  rw [he]
  change xi ((1/2:ℂ)+(rho-1/2)) = _
  congr 1
  ring

/-- The actual Xi source has zero native mean moment. -/
theorem transform_profile_mean_xiZero (q : XiZeroCopy) :
    transform (profile (q.1:ℂ)) (-I/2) = 0 := by
  rw [transform_profile_mean]
  exact xi_eq_zero_of_mem_divisor_support q.1

/-- The reflected source correlation, as a literal convolution integral. -/
def hankelCorrelation (rho : ℂ) (v : ℝ) : ℂ :=
  ∫ t : ℝ, conj (profile rho t) * profile rho (v-t)

private theorem conj_integrand (rho z : ℂ) (t : ℝ) :
    fourierIntegrand (fun x => conj (profile rho x)) z t =
      conj (fourierIntegrand (profile rho) (-conj z) t) := by
  unfold fourierIntegrand
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I,
    Complex.conj_ofReal, conj_conj]
  congr 2
  ring

/-- The conjugated source also has every complex exponential moment. -/
theorem conjugate_profile_integrable (rho z : ℂ) :
    Integrable (fourierIntegrand (fun t => conj (profile rho t)) z) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
    (profile_integrable rho (-conj z))
  exact h.congr (Filter.Eventually.of_forall fun t => (conj_integrand rho z t).symm)

private theorem hankel_integrand (rho z : ℂ) (v : ℝ) :
    fourierIntegrand (hankelCorrelation rho) z v =
      ((fourierIntegrand (fun t => conj (profile rho t)) z) ⋆[
        ContinuousLinearMap.mul ℂ ℂ] (fourierIntegrand (profile rho) z)) v := by
  unfold fourierIntegrand hankelCorrelation convolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change _ = (Complex.exp (-I*z*(t:ℂ))*conj (profile rho t)) *
    (Complex.exp (-I*z*((v-t:ℝ):ℂ))*profile rho (v-t))
  have he : Complex.exp (-I*z*(v:ℂ)) =
      Complex.exp (-I*z*(t:ℂ))*Complex.exp (-I*z*((v-t:ℝ):ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Every exponential twist of the full reflected source correlation is integrable. -/
theorem hankel_integrable (rho z : ℂ) :
    Integrable (fourierIntegrand (hankelCorrelation rho) z) := by
  exact ((conjugate_profile_integrable rho z).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (profile_integrable rho z)).congr
      (Filter.Eventually.of_forall fun v => (hankel_integrand rho z v).symm)

/-- The full reflected correlation has the exact conjugate-reflected product transform. -/
theorem transform_hankelCorrelation (rho z : ℂ) :
    transform (hankelCorrelation rho) z =
      conj (transform (profile rho) (-conj z)) * transform (profile rho) z := by
  unfold transform
  simp_rw [hankel_integrand]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (conjugate_profile_integrable rho z) (profile_integrable rho z)]
  change (∫ t : ℝ, fourierIntegrand (fun x => conj (profile rho x)) z t) * _ = _
  simp_rw [conj_integrand]
  rw [integral_conj]

/-- The reflected product transform contains both explicit dyadic and Xi factors. -/
theorem transform_hankelCorrelation_eq_xiCent (rho z : ℂ) :
    transform (hankelCorrelation rho) z =
      conj (dyadicFactor (-conj z) * xiCent (sourceArgument rho (-conj z))) *
        (dyadicFactor z * xiCent (sourceArgument rho z)) := by
  rw [transform_hankelCorrelation, transform_profile, transform_profile]

/-- The reflected correlation inherits the vanishing actual Xi mean moment. -/
theorem transform_hankelCorrelation_mean_xiZero (q : XiZeroCopy) :
    transform (hankelCorrelation (q.1:ℂ)) (-I/2) = 0 := by
  rw [transform_hankelCorrelation, transform_profile_mean_xiZero, mul_zero]

/-- The translation correlation of the literal dyadic theta profile. -/
def autocorrelation (rho : ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, conj (profile rho t) * profile rho (t+u)

private theorem reflected_conj_integrand (rho z : ℂ) (t : ℝ) :
    fourierIntegrand (fun x => conj (profile rho (-x))) z t =
      conj (fourierIntegrand (profile rho) (conj z) (-t)) := by
  unfold fourierIntegrand
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I,
    Complex.conj_ofReal, conj_conj, Complex.ofReal_neg]
  congr 2
  ring

private theorem reflected_conj_integrable (rho z : ℂ) :
    Integrable (fourierIntegrand (fun t => conj (profile rho (-t))) z) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
    ((profile_integrable rho (conj z)).comp_neg)
  exact h.congr (Filter.Eventually.of_forall fun t =>
    (reflected_conj_integrand rho z t).symm)

private theorem autocorrelation_eq_convolution (rho : ℂ) (u : ℝ) :
    autocorrelation rho u =
      ((fun t => conj (profile rho (-t))) ⋆[
        ContinuousLinearMap.mul ℂ ℂ] (profile rho)) u := by
  unfold autocorrelation convolution
  have h := MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => conj (profile rho t) * profile rho (t+u))
  rw [← h]
  apply integral_congr_ae
  filter_upwards with t
  change conj (profile rho (-t)) * profile rho (-t+u) = _
  rw [show -t+u = u-t by ring]
  rfl

private theorem autocorrelation_integrand (rho z : ℂ) (u : ℝ) :
    fourierIntegrand (autocorrelation rho) z u =
      ((fourierIntegrand (fun t => conj (profile rho (-t))) z) ⋆[
        ContinuousLinearMap.mul ℂ ℂ] (fourierIntegrand (profile rho) z)) u := by
  unfold fourierIntegrand
  rw [autocorrelation_eq_convolution]
  unfold convolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change _ = (Complex.exp (-I*z*(t:ℂ))*conj (profile rho (-t))) *
    (Complex.exp (-I*z*((u-t:ℝ):ℂ))*profile rho (u-t))
  change Complex.exp (-I*z*(u:ℂ)) * (conj (profile rho (-t))*profile rho (u-t)) = _
  have he : Complex.exp (-I*z*(u:ℂ)) =
      Complex.exp (-I*z*(t:ℂ))*Complex.exp (-I*z*((u-t:ℝ):ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Every exponential twist of the full translation correlation is integrable. -/
theorem autocorrelation_integrable (rho z : ℂ) :
    Integrable (fourierIntegrand (autocorrelation rho) z) := by
  exact ((reflected_conj_integrable rho z).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (profile_integrable rho z)).congr
      (Filter.Eventually.of_forall fun u => (autocorrelation_integrand rho z u).symm)

/-- The translation correlation has the exact conjugate product transform on the whole plane. -/
theorem transform_autocorrelation (rho z : ℂ) :
    transform (autocorrelation rho) z =
      conj (transform (profile rho) (conj z)) * transform (profile rho) z := by
  unfold transform
  simp_rw [autocorrelation_integrand]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (reflected_conj_integrable rho z) (profile_integrable rho z)]
  change (∫ t : ℝ, fourierIntegrand (fun x => conj (profile rho (-x))) z t) * _ = _
  simp_rw [reflected_conj_integrand]
  rw [integral_conj, integral_neg_eq_self]

/-- The translation product transform retains both explicit arithmetic factors. -/
theorem transform_autocorrelation_eq_xiCent (rho z : ℂ) :
    transform (autocorrelation rho) z =
      conj (dyadicFactor (conj z) * xiCent (sourceArgument rho (conj z))) *
        (dyadicFactor z * xiCent (sourceArgument rho z)) := by
  rw [transform_autocorrelation, transform_profile, transform_profile]

/-- The translation correlation inherits the vanishing actual Xi mean moment. -/
theorem transform_autocorrelation_mean_xiZero (q : XiZeroCopy) :
    transform (autocorrelation (q.1:ℂ)) (-I/2) = 0 := by
  rw [transform_autocorrelation, transform_profile_mean_xiZero, mul_zero]

/-- The translation correlation has strictly positive real transform at every actual source ordinate. -/
theorem transform_autocorrelation_xiFrequency_re_pos (q : XiZeroCopy) :
    0 < (transform (autocorrelation (q.1:ℂ)) (xiFrequency q:ℂ)).re := by
  rw [transform_autocorrelation, Complex.conj_ofReal]
  have h := transform_profile_xiFrequency_ne_zero q
  rw [mul_comm, Complex.mul_conj]
  simpa using Complex.normSq_pos.mpr h

end
end RHTower.SelbergThetaDilationTransform
