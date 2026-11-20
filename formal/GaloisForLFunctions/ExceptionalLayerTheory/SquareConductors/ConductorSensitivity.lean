import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFirstMomentSeenByTheIntegratedConductorSpline
import GaloisForLFunctions.HTGeometry.HyperbolicModulus
import GaloisForLFunctions.RHTower.MellinIteratedDerivative

/-!
# Frequency response of the integrated conductor spline

The logarithmic phase of a power input enters two factors: one from the
dyadic difference, and one from the eight spline convolutions. Their
moduli give a two-sided estimate uniform in height. Logarithmic weights
detect the exact vanishing order of either factor.
-/

noncomputable section
open Filter MeasureTheory Complex
open scoped Topology
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment

private theorem multiplier (r : ℂ) : mellin squarePrimeWeight r =
    (2-cexp ((r-1/2)*(Real.log 4:ℝ)))*sinhRatio (r-1/2)^8 := by
  have h := power_reading_formula (r+1) (X := 1) zero_lt_one
  rw [power_reading _ zero_lt_one] at h
  simpa only [Complex.ofReal_one,Complex.one_cpow,one_mul,add_sub_cancel_right,
    show r+1-3/2=r-1/2 by ring] using h

/-- Multiplication by the eighth power of the distance from the removable
point separates the norm into a dyadic chord and a hyperbolic sine. -/
theorem normalized_response (z : ℂ) :
    ‖z‖^8 * ‖mellin squarePrimeWeight (z+1/2)‖ =
      ‖2-cexp (z*(Real.log 4:ℝ))‖ * ‖Complex.sinh z‖^8 := by
  rw [multiplier,add_sub_cancel_right,norm_mul,norm_pow]
  by_cases hz : z = 0
  · simp [hz]
  · rw [sinhRatio,if_neg hz,norm_div,div_pow]
    field_simp [norm_ne_zero_iff.mpr hz]

private theorem sinh_norm_sq (z : ℂ) :
    ‖Complex.sinh z‖^2 = Real.sinh z.re^2 + Real.sin z.im^2 := by
  have he : (z.re:ℂ)-((-z.im:ℝ):ℂ)*I=z := by
    simp only [Complex.ofReal_neg,neg_mul,sub_neg_eq_add,Complex.re_add_im]
  have hh := HTGeometry.normSq_sinh_sub_mul_I z.re (-z.im)
  rw [he,Real.cos_neg,Real.sin_neg,neg_sq,Real.cosh_sq,Complex.normSq_eq_norm_sq] at hh
  rw [hh]
  linear_combination (Real.sinh z.re)^2 * Real.sin_sq_add_cos_sq z.im

private theorem sinh_bounds (z : ℂ) :
    |Real.sinh z.re| ≤ ‖Complex.sinh z‖ ∧ ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have h := sinh_norm_sq z
  constructor
  · nlinarith only [h,sq_abs (Real.sinh z.re),sq_nonneg (Real.sin z.im),norm_nonneg (Complex.sinh z)]
  · nlinarith only [h,Real.cosh_sq z.re,Real.sin_sq_add_cos_sq z.im,
      sq_nonneg (Real.cos z.im),Real.cosh_pos z.re]

/-- Uniform upper and lower vertical-line bounds at the exact eighth
power. The lower envelope is positive away from the two exceptional
vertical lines. -/
theorem response_envelopes (z : ℂ) :
    |2-Real.exp (z.re*Real.log 4)| * |Real.sinh z.re|^8 ≤
      ‖z‖^8 * ‖mellin squarePrimeWeight (z+1/2)‖ ∧
    ‖z‖^8 * ‖mellin squarePrimeWeight (z+1/2)‖ ≤
      (2+Real.exp (z.re*Real.log 4))*Real.cosh z.re^8 := by
  rw [normalized_response]
  let w := cexp (z*(Real.log 4:ℝ))
  have hw : ‖w‖ = Real.exp (z.re*Real.log 4) := by
    simp only [w,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have ht : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
  have hl := abs_norm_sub_norm_le (2:ℂ) w
  have hu := norm_sub_le (2:ℂ) w
  rw [ht,hw] at hl hu
  obtain ⟨hs₁,hs₂⟩ := sinh_bounds z
  exact ⟨mul_le_mul hl (pow_le_pow_left₀ (abs_nonneg _) hs₁ 8) (by positivity) (norm_nonneg _),
    mul_le_mul hu (pow_le_pow_left₀ (norm_nonneg _) hs₂ 8) (by positivity) (by positivity)⟩

private theorem rapid : _root_.RHTower.MellinRapid squarePrimeWeight := by
  refine ⟨?_,?_,?_⟩
  · exact (show ContinuousOn squarePrimeWeight (Set.Ioi (0:ℝ)) from
      fun x hx => (continuousAt_squarePrimeWeight hx).continuousWithinAt).locallyIntegrableOn
      measurableSet_Ioi
  · intro a
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (Real.exp (8+Real.log 4))] with x hx
    rw [squarePrimeWeight_zero_outside ((Real.exp_pos _).trans hx) (fun h => hx.not_ge h.2),norm_zero]
    positivity
  · intro b _
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (Real.exp_pos (-8)))] with x hx hx'
    rw [squarePrimeWeight_zero_outside hx (fun h => hx'.not_ge h.1),norm_zero]
    positivity

/-- Multiplicative log moments at scale X are the derivatives of the
actual Mellin multiplier. Centering the logarithm at X removes every
contribution from differentiating the dilation itself. -/
theorem log_power_reading (r : ℂ) (hr : 0 < r.re) (j : ℕ) {X : ℝ} (hX : 0 < X) :
    reading X (fun x => (x:ℂ)^(r+1) * (Real.log (x/X):ℂ)^j) =
      (X:ℂ)^(r+1) * iteratedDeriv j (mellin squarePrimeWeight) r := by
  rw [_root_.RHTower.iteratedDeriv_mellin rapid j hr,reading,mellin,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  have htz := Complex.ofReal_ne_zero.mpr ht'.ne'
  change density t * (((X*t:ℝ):ℂ)^(r+1) * (Real.log (X*t/X):ℂ)^j) =
    (X:ℂ)^(r+1) * ((t:ℂ)^(r-1) * ((Real.log t)^j • squarePrimeWeight t))
  rw [mul_div_cancel_left₀ _ hX.ne',density,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hX.le ht'.le,show r-1=(r+1)+(-(2:ℂ)) by ring,
    Complex.cpow_add (r+1) (-(2:ℂ)) htz,Complex.cpow_neg,Complex.cpow_two,
    Complex.real_smul,Complex.ofReal_pow]
  ring

private def dyadic (r : ℂ) := 2-cexp ((r-1/2)*(Real.log 4:ℝ))
private def sinc (r : ℂ) := Complex.sinh (r-1/2)/(r-1/2)

private theorem germ_factorization {r : ℂ} (hr : r-1/2 ≠ 0) :
    mellin squarePrimeWeight =ᶠ[𝓝 r] dyadic*sinc^8 := by
  filter_upwards [(continuous_id.sub continuous_const).continuousAt.eventually_ne hr] with u hu
  have hu' : u-1/2 ≠ 0 := hu
  simpa only [multiplier,sinhRatio,if_neg hu',Pi.mul_apply,Pi.pow_apply,dyadic,sinc]

private theorem dyadic_order (r : ℂ) : analyticOrderAt dyadic r = if dyadic r=0 then 1 else 0 := by
  have h := (((hasDerivAt_id r).sub_const (1/2)).mul_const (Real.log 4:ℂ)).cexp
  have hd : HasDerivAt dyadic (-cexp ((r-1/2)*(Real.log 4:ℝ))*(Real.log 4:ℝ)) r := by
    have h2 := h.const_sub 2
    simp only [id_eq,one_mul,neg_mul] at h2 ⊢
    exact h2
  have ha : AnalyticAt ℂ dyadic r := by unfold dyadic; fun_prop
  split_ifs with hzero
  · exact ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero (hd.deriv ▸ mul_ne_zero
      (neg_ne_zero.mpr (Complex.exp_ne_zero _)) (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))
  · exact ha.analyticOrderAt_eq_zero.mpr hzero

private theorem sinc_order {r : ℂ} (hr : r-1/2 ≠ 0) : analyticOrderAt sinc r =
    if Complex.sinh (r-1/2)=0 then 1 else 0 := by
  have ha : AnalyticAt ℂ sinc r := by unfold sinc; fun_prop (disch := assumption)
  split_ifs with hz
  · have hc : Complex.cosh (r-1/2) ≠ 0 := by
      intro hc
      have h := Complex.cosh_sq (r-1/2)
      rw [hc,hz] at h
      norm_num at h
    have hd := (Complex.hasDerivAt_sinh (r-1/2)).comp r ((hasDerivAt_id r).sub_const (1/2))
    have he := (hd.div ((hasDerivAt_id r).sub_const (1/2)) hr).deriv
    simp only [id_eq,Function.comp_apply,hz,one_mul,mul_one,zero_mul,sub_zero] at he
    exact ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by rw [sinc,hz,zero_div])
      (he ▸ div_ne_zero (mul_ne_zero hc hr) (pow_ne_zero 2 hr))
  · exact ha.analyticOrderAt_eq_zero.mpr (div_ne_zero hz hr)

/-- Exact analytic order at every noncentral frequency, showing separately
the contribution of the dyadic difference and the eight spline factors. -/
theorem response_order {r : ℂ} (hr : r-1/2 ≠ 0) :
    analyticOrderAt (mellin squarePrimeWeight) r =
      (if 2-cexp ((r-1/2)*(Real.log 4:ℝ))=0 then 1 else 0) +
        (if Complex.sinh (r-1/2)=0 then 8 else 0) := by
  have h₁ : AnalyticAt ℂ dyadic r := by unfold dyadic; fun_prop
  have h₂ : AnalyticAt ℂ sinc r := by unfold sinc; fun_prop (disch := assumption)
  rw [analyticOrderAt_congr (germ_factorization hr),analyticOrderAt_mul h₁ (h₂.pow 8),
    analyticOrderAt_pow h₂,dyadic_order,sinc_order hr]
  unfold dyadic
  split_ifs <;> norm_num

/-- If the multiplier has order m then the first nonvanishing observation
of the log-weighted power occurs at exactly logarithmic degree m, at
every positive observation scale. -/
theorem first_visible_log_degree {r : ℂ} (hr : 0 < r.re) (m : ℕ) {X : ℝ} (hX : 0 < X) :
    analyticOrderAt (mellin squarePrimeWeight) r = m ↔
      (∀ j < m, reading X (fun x => (x:ℂ)^(r+1)*(Real.log (x/X):ℂ)^j)=0) ∧
      reading X (fun x => (x:ℂ)^(r+1)*(Real.log (x/X):ℂ)^m) ≠ 0 := by
  have ha := differentiable_mellin_squarePrimeWeight.analyticAt r
  have hx := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne') :
    (X:ℂ) ≠ 0 ∨ r+1=0)
  simp only [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha,log_power_reading r hr _ hX,
    mul_ne_zero_iff,ne_eq,hx,not_false_eq_true,true_and]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment
