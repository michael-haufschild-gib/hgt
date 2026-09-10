import GaloisForLFunctions.RHTower.SelbergThetaTotientHankel
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalArithmetic
import Mathlib.Analysis.MellinTransform

/-!
# Mellin transform of the literal horizontal theta source

The complete horizontal mean, including its parabolic term and every totient-weighted
reflected row, has Mellin transform
`xi (z + 3/2) * (1 + reflectedCompletedLambda (z + 1) / reflectedCompletedLambda (z + 2))`
after the square-height substitution, for `0 < z.re`.

Absolute row bounds justify the full sum/integral exchange. The final `HasMellin` theorem
asserts both absolute convergence and equality for the actual source. Transfer to the
spectral boundary and cancellation of the native scalar response remain separate questions.
-/

open Complex MeasureTheory Set Function
open scoped ComplexConjugate FourierTransform
namespace RHTower.SelbergThetaHorizontalTransform
open SelbergThetaDilationTransform GaloisForLFunctions.HTGeometry
noncomputable section

private theorem base_measurable : Measurable (baseProfile (-1/2)) := by
  have ht := contDiff_thetaCuspFullSource.continuous.measurable
  unfold baseProfile
  fun_prop

private theorem shifted_product_integrable {f k : ℝ → ℂ} {a : ℝ → ℝ}
    (hf : Integrable f) (hmf : Measurable f) (hk : Integrable k)
    (hmk : Measurable k) (ha : Measurable a) :
    Integrable (fun p : ℝ × ℝ => k p.1 * f (p.2-a p.1)) (volume.prod volume) := by
  apply (integrable_prod_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun x => (hf.comp_sub_right (a x)).const_mul (k x)
  · have he (x : ℝ) : (∫ v : ℝ, ‖k x * f (v-a x)‖) =
        ‖k x‖ * ∫ v : ℝ, ‖f v‖ := by
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_sub_right_eq_self (fun v : ℝ => ‖f v‖)]
    simp_rw [he]
    exact hk.norm.mul_const _

private theorem integral_shifted_product {f k : ℝ → ℂ} {a : ℝ → ℝ}
    (hf : Integrable f) (hmf : Measurable f) (hk : Integrable k)
    (hmk : Measurable k) (ha : Measurable a) :
    (∫ v : ℝ, ∫ x : ℝ, k x * f (v-a x)) = (∫ x : ℝ, k x) * ∫ v : ℝ, f v := by
  have hs : Integrable (Function.uncurry (fun v x : ℝ => k x * f (v-a x)))
      (volume.prod volume) := (shifted_product_integrable hf hmf hk hmk ha).swap
  rw [integral_integral_swap hs]
  simp_rw [integral_const_mul, integral_sub_right_eq_self]
  rw [integral_mul_const]

private theorem norm_integral_shifted_product_le {f k : ℝ → ℂ} {a : ℝ → ℝ}
    (hf : Integrable f) (hmf : Measurable f) (hk : Integrable k)
    (hmk : Measurable k) (ha : Measurable a) :
    (∫ v : ℝ, ‖∫ x : ℝ, k x * f (v-a x)‖) ≤
      (∫ x : ℝ, ‖k x‖) * ∫ v : ℝ, ‖f v‖ := by
  have hi := shifted_product_integrable hf hmf hk hmk ha
  calc
    _ ≤ ∫ v : ℝ, ∫ x : ℝ, ‖k x * f (v-a x)‖ :=
      integral_mono hi.integral_prod_right.norm hi.integral_norm_prod_right
        (fun v => norm_integral_le_integral_norm _)
    _ = ∫ x : ℝ, ∫ v : ℝ, ‖k x * f (v-a x)‖ := by
      have hs : Integrable (Function.uncurry (fun v x : ℝ => ‖k x * f (v-a x)‖))
          (volume.prod volume) := hi.norm.swap
      exact integral_integral_swap hs
    _ = _ := by
      simp_rw [norm_mul, integral_const_mul,
        integral_sub_right_eq_self (fun v : ℝ => ‖f v‖)]
      rw [integral_mul_const]

private def unitHeight : D4BMUpperHalfPlaneCoordinate := ⟨0,1,by norm_num⟩

private def shift (q : ℕ+) (x : ℝ) : ℝ :=
  2 * Real.log (q:ℕ) + Real.log (1+x^2)

private def tiltedBase (P : D4BMEisensteinAbsoluteConvergenceParameter) :=
  fourierIntegrand (baseProfile (-1/2)) (-I*(P.s-1/2))

private def archKernel (P : D4BMEisensteinAbsoluteConvergenceParameter) :=
  d4BMCauchyPowerKernel unitHeight P.s

private theorem archKernel_eq_exp (P : D4BMEisensteinAbsoluteConvergenceParameter) (x : ℝ) :
    archKernel P x = Complex.exp (-P.s * (Real.log (1+x^2):ℂ)) := by
  have hx : 0 < 1+x^2 := by positivity
  change ((1^2+x^2:ℝ):ℂ)^(-P.s) = _
  simp only [one_pow]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  congr 1
  ring

private theorem archKernel_measurable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Measurable (archKernel P) := by
  change Measurable (fun x => archKernel P x)
  simp_rw [archKernel_eq_exp]
  fun_prop

private theorem tiltedBase_measurable
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : Measurable (tiltedBase P) := by
  unfold tiltedBase fourierIntegrand
  have hm := base_measurable
  fun_prop

private theorem zeroRamanujan_eq_totient (Q : CGLPositiveModulus) :
    cglRamanujanAdditiveSum Q (0 : ZMod Q.value) = (Q.value.totient:ℂ) := by
  classical
  let e : (ZMod Q.value)ˣ ≃ {x : ZMod Q.value // IsUnit x} :=
    { toFun := fun u => ⟨u, u.isUnit⟩
      invFun := fun x => x.prop.unit
      left_inv := fun u => IsUnit.unit_of_val_units u.isUnit
      right_inv := fun x => Subtype.ext (IsUnit.unit_spec x.prop) }
  have hc := Fintype.card_congr e
  simp only [cglRamanujanAdditiveSum, mul_zero, Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype, ← hc, ZMod.card_units_eq_totient]
  simp

private theorem arithmeticTerm_exp (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    d4BMZeroRamanujanPNatTerm P q = ((q:ℕ).totient:ℂ) *
      Complex.exp (-(2*P.s) * (Real.log (q:ℕ):ℂ)) := by
  rw [d4BMZeroRamanujanPNatTerm, zeroRamanujan_eq_totient]
  change ((q:ℕ).totient:ℂ) * (((q:ℕ):ℝ):ℂ)^(-(2*P.s)) = _
  have hq : (0:ℝ) < (q:ℕ) := by exact_mod_cast q.pos
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast q.ne_zero), ← Complex.ofReal_log hq.le]
  congr 2
  ring

private theorem arithmeticTerm_summable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (d4BMZeroRamanujanPNatTerm P) := by
  have hw : 2 < (2*P.s).re := by
    norm_num [Complex.mul_re]
    linarith [P.re_gt_one]
  have hs := ArithmeticFunction.LSeriesSummable_mul
    (d4BMIdentityArithmeticC_LSeriesSummable hw)
    (d4BMMoebiusArithmeticC_LSeriesSummable (lt_trans one_lt_two hw))
  have hp := hs.subtype (fun n : ℕ => 0 < n)
  apply hp.congr
  intro q
  change LSeries.term d4BMZeroRamanujanArithmeticC (2*P.s) (q:ℕ) = _
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt q.prop)]
  have he := d4BM_zeroRamanujanArithmeticC_eq_cgl (d4BMPositiveModulusOfPNat q)
  change d4BMZeroRamanujanArithmeticC (q:ℕ) = _ at he
  rw [he, div_eq_mul_inv, ← Complex.cpow_neg]
  rfl

/-- A complete denominator row of the actual reflected theta source. The half-density
weight is `1 / (q * sqrt (1+x²))`, written in exponential form. -/
def row (q : ℕ+) (v : ℝ) : ℂ :=
  ((q:ℕ).totient:ℂ) * ∫ x : ℝ,
    Complex.exp (-(shift q x:ℂ)/2) * baseProfile (-1/2) (v-shift q x)

private theorem row_weight (q : ℕ+) (x : ℝ) :
    Complex.exp (-(shift q x:ℂ)/2) =
      ((((q:ℕ):ℝ):ℂ) * (Real.sqrt (1+x^2):ℂ))⁻¹ := by
  have hx : 0 < 1+x^2 := by positivity
  have hq : (0:ℝ) < (q:ℕ) := by exact_mod_cast q.pos
  have heq : Complex.exp (Real.log (q:ℕ):ℂ) = (((q:ℕ):ℝ):ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hq]
  have hes : Complex.exp ((Real.log (1+x^2):ℂ)/2) = (Real.sqrt (1+x^2):ℂ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have he : -(shift q x:ℂ)/2 = -((Real.log (q:ℕ):ℂ)+(Real.log (1+x^2):ℂ)/2) := by
    unfold shift
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_add, heq, hes]

/-- The row is the literal totient-weighted square-root integral appearing in the horizontal theta mean. -/
theorem row_eq_totient_integral (q : ℕ+) (v : ℝ) :
    row q v = (((q:ℕ).totient:ℂ) / (((q:ℕ):ℝ):ℂ)) *
      ∫ x : ℝ, baseProfile (-1/2)
        (v - 2*Real.log (q:ℕ) - Real.log (1+x^2)) / (Real.sqrt (1+x^2):ℂ) := by
  unfold row
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [row_weight]
  have he : v-shift q x = v-2*Real.log (q:ℕ)-Real.log (1+x^2) := by unfold shift; ring
  rw [he]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

/-- The full totient-weighted reflected source, retaining all positive denominators. -/
def kernel (v : ℝ) : ℂ := ∑' q : ℕ+, row q v

private theorem tiltedBase_eq
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (v : ℝ) :
    tiltedBase P v =
      Complex.exp (-(P.s-1/2)*(v:ℂ)) * baseProfile (-1/2) v := by
  unfold tiltedBase fourierIntegrand
  congr 2
  linear_combination I_sq * (P.s-1/2)*(v:ℂ)

private theorem row_integrand
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) (v : ℝ) :
    fourierIntegrand (row q) (-I*(P.s-1/2)) v =
      d4BMZeroRamanujanPNatTerm P q * ∫ x : ℝ,
        archKernel P x * tiltedBase P (v-shift q x) := by
  have he : -I*(-I*(P.s-1/2)) = -(P.s-1/2) := by
    linear_combination I_sq*(P.s-1/2)
  unfold fourierIntegrand row
  rw [he, arithmeticTerm_exp]
  simp only [mul_assoc]
  rw [mul_left_comm (Complex.exp _) ((q:ℕ).totient:ℂ)]
  congr 1
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [archKernel_eq_exp, tiltedBase_eq]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  unfold shift
  push_cast
  ring

private theorem row_product_integrable
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    Integrable (fun p : ℝ × ℝ => archKernel P p.1 *
      tiltedBase P (p.2-shift q p.1)) (volume.prod volume) := by
  exact shifted_product_integrable (base_integrable (-1/2) _)
    (tiltedBase_measurable P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

/-- Every row is absolutely integrable on each strictly convergent Laplace line. -/
theorem row_integrable
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    Integrable (fourierIntegrand (row q) (-I*(P.s-1/2))) := by
  change Integrable (fun v => fourierIntegrand (row q) (-I*(P.s-1/2)) v)
  simp_rw [row_integrand]
  exact (row_product_integrable P q).integral_prod_right.const_mul _

private theorem row_integral_norm_le
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    (∫ v : ℝ, ‖fourierIntegrand (row q) (-I*(P.s-1/2)) v‖) ≤
      ‖d4BMZeroRamanujanPNatTerm P q‖ *
        ((∫ x : ℝ, ‖archKernel P x‖) * ∫ v : ℝ, ‖tiltedBase P v‖) := by
  simp_rw [row_integrand, norm_mul]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_integral_shifted_product_le (base_integrable (-1/2) _)
    (tiltedBase_measurable P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

/-- Absolute row norms are summable, so exchanging the full totient sum and transform is valid. -/
theorem row_norm_summable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (fun q : ℕ+ => ∫ v : ℝ,
      ‖fourierIntegrand (row q) (-I*(P.s-1/2)) v‖) := by
  exact Summable.of_nonneg_of_le (fun q => integral_nonneg (fun v => norm_nonneg _))
    (row_integral_norm_le P) ((arithmeticTerm_summable P).norm.mul_right _)

/-- Exact transform of one complete denominator row, with its actual arithmetic coefficient. -/
private theorem transform_row
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    transform (row q) (-I*(P.s-1/2)) =
      d4BMZeroRamanujanPNatTerm P q *
        ((∫ x : ℝ, archKernel P x) * transform (baseProfile (-1/2)) (-I*(P.s-1/2))) := by
  unfold transform
  simp_rw [row_integrand]
  rw [integral_const_mul]
  congr 1
  exact integral_shifted_product (base_integrable (-1/2) _)
    (tiltedBase_measurable P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

private theorem kernel_integrand (z : ℂ) (v : ℝ) :
    fourierIntegrand kernel z v = ∑' q : ℕ+, fourierIntegrand (row q) z v := by
  unfold fourierIntegrand kernel
  exact tsum_mul_left.symm

/-- The full reflected theta kernel is absolutely integrable at `-I * (P.s - 1/2)` for `Re(P.s) > 1`. -/
theorem kernel_integrable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Integrable (fourierIntegrand kernel (-I*(P.s-1/2))) := by
  change Integrable (fun v => fourierIntegrand kernel (-I*(P.s-1/2)) v)
  simp_rw [kernel_integrand]
  exact integrable_tsum_of_summable_integral_norm (row_integrable P) (row_norm_summable P)

private theorem transform_kernel_factored
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform kernel (-I*(P.s-1/2)) =
      ((∫ x : ℝ, archKernel P x) *
        (riemannZeta (2*P.s-1) / riemannZeta (2*P.s))) *
          transform (baseProfile (-1/2)) (-I*(P.s-1/2)) := by
  unfold transform
  simp_rw [kernel_integrand]
  rw [integral_tsum_eq_tsum_integral_of_summable_integral_norm
    (row_integrable P) (row_norm_summable P)]
  change (∑' q : ℕ+, transform (row q) (-I*(P.s-1/2))) = _
  simp_rw [transform_row]
  rw [tsum_mul_right, tsum_d4BMZeroRamanujanPNatTerm_eq_zetaRatio]
  unfold transform
  ring

/-- Completed transform of the literal all-denominator reflected theta source. -/
theorem transform_kernel_completed
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    reflectedCompletedLambda (2*P.s) * transform kernel (-I*(P.s-1/2)) =
      reflectedCompletedLambda (2*P.s-1) *
        transform (baseProfile (-1/2)) (-I*(P.s-1/2)) := by
  have he := d4BM_completedZeroWeylFactor_eq_reflectedConstantTerm unitHeight P
  have hf : 𝓕 (d4BMCauchyPowerKernel unitHeight P.s) 0 = ∫ x : ℝ, archKernel P x := by
    rw [Real.fourier_eq]
    simp [archKernel]
  rw [hf] at he
  simp only [unitHeight, Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one] at he
  rw [transform_kernel_factored, ← mul_assoc, he]

/-- Exact completed-zeta ratio multiplying the full reflected theta source. -/
theorem transform_kernel (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform kernel (-I*(P.s-1/2)) =
      (reflectedCompletedLambda (2*P.s-1) / reflectedCompletedLambda (2*P.s)) *
        transform (baseProfile (-1/2)) (-I*(P.s-1/2)) := by
  have hn : reflectedCompletedLambda (2*P.s) ≠ 0 :=
    D4BMModularCore.cuspCompletedLambda_ne_zero (by
      norm_num [Complex.mul_re]
      linarith [P.re_gt_one])
  apply (mul_left_cancel₀ hn)
  rw [transform_kernel_completed]
  field_simp

private theorem base_apply (v : ℝ) :
    baseProfile (-1/2) v = (1/2:ℂ)*(thetaCuspFullSource (v/2):ℂ) := by
  norm_num [baseProfile]

private theorem positiveProfile_exp (v : ℝ) :
    (SelbergThetaNativeSource.positiveProfile (Real.exp v):ℂ) =
      2*(Real.exp (v/2):ℂ)*baseProfile (-1/2) v := by
  rw [SelbergThetaNativeSource.positiveProfile,Real.log_exp,base_apply]
  push_cast
  ring

private theorem positiveProfile_exp_neg (v : ℝ) :
    (SelbergThetaNativeSource.positiveProfile (Real.exp (-v)):ℂ) =
      2*(Real.exp (-v/2):ℂ)*baseProfile (-1/2) v := by
  rw [positiveProfile_exp,base_apply,base_apply]
  rw [neg_div,thetaCuspFullSource_neg]

private theorem exp_shift (c : ℕ+) (x : ℝ) :
    Real.exp (shift c x) = ((c:ℕ):ℝ)^2*(1+x^2) := by
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  unfold shift
  rw [show 2*Real.log (c:ℕ) = Real.log (c:ℕ)+Real.log (c:ℕ) by ring,
    Real.exp_add,Real.exp_add,Real.exp_log hc,
    Real.exp_log (by positivity : 0 < 1+x^2)]
  ring

private theorem archProfile_scaled (v : ℝ) (c : ℕ+) (x : ℝ) :
    SelbergThetaHorizontalArithmetic.archProfile (Real.exp (-v)) c (Real.exp (-v)*x) =
      2*(Real.exp ((v-shift c x)/2):ℂ)*baseProfile (-1/2) (v-shift c x) := by
  have hc : ((c:ℕ):ℝ) ≠ 0 := by exact_mod_cast c.ne_zero
  have hx : (1+x^2:ℝ) ≠ 0 := by positivity
  have he : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
  have hy :
      Real.exp (-v) / (((c:ℕ):ℝ)^2*((Real.exp (-v))^2+(Real.exp (-v)*x)^2)) =
        Real.exp (v-shift c x) := by
    rw [Real.exp_sub,exp_shift,Real.exp_neg]
    field_simp
  change (SelbergThetaNativeSource.positiveProfile
    (Real.exp (-v) / (((c:ℕ):ℝ)^2*((Real.exp (-v))^2+(Real.exp (-v)*x)^2))):ℂ) = _
  rw [hy,positiveProfile_exp]

private theorem row_eq_archProfile (v : ℝ) (c : ℕ+) :
    ((c:ℕ).totient:ℂ)*
        (∫ x, SelbergThetaHorizontalArithmetic.archProfile (Real.exp (-v)) c x) =
      2*(Real.exp (-v/2):ℂ)*row c v := by
  let f := SelbergThetaHorizontalArithmetic.archProfile (Real.exp (-v)) c
  have hs : (∫ x, f (Real.exp (-v)*x)) =
      (Real.exp v) • (∫ x, f x) := by
    rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr (Real.exp_pos _)),Real.exp_neg,inv_inv]
  have ht : (∫ x, f x) = (Real.exp (-v)) • (∫ x, f (Real.exp (-v)*x)) := by
    rw [hs,smul_smul,← Real.exp_add]
    simp
  rw [show (∫ x, SelbergThetaHorizontalArithmetic.archProfile (Real.exp (-v)) c x) =
    (∫ x, f x) by rfl,ht]
  change ((c:ℕ).totient:ℂ)*
    ((Real.exp (-v):ℂ)*(∫ x, SelbergThetaHorizontalArithmetic.archProfile (Real.exp (-v)) c (Real.exp (-v)*x))) = _
  simp_rw [archProfile_scaled]
  rw [← integral_const_mul]
  have he (x : ℝ) :
      (Real.exp (-v):ℂ)*(2*(Real.exp ((v-shift c x)/2):ℂ)*baseProfile (-1/2) (v-shift c x)) =
        (2*(Real.exp (-v/2):ℂ))*(Complex.exp (-(shift c x:ℂ)/2)*baseProfile (-1/2) (v-shift c x)) := by
    rw [show Complex.exp (-(shift c x:ℂ)/2) = (Real.exp (-shift c x/2):ℂ) by
      simpa only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat] using
        (Complex.ofReal_exp (-shift c x/2)).symm]
    have hh : Real.exp (-v)*Real.exp ((v-shift c x)/2) =
        Real.exp (-v/2)*Real.exp (-shift c x/2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    have hhC := congrArg (fun r : ℝ => (r:ℂ)) hh
    simp only [Complex.ofReal_mul] at hhC
    linear_combination 2*baseProfile (-1/2) (v-shift c x)*hhC
  simp_rw [he]
  rw [integral_const_mul]
  unfold row
  ring

/-- The literal horizontal theta source is the parabolic source plus every reflected row. -/
theorem horizontalWeight_log (v : ℝ) :
    (SelbergThetaCommonForcingPairing.horizontalWeight (Real.exp (-v)):ℂ) =
      2*(Real.exp (-v/2):ℂ)*(baseProfile (-1/2) v+kernel v) := by
  rw [SelbergThetaHorizontalArithmetic.horizontalWeight_eq_totient _ (Real.exp_pos _),
    positiveProfile_exp_neg]
  simp_rw [row_eq_archProfile]
  rw [tsum_mul_left,kernel]
  ring

private theorem transform_base_actual (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform (baseProfile (-1/2)) (-I*(P.s-1/2)) = xi (2*P.s-1/2) := by
  rw [transform_base]
  change xi (1/2+sourceArgument (-1/2) (-I*(P.s-1/2))) = _
  have he : 1/2+sourceArgument (-1/2) (-I*(P.s-1/2)) = 1-(2*P.s-1/2) := by
    unfold sourceArgument
    linear_combination 2*I_sq*(P.s-1/2)
  rw [he,xi_one_sub]

/-- Mellin integrand of the actual horizontal source in the reflected logarithmic coordinate. -/
def logIntegrand (P : D4BMEisensteinAbsoluteConvergenceParameter) (v : ℝ) : ℂ :=
  Complex.exp (-(P.s-1)*(v:ℂ))*
    (SelbergThetaCommonForcingPairing.horizontalWeight (Real.exp (-v)):ℂ)

private theorem logIntegrand_eq (P : D4BMEisensteinAbsoluteConvergenceParameter) (v : ℝ) :
    logIntegrand P v = 2*(
      fourierIntegrand (baseProfile (-1/2)) (-I*(P.s-1/2)) v+
      fourierIntegrand kernel (-I*(P.s-1/2)) v) := by
  rw [logIntegrand,horizontalWeight_log,Complex.ofReal_exp]
  unfold fourierIntegrand
  have he : -(P.s-1)*(v:ℂ)+((-v/2:ℝ):ℂ) =
      -I*(-I*(P.s-1/2))*(v:ℂ) := by
    push_cast
    linear_combination -I_sq*(P.s-1/2)*(v:ℂ)
  calc
    _ = 2*(Complex.exp (-(P.s-1)*(v:ℂ))*Complex.exp ((-v/2:ℝ):ℂ))*
        (baseProfile (-1/2) v+kernel v) := by ring
    _ = _ := by rw [← Complex.exp_add,he]; ring

/-- Absolute admission of the full horizontal source on every safe Mellin line. -/
theorem logIntegrand_integrable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Integrable (logIntegrand P) := by
  have h := ((base_integrable (-1/2) (-I*(P.s-1/2))).add (kernel_integrable P)).const_mul (2:ℂ)
  exact h.congr (ae_of_all _ fun v => (logIntegrand_eq P v).symm)

/-- The full horizontal theta transform, with both parabolic and reflected terms retained. -/
theorem integral_logIntegrand (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∫ v, logIntegrand P v) = 2*xi (2*P.s-1/2)*
      (1+reflectedCompletedLambda (2*P.s-1)/reflectedCompletedLambda (2*P.s)) := by
  simp_rw [logIntegrand_eq]
  rw [integral_const_mul,integral_add
    (base_integrable (-1/2) (-I*(P.s-1/2))) (kernel_integrable P)]
  change 2*(transform (baseProfile (-1/2)) (-I*(P.s-1/2))+
    transform kernel (-I*(P.s-1/2))) = _
  rw [transform_kernel,transform_base_actual]
  ring

private def heightMellinIntegrand (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (y:ℂ)^(P.s-2)*(SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ)

private theorem heightMellin_exp (P : D4BMEisensteinAbsoluteConvergenceParameter) (v : ℝ) :
    Real.exp v • heightMellinIntegrand P (Real.exp v) = logIntegrand P (-v) := by
  unfold heightMellinIntegrand logIntegrand
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le,Real.log_exp,Complex.real_smul,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  simp only [neg_neg,Complex.ofReal_neg]
  congr 2
  ring

private theorem integral_exp_substitution (f : ℝ → ℂ) :
    (∫ y in Ioi (0:ℝ), f y) = ∫ v : ℝ, Real.exp v • f (Real.exp v) := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [image_univ,Real.range_exp,setIntegral_univ,abs_of_pos (Real.exp_pos _)] using h

private theorem integrable_exp_substitution (f : ℝ → ℂ) :
    IntegrableOn f (Ioi (0:ℝ)) ↔ Integrable (fun v => Real.exp v • f (Real.exp v)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := univ) MeasurableSet.univ
    (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt) Real.exp_injective.injOn f
  simpa only [image_univ,Real.range_exp,integrableOn_univ,abs_of_pos (Real.exp_pos _)] using h

/-- The Mellin integral of the literal native horizontal weight converges absolutely. -/
theorem horizontalWeight_mellin_convergent (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    MellinConvergent (fun y => (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ)) (P.s-1) := by
  unfold MellinConvergent
  simp only [show P.s-1-1 = P.s-2 by ring,smul_eq_mul]
  change IntegrableOn (heightMellinIntegrand P) (Ioi (0:ℝ))
  rw [integrable_exp_substitution]
  simpa only [heightMellin_exp] using (logIntegrand_integrable P).comp_neg

/-- Exact Mellin value of the literal native horizontal theta weight. -/
theorem horizontalWeight_mellin (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    mellin (fun y => (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ)) (P.s-1) =
      2*xi (2*P.s-1/2)*
        (1+reflectedCompletedLambda (2*P.s-1)/reflectedCompletedLambda (2*P.s)) := by
  unfold mellin
  simp only [show P.s-1-1 = P.s-2 by ring,smul_eq_mul]
  change (∫ y in Ioi (0:ℝ), heightMellinIntegrand P y) = _
  rw [integral_exp_substitution]
  simp_rw [heightMellin_exp]
  rw [integral_neg_eq_self,integral_logIntegrand]

/-- Source-specific completed Mellin factorization on its full absolute-convergence half-plane. -/
theorem horizontalWeight_square_hasMellin {z : ℂ} (hz : 0 < z.re) :
    HasMellin (fun a : ℝ => (SelbergThetaCommonForcingPairing.horizontalWeight (a^2):ℂ)) z
      (xi (z+3/2)*(1+reflectedCompletedLambda (z+1)/reflectedCompletedLambda (z+2))) := by
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨1+z/2,by simp; linarith⟩
  have hp : P.s-1 = z/2 := by dsimp [P]; ring
  have hv := horizontalWeight_mellin P
  rw [hp] at hv
  have hs : MellinConvergent
      (fun a : ℝ => (SelbergThetaCommonForcingPairing.horizontalWeight (a^(2:ℝ)):ℂ)) z := by
    apply (MellinConvergent.comp_rpow
      (f := fun y : ℝ => (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ))
      (s := z) (a := (2:ℝ)) (by norm_num)).2
    simpa only [hp,Complex.ofReal_ofNat] using horizontalWeight_mellin_convergent P
  have hm := mellin_comp_rpow
    (fun y => (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ)) z (2:ℝ)
  norm_num only [Real.rpow_two,Complex.ofReal_ofNat,abs_of_pos (by norm_num : (0:ℝ)<2)] at hs hm
  refine ⟨hs,?_⟩
  rw [hm,hv]
  simp only [Complex.real_smul]
  have h0 : 2*P.s-1/2 = z+3/2 := by dsimp [P]; ring
  have h1 : 2*P.s-1 = z+1 := by dsimp [P]; ring
  have h2 : 2*P.s = z+2 := by dsimp [P]; ring
  rw [h0,h1,h2]
  norm_num
  ring

end
end RHTower.SelbergThetaHorizontalTransform
