import GaloisForLFunctions.RHTower.SelbergThetaDilationTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPositiveMean
import Mathlib.Analysis.Complex.RemovableSingularity
/-!
# The full totient-weighted theta Hankel transform

For the literal theta dilation profile `g`, let `J(v) = ∫ conj(g(t)) g(v-t) dt`.
The full reflected kernel is

`H(v) = ∑_{q≥1} φ(q)/q ∫ J(v-2 log(q)-log(1+x²))/sqrt(1+x²) dx`.

Absolute row norm summability and Fubini give, for `Re(s)>1/2`,

`∫ exp(-s*v) H(v) dv = Λ(2s)/Λ(2s+1) * transform J (-I*s)`.

At each actual Xi divisor copy, both source factors vanish at the mean point.
Divided differences construct a holomorphic continuation on `Re(s)>0`, with
value zero at `s=1/2` and derivative `2*conj(ξ′(rho))*ξ′(rho)/ξ(2)` there.
The actual full-kernel integrals consequently have zero right Abel limit at
the mean point. Real-frequency boundary integration and the modular Gram
identity are separate analytic questions.
-/

open Complex MeasureTheory Set Function
open scoped ComplexConjugate FourierTransform
namespace RHTower.SelbergThetaTotientHankel
open SelbergThetaDilationTransform GaloisForLFunctions.HTGeometry
noncomputable section

private theorem hankel_measurable (rho : ℂ) : Measurable (hankelCorrelation rho) := by
  have hp : Continuous (profile rho) := by
    unfold profile baseProfile
    have hc := contDiff_thetaCuspFullSource.continuous
    fun_prop
  have hm : StronglyMeasurable (fun p : ℝ × ℝ =>
      conj (profile rho p.2) * profile rho (p.1-p.2)) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  exact hm.integral_prod_right'.measurable

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

private def tiltedHankel (rho : ℂ) (P : D4BMEisensteinAbsoluteConvergenceParameter) :=
  fourierIntegrand (hankelCorrelation rho) (-I*(P.s-1/2))

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

private theorem tiltedHankel_measurable (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : Measurable (tiltedHankel rho P) := by
  unfold tiltedHankel fourierIntegrand
  have hm := hankel_measurable rho
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

/-- A complete denominator row of the actual reflected theta correlation. The half-density
weight is `1 / (q * sqrt (1+x²))`, written in exponential form. -/
def row (rho : ℂ) (q : ℕ+) (v : ℝ) : ℂ :=
  ((q:ℕ).totient:ℂ) * ∫ x : ℝ,
    Complex.exp (-(shift q x:ℂ)/2) * hankelCorrelation rho (v-shift q x)


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

/-- The row is the literal totient-weighted square-root integral appearing in full Gram unfolding. -/
theorem row_eq_totient_integral (rho : ℂ) (q : ℕ+) (v : ℝ) :
    row rho q v = (((q:ℕ).totient:ℂ) / (((q:ℕ):ℝ):ℂ)) *
      ∫ x : ℝ, hankelCorrelation rho
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
def kernel (rho : ℂ) (v : ℝ) : ℂ := ∑' q : ℕ+, row rho q v

private theorem tiltedHankel_eq (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (v : ℝ) :
    tiltedHankel rho P v =
      Complex.exp (-(P.s-1/2)*(v:ℂ)) * hankelCorrelation rho v := by
  unfold tiltedHankel fourierIntegrand
  congr 2
  linear_combination I_sq * (P.s-1/2)*(v:ℂ)

private theorem row_integrand (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) (v : ℝ) :
    fourierIntegrand (row rho q) (-I*(P.s-1/2)) v =
      d4BMZeroRamanujanPNatTerm P q * ∫ x : ℝ,
        archKernel P x * tiltedHankel rho P (v-shift q x) := by
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
  rw [archKernel_eq_exp, tiltedHankel_eq]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  unfold shift
  push_cast
  ring

private theorem row_product_integrable (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    Integrable (fun p : ℝ × ℝ => archKernel P p.1 *
      tiltedHankel rho P (p.2-shift q p.1)) (volume.prod volume) := by
  exact shifted_product_integrable (hankel_integrable rho _)
    (tiltedHankel_measurable rho P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

/-- Every row is absolutely integrable on each strictly convergent Laplace line. -/
theorem row_integrable (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    Integrable (fourierIntegrand (row rho q) (-I*(P.s-1/2))) := by
  change Integrable (fun v => fourierIntegrand (row rho q) (-I*(P.s-1/2)) v)
  simp_rw [row_integrand]
  exact (row_product_integrable rho P q).integral_prod_right.const_mul _

private theorem row_integral_norm_le (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    (∫ v : ℝ, ‖fourierIntegrand (row rho q) (-I*(P.s-1/2)) v‖) ≤
      ‖d4BMZeroRamanujanPNatTerm P q‖ *
        ((∫ x : ℝ, ‖archKernel P x‖) * ∫ v : ℝ, ‖tiltedHankel rho P v‖) := by
  simp_rw [row_integrand, norm_mul]
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_integral_shifted_product_le (hankel_integrable rho _)
    (tiltedHankel_measurable rho P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

/-- Absolute row norms are summable, so exchanging the full totient sum and transform is valid. -/
theorem row_norm_summable (rho : ℂ) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Summable (fun q : ℕ+ => ∫ v : ℝ,
      ‖fourierIntegrand (row rho q) (-I*(P.s-1/2)) v‖) := by
  exact Summable.of_nonneg_of_le (fun q => integral_nonneg (fun v => norm_nonneg _))
    (row_integral_norm_le rho P) ((arithmeticTerm_summable P).norm.mul_right _)

/-- Exact transform of one complete denominator row, with its actual arithmetic coefficient. -/
private theorem transform_row (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (q : ℕ+) :
    transform (row rho q) (-I*(P.s-1/2)) =
      d4BMZeroRamanujanPNatTerm P q *
        ((∫ x : ℝ, archKernel P x) * transform (hankelCorrelation rho) (-I*(P.s-1/2))) := by
  unfold transform
  simp_rw [row_integrand]
  rw [integral_const_mul]
  congr 1
  exact integral_shifted_product (hankel_integrable rho _)
    (tiltedHankel_measurable rho P) (integrable_d4BMCauchyPowerKernel unitHeight P)
    (archKernel_measurable P) (by unfold shift; fun_prop)

private theorem kernel_integrand (rho : ℂ) (z : ℂ) (v : ℝ) :
    fourierIntegrand (kernel rho) z v = ∑' q : ℕ+, fourierIntegrand (row rho q) z v := by
  unfold fourierIntegrand kernel
  exact tsum_mul_left.symm

/-- The full reflected theta kernel is absolutely integrable on every Laplace line `Re(s)>1/2`. -/
theorem kernel_integrable (rho : ℂ) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Integrable (fourierIntegrand (kernel rho) (-I*(P.s-1/2))) := by
  change Integrable (fun v => fourierIntegrand (kernel rho) (-I*(P.s-1/2)) v)
  simp_rw [kernel_integrand]
  exact integrable_tsum_of_summable_integral_norm (row_integrable rho P) (row_norm_summable rho P)

private theorem transform_kernel_factored (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform (kernel rho) (-I*(P.s-1/2)) =
      ((∫ x : ℝ, archKernel P x) *
        (riemannZeta (2*P.s-1) / riemannZeta (2*P.s))) *
          transform (hankelCorrelation rho) (-I*(P.s-1/2)) := by
  unfold transform
  simp_rw [kernel_integrand]
  rw [integral_tsum_eq_tsum_integral_of_summable_integral_norm
    (row_integrable rho P) (row_norm_summable rho P)]
  change (∑' q : ℕ+, transform (row rho q) (-I*(P.s-1/2))) = _
  simp_rw [transform_row]
  rw [tsum_mul_right, tsum_d4BMZeroRamanujanPNatTerm_eq_zetaRatio]
  unfold transform
  ring

/-- Completed transform of the literal all-denominator theta Hankel kernel. -/
theorem transform_kernel_completed (rho : ℂ)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    reflectedCompletedLambda (2*P.s) * transform (kernel rho) (-I*(P.s-1/2)) =
      reflectedCompletedLambda (2*P.s-1) *
        transform (hankelCorrelation rho) (-I*(P.s-1/2)) := by
  have he := d4BM_completedZeroWeylFactor_eq_reflectedConstantTerm unitHeight P
  have hf : 𝓕 (d4BMCauchyPowerKernel unitHeight P.s) 0 = ∫ x : ℝ, archKernel P x := by
    rw [Real.fourier_eq]
    simp [archKernel]
  rw [hf] at he
  simp only [unitHeight, Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one] at he
  rw [transform_kernel_factored, ← mul_assoc, he]

/-- Exact completed-zeta ratio multiplying the full reflected theta correlation. -/
theorem transform_kernel (rho : ℂ) (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform (kernel rho) (-I*(P.s-1/2)) =
      (reflectedCompletedLambda (2*P.s-1) / reflectedCompletedLambda (2*P.s)) *
        transform (hankelCorrelation rho) (-I*(P.s-1/2)) := by
  have hn : reflectedCompletedLambda (2*P.s) ≠ 0 :=
    D4BMModularCore.cuspCompletedLambda_ne_zero (by
      norm_num [Complex.mul_re]
      linarith [P.re_gt_one])
  apply (mul_left_cancel₀ hn)
  rw [transform_kernel_completed]
  field_simp

private def laplaceFactor (s : ℂ) : ℂ :=
  2 - Complex.exp ((s-1/2)*(Real.log 2:ℂ))

private def laplaceSource (rho s : ℂ) : ℂ :=
  laplaceFactor s * xi (rho+1-2*s)

private theorem profile_laplace (rho s : ℂ) :
    transform (profile rho) (-I*s) = laplaceSource rho s := by
  rw [transform_profile, dyadicFactor_eq_exp]
  have he : I*(-I*s) = s := by linear_combination -I_sq*s
  rw [he]
  change laplaceFactor s * xi (1/2 + sourceArgument rho (-I*s)) = _
  unfold laplaceSource
  congr 2
  unfold sourceArgument
  linear_combination 2*I_sq*s

private theorem laplaceSource_conj (rho s : ℂ) :
    conj (laplaceSource rho (conj s)) = laplaceSource (conj rho) s := by
  simp only [laplaceSource, laplaceFactor, map_mul, map_sub, map_add, map_one,
    map_div₀, map_ofNat, ← Complex.exp_conj, ← xi_conj, Complex.conj_ofReal, conj_conj]

private theorem hankel_laplace (rho s : ℂ) :
    transform (hankelCorrelation rho) (-I*s) =
      laplaceSource (conj rho) s * laplaceSource rho s := by
  rw [transform_hankelCorrelation]
  have he : -conj (-I*s) = -I*conj s := by simp
  rw [he, profile_laplace, profile_laplace, laplaceSource_conj]

private def sourceSlope (rho s : ℂ) : ℂ :=
  laplaceFactor s * dslope xi rho (rho+1-2*s)

private theorem sourceSlope_differentiable (rho : ℂ) : Differentiable ℂ (sourceSlope rho) := by
  have hd : Differentiable ℂ (dslope xi rho) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (by simp)).2
      xi_differentiable.differentiableOn)
  unfold sourceSlope laplaceFactor
  fun_prop

private theorem laplaceSource_factorization {rho : ℂ} (hxi : xi rho = 0) (s : ℂ) :
    laplaceSource rho s = (1-2*s)*sourceSlope rho s := by
  have he := sub_smul_dslope xi rho (rho+1-2*s)
  rw [hxi, sub_zero, smul_eq_mul] at he
  have he' : (rho+1-2*s)-rho = 1-2*s := by ring
  rw [he'] at he
  unfold laplaceSource sourceSlope
  rw [← he]
  ring

/-- The source-specific analytic continuation obtained by cancelling both actual Xi factors
against the mean scattering pole. -/
def continuation (q : XiZeroCopy) (s : ℂ) : ℂ :=
  ((2*s-1)*(2*s+1)*xi (2*s) / xi (2*s+1)) *
    sourceSlope (conj (q.1:ℂ)) s * sourceSlope (q.1:ℂ) s

/-- The two source zeros leave a vanishing continuation at the mean pole. -/
theorem continuation_mean (q : XiZeroCopy) : continuation q (1/2) = 0 := by
  norm_num [continuation]

/-- The actual source cancellation yields holomorphy throughout the positive Laplace half-plane. -/
theorem continuation_analytic (q : XiZeroCopy) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (continuation q) s := by
  have ha : AnalyticAt ℂ (fun z : ℂ => 2*z) s := analyticAt_const.mul analyticAt_id
  have hb : AnalyticAt ℂ (fun z : ℂ => 2*z+1) s := ha.add analyticAt_const
  have hn : xi (2*s+1) ≠ 0 := xi_ne_zero_of_one_lt_re (by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith)
  exact (((((ha.sub analyticAt_const).mul hb).mul ((xi_differentiable.analyticAt _).comp ha)).div
    ((xi_differentiable.analyticAt _).comp hb) hn).mul
      ((sourceSlope_differentiable (conj (q.1:ℂ))).analyticAt s)).mul
        ((sourceSlope_differentiable (q.1:ℂ)).analyticAt s)

private theorem xi_eq_half_mul_reflected {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    xi w = w*(w-1)/2 * reflectedCompletedLambda w := by
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  rw [xi_eq_half_mul hw0 hw1, reflectedCompletedLambda, riemannZeta_def_of_ne_zero hw0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hw]

private theorem scatteringRatio_eq_xi {s : ℂ} (hs : 1/2 < s.re) :
    reflectedCompletedLambda (2*s) / reflectedCompletedLambda (2*s+1) =
      ((2*s+1)/(2*s-1)) * (xi (2*s) / xi (2*s+1)) := by
  have h2 : 1 < (2*s).re := by norm_num [Complex.mul_re]; linarith
  have h3 : 1 < (2*s+1).re := by norm_num [Complex.add_re, Complex.mul_re]; linarith
  have hn2 : 2*s ≠ 1 := by intro h; norm_num [h] at h2
  have hn3 : 2*s+1 ≠ 1 := by intro h; norm_num [h] at h3
  have hz2 : 2*s ≠ 0 := by intro h; norm_num [h] at h2
  have hz3 : 2*s+1 ≠ 0 := by intro h; norm_num [h] at h3
  have hL := D4BMModularCore.cuspCompletedLambda_ne_zero h3
  rw [xi_eq_half_mul_reflected (lt_trans zero_lt_one h2) hn2,
    xi_eq_half_mul_reflected (lt_trans zero_lt_one h3) hn3]
  field_simp
  ring

private theorem continuation_eq_scattering (q : XiZeroCopy) {s : ℂ} (hs : 1/2 < s.re) :
    continuation q s =
      (reflectedCompletedLambda (2*s)/reflectedCompletedLambda (2*s+1)) *
        transform (hankelCorrelation (q.1:ℂ)) (-I*s) := by
  have hr := xi_eq_zero_of_mem_divisor_support q.1
  have hc : xi (conj (q.1:ℂ)) = 0 := by rw [xi_conj, hr, map_zero]
  have hn : 2*s-1 ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    norm_num [Complex.sub_re, Complex.mul_re] at he'
    linarith
  rw [scatteringRatio_eq_xi hs, hankel_laplace,
    laplaceSource_factorization hr, laplaceSource_factorization hc]
  unfold continuation
  field_simp
  ring

/-- The holomorphic continuation agrees with the transform of the full kernel on its proved
absolute-convergence half-plane. -/
theorem transform_kernel_eq_continuation (q : XiZeroCopy)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    transform (kernel (q.1:ℂ)) (-I*(P.s-1/2)) = continuation q (P.s-1/2) := by
  have hs : 1/2 < (P.s-1/2).re := by
    norm_num [Complex.sub_re]
    linarith [P.re_gt_one]
  rw [continuation_eq_scattering q hs, transform_kernel]
  have h2 : 2*P.s-1 = 2*(P.s-1/2) := by ring
  have h3 : 2*P.s = 2*(P.s-1/2)+1 := by ring
  rw [← h3, ← h2]

private theorem sourceSlope_mean (rho : ℂ) : sourceSlope rho (1/2) = deriv xi rho := by
  have he : rho+1-2*(1/2:ℂ) = rho := by ring
  unfold sourceSlope laplaceFactor
  rw [he, dslope_same]
  norm_num

/-- The first mean-pole jet is fixed by the squared derivative of the actual Xi source. -/
theorem hasDerivAt_continuation_mean (q : XiZeroCopy) :
    HasDerivAt (continuation q)
      ((2 / xi 2) * (conj (deriv xi (q.1:ℂ)) * deriv xi (q.1:ℂ))) (1/2) := by
  let B : ℂ → ℂ := fun s => ((2*s+1)*xi (2*s)/xi (2*s+1)) *
    sourceSlope (conj (q.1:ℂ)) s * sourceSlope (q.1:ℂ) s
  have hs1 := sourceSlope_differentiable (conj (q.1:ℂ))
  have hs2 := sourceSlope_differentiable (q.1:ℂ)
  have hx : xi (2*(1/2:ℂ)+1) ≠ 0 := by convert xi_two_ne_zero using 1; norm_num
  have hxiD := xi_differentiable
  have hB : DifferentiableAt ℂ B (1/2) := by
    dsimp only [B]
    fun_prop
  have hD : HasDerivAt (fun s : ℂ => (2*s-1)*B s) (2*B (1/2)) (1/2) := by
    simpa using! (((hasDerivAt_id (1/2:ℂ)).const_mul 2).sub_const 1).mul hB.hasDerivAt
  have he : ((2 / xi 2) * (conj (deriv xi (q.1:ℂ)) * deriv xi (q.1:ℂ))) =
      2*B (1/2) := by
    simp only [B, sourceSlope_mean]
    norm_num [xi_one, xi_deriv_conj]
    ring
  have hf : continuation q = fun s : ℂ => (2*s-1)*B s := by
    funext s
    dsimp only [B, continuation]
    ring
  rw [hf, he]
  exact hD

/-- The actual full-kernel Laplace integrals tend to zero as their absolute-convergence line
approaches the mean pole from the right. -/
theorem kernel_mean_abel_limit (q : XiZeroCopy) :
    Filter.Tendsto (fun sigma : ℝ => transform (kernel (q.1:ℂ)) (-I*(sigma:ℂ)))
      (nhdsWithin (1/2) (Ioi (1/2))) (nhds 0) := by
  have hc : ContinuousAt (fun sigma : ℝ => continuation q (sigma:ℂ)) (1/2) :=
    (continuation_analytic q (s := ((1/2:ℝ):ℂ)) (by norm_num)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have he : continuation q ((1/2:ℝ):ℂ) = 0 := by
    norm_num [continuation]
  have hlim : Filter.Tendsto (fun sigma : ℝ => continuation q (sigma:ℂ))
      (nhdsWithin (1/2) (Ioi (1/2))) (nhds 0) := by
    rw [← he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hs : 1/2 < sigma := hsigma
  let P : D4BMEisensteinAbsoluteConvergenceParameter :=
    ⟨(sigma:ℂ)+1/2, by norm_num [Complex.add_re]; linarith⟩
  have ht := transform_kernel_eq_continuation q P
  have hp : P.s-1/2 = (sigma:ℂ) := by dsimp [P]; ring
  rw [hp] at ht
  exact ht.symm

end
end RHTower.SelbergThetaTotientHankel
