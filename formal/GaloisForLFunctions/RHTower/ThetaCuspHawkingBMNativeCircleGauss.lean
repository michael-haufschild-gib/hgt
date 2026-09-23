import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCuspTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Identification of the original height-power circle with the physical Gauss kernel. -/
open Set Filter Topology MeasureTheory Complex
open scoped Nat ComplexConjugate
namespace RHTower.D4BMNativeCircle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private def circlePhase (n : ℤ) (theta : ℝ) : ℂ :=
  Complex.exp ((n:ℂ)*Complex.I*(theta:ℂ))
private theorem phase_norm (n : ℤ) (theta : ℝ) : ‖circlePhase n theta‖=1 := by
  simp [circlePhase,Complex.norm_exp]
private theorem phase_continuous (n : ℤ) : Continuous (circlePhase n) := by
  unfold circlePhase
  fun_prop
private theorem phase_mul (n m : ℤ) (theta : ℝ) :
    circlePhase n theta*circlePhase m theta=circlePhase (n+m) theta := by
  simp only [circlePhase,← Complex.exp_add,Int.cast_add]
  congr 1
  ring
private theorem phase_integral (n : ℤ) :
    (∫ theta in Ioc (0:ℝ) (2*Real.pi),circlePhase n theta)=
      if n=0 then (2*Real.pi:ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  by_cases hn : n=0
  · subst n
    simp [circlePhase]
  · have hc : (n:ℂ)*Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero
    rw [if_neg hn]
    dsimp only [circlePhase]
    rw [integral_exp_mul_complex hc]
    have he : ((n:ℂ)*Complex.I)*(2*Real.pi:ℂ)=(n:ℂ)*(2*Real.pi*Complex.I) := by ring
    rw [show (((2*Real.pi:ℝ):ℂ))=(2*Real.pi:ℂ) by push_cast; rfl,he,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

private def circleCoefficient (alpha : ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  Ring.choose (-alpha) n*(-(r:ℂ))^n
private def circleTerm (alpha : ℂ) (r theta : ℝ) (n : ℕ) : ℂ :=
  circleCoefficient alpha r n*circlePhase (n:ℤ) theta

private theorem coefficient_summable (alpha : ℂ) (r : ℝ) (hr : |r|<1) :
    Summable (fun n => ‖circleCoefficient alpha r n‖) := by
  have hx : (-(r:ℂ)) ∈ Metric.eball (0:ℂ) (binomialSeries ℂ (-alpha)).radius := by
    apply Metric.eball_subset_eball binomialSeries_radius_ge_one
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal,Metric.mem_ball,dist_zero_right,
      norm_neg,Complex.norm_real,Real.norm_eq_abs]
    exact hr
  have h := (binomialSeries ℂ (-alpha)).summable_norm_apply hx
  simpa only [circleCoefficient,binomialSeries,FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] using h

private theorem term_norm (alpha : ℂ) (r theta : ℝ) (n : ℕ) :
    ‖circleTerm alpha r theta n‖=‖circleCoefficient alpha r n‖ := by
  rw [circleTerm,norm_mul,phase_norm,mul_one]

private theorem binomial_circle_hasSum (alpha : ℂ) (r theta : ℝ) (hr : |r|<1) :
    HasSum (circleTerm alpha r theta)
      ((1-(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)) := by
  have hx : (-(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ))) ∈ Metric.eball (0:ℂ) 1 := by
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal,Metric.mem_ball,dist_zero_right,norm_mul,norm_neg,
      Complex.norm_exp,show (Complex.I*(theta:ℂ)).re=0 by simp,Real.exp_zero,mul_one,
      Complex.norm_real,Real.norm_eq_abs]
    exact hr
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := -alpha)).hasSum hx
  convert! h using 1
  · ext n
    simp only [circleTerm,circleCoefficient,circlePhase,binomialSeries,
      FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,mul_pow,← Complex.exp_nat_mul]
    simp only [Int.cast_natCast,mul_assoc]
  · simp only [zero_add,neg_mul,sub_eq_add_neg]

private theorem diagonal_circle_integral (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    average (fun theta => (∑' n, c n*circlePhase (n:ℤ) theta)*
      (∑' m, c m*circlePhase (-(m:ℤ)) theta)) = ∑' n, (c n)^(2 : ℕ) := by
  let F : ℕ × ℕ → ℝ → ℂ := fun p theta =>
    (c p.1*c p.2)*circlePhase ((p.1:ℤ)-(p.2:ℤ)) theta
  have hn (p : ℕ × ℕ) (theta : ℝ) : ‖F p theta‖=‖c p.1‖*‖c p.2‖ := by
    dsimp only [F]
    rw [norm_mul,phase_norm,mul_one,norm_mul]
  have hi (p : ℕ × ℕ) : IntegrableOn (F p) (Ioc 0 (2*Real.pi)) :=
    (continuous_const.mul (phase_continuous _)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hs : Summable (fun p : ℕ × ℕ => ∫ theta in Ioc 0 (2*Real.pi), ‖F p theta‖) := by
    simp only [hn,integral_const,Measure.real,smul_eq_mul]
    exact (hc.mul_of_nonneg hc (fun n => norm_nonneg _) (fun n => norm_nonneg _)).mul_left _
  have he (theta : ℝ) : (∑' n, c n*circlePhase (n:ℤ) theta)*
      (∑' m, c m*circlePhase (-(m:ℤ)) theta)=∑' p, F p theta := by
    rw [tsum_mul_tsum_of_summable_norm
      (by simpa only [norm_mul,phase_norm,mul_one] using hc)
      (by simpa only [norm_mul,phase_norm,mul_one] using hc)]
    apply tsum_congr
    intro p
    dsimp only [F]
    rw [show (c p.1*circlePhase (p.1:ℤ) theta)*(c p.2*circlePhase (-(p.2:ℤ)) theta)=
      (c p.1*c p.2)*(circlePhase (p.1:ℤ) theta*circlePhase (-(p.2:ℤ)) theta) by ring,
      phase_mul,sub_eq_add_neg]
  simp only [he,average]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  have hv (p : ℕ × ℕ) : (∫ theta in Ioc (0:ℝ) (2*Real.pi), F p theta)=
      if p.1=p.2 then (2*Real.pi:ℂ)*(c p.1)^(2 : ℕ) else 0 := by
    dsimp only [F]
    rw [integral_const_mul,phase_integral]
    by_cases hp : p.1=p.2
    · simp [hp]; ring
    · have hh : (p.1:ℤ)-(p.2:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp)
      simp [hp,hh]
  have hsum := (hasSum_integral_of_summable_integral_norm hi hs).summable
  rw [hsum.tsum_prod]
  have hdiag (b : ℕ) : (∑' m : ℕ, if b=m then (2*Real.pi:ℂ)*(c b)^(2 : ℕ) else 0)=
      (2*Real.pi:ℂ)*(c b)^(2 : ℕ) := by
    rw [tsum_eq_single b]
    · simp
    · intro m hm
      simp [Ne.symm hm]
  simp only [hv,hdiag,tsum_mul_left]
  field_simp

private theorem coefficient_as_gauss (alpha : ℂ) (r : ℝ) (n : ℕ) :
    circleCoefficient alpha r n =
      (ordinaryHypergeometricSeries ℂ alpha 1 1 n fun _ => (r:ℂ)) := by
  have hb := binomialSeries_eq_ordinaryHypergeometricSeries
    (𝔸 := ℂ) (a := -alpha) (b := (1:ℂ)) (by
      intro k hk
      have h := congrArg Complex.re hk
      norm_num at h
      linarith [Nat.cast_nonneg (α := ℝ) k])
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ =>
    p n (fun _ => -(r:ℂ))) hb
  simpa [circleCoefficient,binomialSeries,FormalMultilinearSeries.compContinuousLinearMap,
    FormalMultilinearSeries.ofScalars_apply_eq,neg_neg,mul_comm] using h

private theorem coefficient_square (alpha : ℂ) (r : ℝ) (n : ℕ) :
    (circleCoefficient alpha r n)^(2 : ℕ) =
      (ordinaryHypergeometricSeries ℂ alpha alpha 1 n fun _ => ((r:ℂ)^(2 : ℕ))) := by
  rw [coefficient_as_gauss,ordinaryHypergeometricSeries_apply_eq,
    ordinaryHypergeometricSeries_apply_eq,ascPochhammer_eval_one]
  simp only [smul_eq_mul]
  have hfac : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp
  ring

private theorem binomial_product_average (alpha : ℂ) (r : ℝ) (hr : |r|<1) :
    average (fun theta =>
      (1-(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)*
      (1-(r:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha)) =
      (ordinaryHypergeometricSeries ℂ alpha alpha 1).sum ((r:ℂ)^(2 : ℕ)) := by
  have he (theta : ℝ) :
      (1-(r:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha)=
        ∑' n, circleCoefficient alpha r n*circlePhase (-(n:ℤ)) theta := by
    have h := (binomial_circle_hasSum alpha r (-theta) hr).tsum_eq
    convert! h.symm using 1 <;>
      simp [circleTerm,circlePhase,Int.cast_neg,mul_neg,neg_mul]
  simp only [he,← (binomial_circle_hasSum alpha r _ hr).tsum_eq,circleTerm]
  rw [diagonal_circle_integral _ (coefficient_summable alpha r hr)]
  exact tsum_congr (fun n => coefficient_square alpha r n)

private theorem conjugate_power_product (alpha z : ℂ) (hz : 0 < z.re) :
    z^alpha*(conj z)^alpha=(z*conj z)^alpha := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have hc0 : conj z ≠ 0 := by simpa using hz0
  have ha : z.arg ≠ Real.pi := (Complex.arg_lt_pi_iff.mpr (Or.inl hz.le)).ne
  have hlog : Complex.log (z*conj z)=Complex.log z+Complex.log (conj z) := by
    apply (Complex.log_mul_eq_add_log_iff hz0 hc0).mpr
    rw [Complex.arg_conj,if_neg ha]
    simp only [add_neg_cancel,mem_Ioc]
    constructor <;> linarith [Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero hz0,Complex.cpow_def_of_ne_zero hc0,
    Complex.cpow_def_of_ne_zero (mul_ne_zero hz0 hc0),hlog,add_mul,Complex.exp_add]

private theorem paired_power_product (alpha : ℂ) (r theta : ℝ) (hr : |r|<1) :
    (1-(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)*
      (1-(r:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha)=
        ((1-2*r*Real.cos theta+r^(2 : ℕ):ℝ):ℂ)^(-alpha) := by
  let z : ℂ := 1-(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ))
  have hn : ‖(r:ℂ)*Complex.exp (Complex.I*(theta:ℂ))‖ < 1 := by
    simpa [Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs] using hr
  have hz : 0 < z.re := by
    have he := Complex.re_le_norm ((r:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))
    dsimp [z]
    linarith
  have hc : 1-(r:ℂ)*Complex.exp (-Complex.I*(theta:ℂ))=conj z := by
    dsimp only [z]
    rw [map_sub,map_one,map_mul,Complex.conj_ofReal,← Complex.exp_conj]
    simp
  rw [hc,conjugate_power_product (-alpha) z hz]
  congr 1
  rw [Complex.mul_conj]
  have hh : Complex.normSq z=1-2*r*Real.cos theta+r^(2 : ℕ) := by
    simp [z,Complex.normSq_apply,Complex.exp_re,Complex.exp_im]
    nlinarith [congrArg (fun v : ℝ => r^(2 : ℕ)*v) (Real.sin_sq_add_cos_sq theta)]
  exact congrArg Complex.ofReal hh

private def diskRadius (d : ℝ) : ℝ := Real.sinh d/(Real.cosh d+1)
private def diskScale (d : ℝ) : ℝ := (Real.cosh d+1)/2

private theorem diskScale_positive (d : ℝ) : 0 < diskScale d := by
  unfold diskScale
  positivity

private theorem diskRadius_lt_one (d : ℝ) : |diskRadius d|<1 := by
  have hp : 0 < Real.cosh d+1 := by positivity
  rw [diskRadius,abs_div,abs_of_pos hp,div_lt_one hp]
  have h1 := Real.sinh_lt_cosh (x := d)
  have h2 := Real.sinh_lt_cosh (x := -d)
  rw [Real.sinh_neg,Real.cosh_neg] at h2
  apply abs_lt.mpr
  constructor <;> linarith

private theorem diskRadius_sq (d : ℝ) :
    diskRadius d^(2 : ℕ)=(Real.cosh d-1)/(Real.cosh d+1) := by
  have hp : Real.cosh d+1 ≠ 0 := ne_of_gt (by positivity)
  unfold diskRadius
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq d]

private theorem denominator_disk_factor (d theta : ℝ) :
    denominator d theta=diskScale d*(1-2*diskRadius d*Real.cos theta+diskRadius d^(2 : ℕ)) := by
  rw [diskRadius_sq]
  unfold denominator diskScale diskRadius
  have hp : Real.cosh d+1 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

private theorem height_power_factor (alpha : ℂ) (d theta : ℝ) :
    (height d theta:ℂ)^alpha=(diskScale d:ℂ)^(-alpha)*
      ((1-(diskRadius d:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)*
      (1-(diskRadius d:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha)) := by
  rw [paired_power_product alpha _ _ (diskRadius_lt_one d)]
  have hk : 0 < 1-2*diskRadius d*Real.cos theta+diskRadius d^(2 : ℕ) := by
    have h := denominator_pos d theta
    rw [denominator_disk_factor] at h
    exact (mul_pos_iff_of_pos_left (diskScale_positive d)).mp h
  unfold height
  rw [Complex.ofReal_div,Complex.ofReal_one,one_div,
    Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi
      (Complex.ofReal_mem_slitPlane.mpr (denominator_pos d theta))),← Complex.cpow_neg,
    denominator_disk_factor,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (diskScale_positive d).le hk.le]

/-- The original height-power circle integral equals the actual physical Gauss-series kernel,
with its exact degree and characteristic normalization, for every complex exponent. -/
theorem powerCircle_eq_legendre (alpha : ℂ) (d : ℝ) :
    powerCircle alpha d = D4BMCausalKernel.legendreKernel (-alpha) (Real.cosh d) := by
  unfold powerCircle
  simp only [height_power_factor,average]
  rw [integral_const_mul]
  have h := binomial_product_average alpha (diskRadius d) (diskRadius_lt_one d)
  unfold average at h
  rw [show (1/(2*Real.pi:ℂ))*((diskScale d:ℂ)^(-alpha)*
      (∫ theta in Ioc (0:ℝ) (2*Real.pi),
        (1-(diskRadius d:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)*
        (1-(diskRadius d:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha))) =
      (diskScale d:ℂ)^(-alpha)*((1/(2*Real.pi:ℂ))*
        (∫ theta in Ioc (0:ℝ) (2*Real.pi),
          (1-(diskRadius d:ℂ)*Complex.exp (Complex.I*(theta:ℂ)))^(-alpha)*
          (1-(diskRadius d:ℂ)*Complex.exp (-Complex.I*(theta:ℂ)))^(-alpha))) by ring,h]
  change (diskScale d:ℂ)^(-alpha)*
      (ordinaryHypergeometricSeries ℂ alpha alpha 1).sum ((diskRadius d:ℂ)^(2 : ℕ)) =
    (diskScale d:ℂ)^(-alpha)*
      (ordinaryHypergeometricSeries ℂ (- -alpha) (- -alpha) 1).sum
        (((Real.cosh d-1)/(Real.cosh d+1):ℝ):ℂ)
  rw [neg_neg,← Complex.ofReal_pow,diskRadius_sq]

/-- All three original cusp channels of the full native source use the physical Gauss kernel;
the complete signed Fourier remainder stays in the equality. -/
theorem mean_cusp_expansion_legendre
    (q : XiZeroCopy) (d x k : ℝ) :
    mean q d x k =
      (∑ i : Fin 3, D4BMJointSource.principalAmplitude q i*
        (Real.exp k:ℂ)^(D4BMJointSource.principalExponent q i)*
        D4BMCausalKernel.legendreKernel (-(D4BMJointSource.principalExponent q i)) (Real.cosh d))+
      average (fun theta => D4BMGlobalAngularResponse.squareRemainder
        (D4BMGlobalAngularResponse.center q) (logCircle d theta x k)/2) := by
  rw [mean_cusp_expansion]
  simp only [transportedPrincipal,powerCircle_eq_legendre]

end
end RHTower.D4BMNativeCircle
