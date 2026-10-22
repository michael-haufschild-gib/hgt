import GaloisForLFunctions.RHTower.FZZCigarCubicFinitePartExtraction
import GaloisForLFunctions.RHTower.FZZCigarCubicMarkedScreeningCutoff

/-!
# Original higher screening remainder derivatives

Both logarithmic insertions are derived from the admitted original fifth
subtraction. Neighboring powers admit the singular-factor logarithmic moment.
For the regular factor, differentiation of the exact pointwise Taylor integral
remainder retains both the descending-factorial derivative and the lifted
logarithmic moment. Joint integrability precedes Fubini and identifies the
original differentiated subtraction before differentiating its plane integral.

The full cubic Taylor-mark polynomial and its six-slot angular average are
retained, including finite radial terms. The original exterior derivative
then assembles with both distinct local derivatives into the complete cubic
regular-source derivative. Public theorems have only real or complex data;
all domain and integrability conditions are proved internally.

Original marked cutoff extraction, fractional screening continuation, complete
physical normalization, phase-frame identification and mixed Ward production
remain separate obligations. No RH conclusion is claimed here.
-/

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def positiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))



private theorem positive_sub_negative (r : ℝ) : max r 0-max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), sub_zero]
  · rw [max_eq_right (le_of_not_ge hr), max_eq_left (neg_nonneg.mpr (le_of_not_ge hr))]
    ring


private theorem fifth_admission (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fzzScreeningFifthSubtracted α β) (ball 0 (1/2)) := by
  have h := fzzScreeningFifthSubtracted_integrable (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h


private theorem fifth_singular_marked_source (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted α β z)
      (ball 0 (1/2)) ∧
    HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (α+δ) β z)
      (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningFifthSubtracted α β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, -8 < α+δ :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa using ha)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningFifthSubtracted α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict (ball 0 (1/2))) := by
    filter_upwards [hshift] with δ hδ
    apply (fifth_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (fifth_subtracted_shift α β δ hz).symm
  have h := signed_exp_hasDerivAt (volume.restrict (ball (0 : ℂ) (1/2)))
    (fzzScreeningFifthSubtracted α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningFifthSubtracted fzzScreeningFifthTaylor; fun_prop) (by fun_prop) 0 hi
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have he : (fun δ => ∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (α+δ) β z) =ᶠ[𝓝 0]
      (fun δ => ∫ z : ℂ in ball 0 (1/2),
        fzzScreeningFifthSubtracted α β z*Real.exp (δ*Real.log ‖z‖)) := by
    filter_upwards with δ
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (fifth_subtracted_shift α β δ hz).symm
  constructor
  · simpa only [IntegrableOn, mul_comm] using h.1
  · simpa only [mul_comm] using h.2.congr_of_eventuallyEq he

theorem fzzScreeningFifthSubtracted_singularMark_integrable (u β : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted (-8+Real.exp u) β z)
      (ball 0 (1/2)) :=
  (fifth_singular_marked_source _ β (by linarith [Real.exp_pos u])).1

theorem fzzScreeningFifthSubtracted_singularMark_hasDerivAt (u β : ℝ) :
    HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u+δ) β z)
      (∫ z : ℂ in ball 0 (1/2),
        Real.log ‖z‖*fzzScreeningFifthSubtracted (-8+Real.exp u) β z) 0 :=
  (fifth_singular_marked_source _ β (by linarith [Real.exp_pos u])).2



private theorem plane_q_identity (z : ℂ) :
    1+(‖z‖^(2 : ℕ)-2*z.re) = ‖z-1‖^(2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring


/-- Derivative of every coefficient in the original fifth subtraction. -/
def fzzScreeningFifthTaylorMark (β : ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    (descPochhammer ℝ j).derivative.eval (β/2) / (2*(j.factorial : ℝ)) *
      (‖z‖^(2 : ℕ)-2*z.re)^j

/-- The regular-factor logarithmic insertion retains the differentiated subtraction. -/
def fzzScreeningFifthRegularMark (α β : ℝ) (z : ℂ) : ℝ :=
  ‖z‖^α * (Real.log ‖z-1‖*‖z-1‖^β - fzzScreeningFifthTaylorMark β z)

private theorem pochhammer_half_deriv (j : ℕ) (β : ℝ) :
    HasDerivAt (fun s : ℝ => (descPochhammer ℝ j).eval (s/2))
      ((descPochhammer ℝ j).derivative.eval (β/2)/2) β := by
  simpa only [Function.comp_def,mul_one_div,id_eq] using
    ((descPochhammer ℝ j).hasDerivAt (β/2)).comp β ((hasDerivAt_id β).div_const 2)

private theorem fifth_taylor_deriv (β : ℝ) (z : ℂ) :
    HasDerivAt (fun s => fzzScreeningFifthTaylor s z) (fzzScreeningFifthTaylorMark β z) β := by
  have h := HasDerivAt.fun_sum (u := Finset.range 6) (fun j _ =>
    ((pochhammer_half_deriv j β).div_const (j.factorial : ℝ)).mul_const ((‖z‖^(2 : ℕ)-2*z.re)^j))
  apply h.congr_deriv
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem fifth_regular_point_deriv (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    HasDerivAt (fun s => fzzScreeningFifthSubtracted α s z)
      (fzzScreeningFifthRegularMark α β z) β := by
  have hn : 0 < ‖z-1‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hz' : z=1 := sub_eq_zero.mp he
    have hh : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [hz',norm_one] at hh
    norm_num at hh
  have h := HasDerivAt.const_rpow hn (hasDerivAt_id β)
  simpa only [mul_one,id_eq,Pi.sub_apply,fzzScreeningFifthSubtracted,fzzScreeningFifthRegularMark]
    using (h.sub (fifth_taylor_deriv β z)).const_mul (‖z‖^α)

private theorem fifth_lift_admission (α β : ℝ) (ha : -8 < α) :
    Integrable (fun p => fzzScreeningFifthLiftWeight α p *
      Real.exp (β*fzzScreeningFifthLiftLog p)) fzzScreeningFifthLiftMeasure :=
  fifth_lift_exp_integrable α β ha

private theorem fifth_lift_source (α β : ℝ) (ha : -8 < α) :
    Integrable (fun p => fzzScreeningFifthLiftWeight α p *
      (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p)))
        fzzScreeningFifthLiftMeasure ∧
    HasDerivAt (fun s => ∫ p, fzzScreeningFifthLiftWeight α p *
      Real.exp (s*fzzScreeningFifthLiftLog p) ∂fzzScreeningFifthLiftMeasure)
      (∫ p, fzzScreeningFifthLiftWeight α p *
        (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p))
          ∂fzzScreeningFifthLiftMeasure) β :=
  signed_exp_hasDerivAt _ _ _ (by unfold fzzScreeningFifthLiftWeight; fun_prop)
    (by unfold fzzScreeningFifthLiftLog; fun_prop) β
    (Eventually.of_forall (fun s => fifth_lift_admission α s ha))

private theorem fifth_slice_admission (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    IntegrableOn (fun t => fzzScreeningFifthLiftWeight α (z,t)*
      Real.exp (β*fzzScreeningFifthLiftLog (z,t))) (Ioc 0 1) := by
  have hp : ∀ t ∈ Icc (0:ℝ) 1, 0 < 1+(‖z‖^(2 : ℕ)-2*z.re)*t := by
    intro t ht
    exact lt_of_lt_of_le (by norm_num) (affine_base_bounds _ t (plane_q_bounds z hz).1 ht).1
  have hc : ContinuousOn (fun t : ℝ => 1+(‖z‖^(2 : ℕ)-2*z.re)*t) (Icc 0 1) := by fun_prop
  have hr := hc.rpow_const (fun t ht => Or.inl (hp t ht).ne') (p := (-6:ℝ))
  have hl := hc.log (fun t ht => (hp t ht).ne')
  have hh : ContinuousOn (fun t => fzzScreeningFifthLiftWeight α (z,t)*
      Real.exp (β*fzzScreeningFifthLiftLog (z,t))) (Icc 0 1) := by
    unfold fzzScreeningFifthLiftWeight fzzScreeningFifthLiftLog
    change ContinuousOn (fun t : ℝ =>
      (‖z‖^α*(‖z‖^(2 : ℕ)-2*z.re)^(6 : ℕ))*((1-t)^(5 : ℕ) / ((5:ℕ).factorial:ℝ))*
        (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(-6:ℝ)*
          Real.exp (β*(Real.log (1+(‖z‖^(2 : ℕ)-2*z.re)*t)/2))) (Icc 0 1)
    have hc0 : ContinuousOn (fun t : ℝ =>
        (‖z‖^α*(‖z‖^(2 : ℕ)-2*z.re)^(6 : ℕ))*((1-t)^(5 : ℕ) / ((5:ℕ).factorial:ℝ))) (Icc 0 1) := by
      fun_prop
    exact (hc0.mul hr).mul
      (Real.continuous_exp.comp_continuousOn ((hl.div_const 2).const_mul β))
  exact (hh.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

private theorem fifth_regular_mark_lift (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    fzzScreeningFifthRegularMark α β z =
      ((descPochhammer ℝ 6).derivative.eval (β/2)/2)*
        (∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t)*
          Real.exp (β*fzzScreeningFifthLiftLog (z,t))) +
      (descPochhammer ℝ 6).eval (β/2)*
        (∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t)*
          (fzzScreeningFifthLiftLog (z,t)*Real.exp (β*fzzScreeningFifthLiftLog (z,t)))) := by
  have h := signed_exp_hasDerivAt (volume.restrict (Ioc (0:ℝ) 1))
    (fun t => fzzScreeningFifthLiftWeight α (z,t)) (fun t => fzzScreeningFifthLiftLog (z,t))
    (by unfold fzzScreeningFifthLiftWeight; fun_prop)
    (by unfold fzzScreeningFifthLiftLog; fun_prop) β
    (Eventually.of_forall (fun s => fifth_slice_admission α s z hz))
  have hd := ((pochhammer_half_deriv 6 β).mul h.2).congr_of_eventuallyEq
    (Eventually.of_forall (fun s => fifth_subtracted_lift_pointwise α s z hz))
  exact (fifth_regular_point_deriv α β z hz).unique hd

private theorem fifth_regular_mark_integrable (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fzzScreeningFifthRegularMark α β) (ball 0 (1/2)) := by
  have hi := (fifth_lift_admission α β ha).integral_prod_left
  have hm := (fifth_lift_source α β ha).1.integral_prod_left
  apply ((hi.const_mul ((descPochhammer ℝ 6).derivative.eval (β/2)/2)).add
    (hm.const_mul ((descPochhammer ℝ 6).eval (β/2)))).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact (fifth_regular_mark_lift α β z (ball_subset_closedBall hz)).symm

private theorem fifth_regular_mark_integral (α β : ℝ) (ha : -8 < α) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark α β z) =
      ((descPochhammer ℝ 6).derivative.eval (β/2)/2)*
        (∫ p, fzzScreeningFifthLiftWeight α p*Real.exp (β*fzzScreeningFifthLiftLog p)
          ∂fzzScreeningFifthLiftMeasure) +
      (descPochhammer ℝ 6).eval (β/2)*
        (∫ p, fzzScreeningFifthLiftWeight α p*
          (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p))
            ∂fzzScreeningFifthLiftMeasure) := by
  have hi := (fifth_lift_admission α β ha).integral_prod_left
  have hm := (fifth_lift_source α β ha).1.integral_prod_left
  rw [fzzScreeningFifthLiftMeasure, integral_prod _ (fifth_lift_admission α β ha),
    integral_prod _ (fifth_lift_source α β ha).1, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul _) (hm.const_mul _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact fifth_regular_mark_lift α β z (ball_subset_closedBall hz)

theorem fzzScreeningFifthRegularMark_integrable (u β : ℝ) :
    IntegrableOn (fzzScreeningFifthRegularMark (-8+Real.exp u) β) (ball 0 (1/2)) :=
  fifth_regular_mark_integrable _ β (by linarith [Real.exp_pos u])

theorem fzzScreeningFifthSubtracted_regularMark_hasDerivAt (u β : ℝ) :
    HasDerivAt (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u) s z)
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-8+Real.exp u) β z) β := by
  rw [fifth_regular_mark_integral _ β (by linarith [Real.exp_pos u])]
  exact ((pochhammer_half_deriv 6 β).mul
    (fifth_lift_source _ β (by linarith [Real.exp_pos u])).2).congr_of_eventuallyEq
      (Eventually.of_forall (fun s => fzzScreeningFifthSubtracted_lift_identity u s))

theorem fzzScreeningFifthTaylorMark_cubic (z : ℂ) :
    fzzScreeningFifthTaylorMark (-6) z =
      (‖z‖^(2 : ℕ)-2*z.re)/2-7*(‖z‖^(2 : ℕ)-2*z.re)^(2 : ℕ)/4+47*(‖z‖^(2 : ℕ)-2*z.re)^(3 : ℕ)/12-
        57*(‖z‖^(2 : ℕ)-2*z.re)^(4 : ℕ)/8+459*(‖z‖^(2 : ℕ)-2*z.re)^(5 : ℕ)/40 := by
  simp only [fzzScreeningFifthTaylorMark,Finset.sum_range_succ,Finset.sum_range_zero,
    descPochhammer_succ_right,descPochhammer_zero,Polynomial.derivative_mul,
    Polynomial.derivative_sub,Polynomial.derivative_X,Polynomial.derivative_natCast,
    Polynomial.derivative_one,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_zero,Polynomial.eval_X,Polynomial.eval_natCast]
  norm_num
  ring

private theorem cosine_first : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

private theorem cosine_second : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(2 : ℕ)) = Real.pi := by
  rw [integral_cos_sq]
  simp

private theorem cosine_third : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(3 : ℕ)) = 0 := by
  rw [integral_cos_pow_three]
  simp


private theorem cosine_fifth : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(5 : ℕ)) = 0 := by
  rw [show (5:ℕ)=3+2 by rfl, integral_cos_pow, cosine_third]
  simp


theorem fzzScreeningFifthTaylorMark_cubic_circleAverage (r : ℝ) :
    Real.circleAverage (fzzScreeningFifthTaylorMark (-6)) 0 r =
      -3*r^(2 : ℕ)-21*r^(4 : ℕ)+(788/3)*r^(6 : ℕ)+(1779/8)*r^(8 : ℕ)+(459/40)*r^(10 : ℕ) := by
  have h := quintic_cosine_integral
    (r^(2 : ℕ)/2-7*r^(4 : ℕ)/4+47*r^(6 : ℕ)/12-57*r^(8 : ℕ)/8+459*r^(10 : ℕ)/40)
    (-r+7*r^(3 : ℕ)-47*r^(5 : ℕ)/2+57*r^(7 : ℕ)-459*r^(9 : ℕ)/4)
    (-7*r^(2 : ℕ)+47*r^(4 : ℕ)-171*r^(6 : ℕ)+459*r^(8 : ℕ))
    (-94*r^(3 : ℕ)/3+228*r^(5 : ℕ)-918*r^(7 : ℕ))
    (-114*r^(4 : ℕ)+918*r^(6 : ℕ)) (-1836*r^(5 : ℕ)/5)
  have he : (fun θ : ℝ => fzzScreeningFifthTaylorMark (-6) (circleMap 0 r θ)) =
      (fun θ : ℝ =>
        (r^(2 : ℕ)/2-7*r^(4 : ℕ)/4+47*r^(6 : ℕ)/12-57*r^(8 : ℕ)/8+459*r^(10 : ℕ)/40)+
        (-r+7*r^(3 : ℕ)-47*r^(5 : ℕ)/2+57*r^(7 : ℕ)-459*r^(9 : ℕ)/4)*Real.cos θ+
        (-7*r^(2 : ℕ)+47*r^(4 : ℕ)-171*r^(6 : ℕ)+459*r^(8 : ℕ))*Real.cos θ^(2 : ℕ)+
        (-94*r^(3 : ℕ)/3+228*r^(5 : ℕ)-918*r^(7 : ℕ))*Real.cos θ^(3 : ℕ)+
        (-114*r^(4 : ℕ)+918*r^(6 : ℕ))*Real.cos θ^(4 : ℕ)+(-1836*r^(5 : ℕ)/5)*Real.cos θ^(5 : ℕ)) := by
    funext θ
    rw [fzzScreeningFifthTaylorMark_cubic]
    simp only [norm_circleMap_zero,sq_abs,circleMap_zero_re]
    ring
  rw [Real.circleAverage_def,smul_eq_mul,he,h]
  field_simp [Real.pi_ne_zero]
  ring


theorem fzzScreeningCubicExteriorMark_hasDerivAt :
    HasDerivAt (fun α => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel α (-6) z)
      (∫ z : ℂ in fzzScreeningPlaneExterior,
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z) (-6) := by
  have h0 := (exterior_marked_source (-6) (-6) (by norm_num)).2
  have h := HasDerivAt.comp_sub_const (-6 : ℝ) (-6)
    (by simpa only [sub_self] using h0)
  simpa only [zero_add,show ∀ s : ℝ, -6+(s-(-6))=s by intro s; ring] using h

/-- Differentiation of the complete original regular part retains both distinct
local insertions and the original exterior logarithmic insertion. -/
theorem fzzScreeningCubicOriginalRemainders_hasDerivAt :
    HasDerivAt (fun α =>
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted α (-6) z)+
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (-6) α z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α (-6) z))
      ((∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z)+
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-6) (-6) z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior,
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)) (-6) := by
  have h0 := (fifth_singular_marked_source (-6) (-6) (by norm_num)).2
  have hs := HasDerivAt.comp_sub_const (-6 : ℝ) (-6)
    (by simpa only [sub_self] using h0)
  simp only [show ∀ s : ℝ, -6+(s-(-6))=s by intro s; ring] at hs
  have hr := fzzScreeningFifthSubtracted_regularMark_hasDerivAt (Real.log 2) (-6)
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hr
  norm_num only at hr
  exact (hs.fun_add hr).fun_add fzzScreeningCubicExteriorMark_hasDerivAt

end GaloisForLFunctions.RHTower
