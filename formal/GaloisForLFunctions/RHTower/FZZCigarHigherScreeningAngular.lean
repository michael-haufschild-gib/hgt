import GaloisForLFunctions.RHTower.SteinhausTorusJensenFloor
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Original higher screening angular source

The original inverse-power circle integral admits parameter differentiation on
compact parameter–angle rectangles strictly inside the unit radius. Its exact
recurrence derives the fourth- and sixth-power averages from the admitted Poisson
average. At exponent `-6`, the original angular source has three singular radial
coefficients and an explicit continuous remainder. Their exact primitive and
dominated convergence give its corrected radial cutoff limit.

All public statements discharge their analytic domains from real data. The radial
cutoff theorem concerns the original circle average; planar-annulus transport,
marked higher collision terms and the complete FZZ Ward identity require separate
proofs. No RH assertion or physical stationarity is assumed here.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

/-- The original inverse-power collision factor averaged over a Euclidean circle. -/
def fzzScreeningHigherAngular (n : ℕ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ => (‖1-z‖^(2*n))⁻¹) 0 r

/-- An interior radius, with its analytic domain discharged from real data. -/
def fzzScreeningAngularRadius (u : ℝ) : ℝ := (1+Real.exp u)⁻¹

/-- Exact remainder after the three divergent angular coefficients at exponent `-6`. -/
def fzzScreeningCubicAngularRemainder (r : ℝ) : ℝ :=
  (100-275*r^(2 : ℕ)+316*r^(4 : ℕ)-171*r^(6 : ℕ)+36*r^(8 : ℕ))/(1-r^(2 : ℕ))^(5 : ℕ)

/-- Integrated singular coefficients, before the polar factor `2*pi`. -/
def fzzScreeningCubicCollisionPrimitive (r : ℝ) : ℝ :=
  -(r^(4 : ℕ))⁻¹/4-9*(r^(2 : ℕ))⁻¹/2+36*Real.log r

private def angularQ (r θ : ℝ) : ℝ := 1-2*r*Real.cos θ+r^(2 : ℕ)
private def angularPower (n : ℕ) (r θ : ℝ) : ℝ := (angularQ r θ^n)⁻¹
private def angularMean (n : ℕ) (r : ℝ) : ℝ :=
  (2*Real.pi)⁻¹*(∫ θ : ℝ in Ioc 0 (2*Real.pi), angularPower n r θ)
private def angularPowerDerivative (n : ℕ) (r θ : ℝ) : ℝ :=
  2*((n+1 : ℕ) : ℝ)*(Real.cos θ-r)*(angularQ r θ^(n+2))⁻¹

private theorem angularQ_pos (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < angularQ r θ := by
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (show 0 ≤ 2*r by positivity)
  have hs : 0 < (1-r)^(2 : ℕ) := by
    have h : 0 < 1-r := by linarith
    positivity
  unfold angularQ
  nlinarith

private theorem norm_circle_eq_angularQ (r θ : ℝ) :
    ‖1-(r : ℂ)*circleMap 0 1 θ‖^(2 : ℕ) = angularQ r θ := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, circleMap_zero_re, circleMap_zero_im, one_mul,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  have ht : r^(2 : ℕ)*(Real.sin θ^(2 : ℕ)+Real.cos θ^(2 : ℕ))=r^(2 : ℕ) := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  unfold angularQ
  nlinarith [ht]

private theorem angularMean_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    angularMean 1 r = (1-r^(2 : ℕ))⁻¹ := by
  have h := _root_.RHTower.circleAverage_inv_normSq_one_sub_mul hr0 hr1
  rw [Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)] at h
  simp_rw [norm_circle_eq_angularQ] at h
  simpa only [angularMean, angularPower, pow_one] using h

private theorem angularQ_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun t => angularQ t θ) (2*r-2*Real.cos θ) r := by
  have h := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_id r).const_mul (2*Real.cos θ))).add ((hasDerivAt_id r).pow 2)
  convert! h using 1
  · ext t
    simp only [angularQ, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

private theorem angularPower_hasDerivAt (n : ℕ) (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (fun t => angularPower (n+1) t θ) (angularPowerDerivative n r θ) r := by
  have hq := (angularQ_pos r θ hr0 hr1).ne'
  have h := ((angularQ_hasDerivAt r θ).pow (n+1)).inv (pow_ne_zero _ hq)
  convert! h using 1
  dsimp [angularPowerDerivative]
  simp only [pow_succ]
  field_simp [hq, pow_ne_zero n hq]
  ring

private theorem angularPower_continuous (n : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (angularPower n r) := by
  apply Continuous.inv₀
  · unfold angularQ
    fun_prop
  · intro θ
    exact pow_ne_zero _ (angularQ_pos r θ hr0 hr1).ne'

private theorem angularPowerDerivative_continuous (n : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (angularPowerDerivative n r) := by
  exact (show Continuous (fun θ : ℝ => 2*((n+1 : ℕ) : ℝ)*(Real.cos θ-r)) by fun_prop).mul
    (angularPower_continuous (n+2) r hr0 hr1)

private theorem angularMean_hasDerivAt (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (angularMean (n+1))
      ((2*Real.pi)⁻¹*(∫ θ : ℝ in Ioc 0 (2*Real.pi), angularPowerDerivative n r θ)) r := by
  let lo := r/2
  let hi := (1+r)/2
  let K := Icc lo hi ×ˢ Icc (0 : ℝ) (2*Real.pi)
  have hbounds : ∀ p : ℝ × ℝ, p ∈ K → 0 ≤ p.1 ∧ p.1 < 1 := by
    intro p hp
    dsimp [K,lo,hi] at hp
    constructor <;> linarith [hp.1.1,hp.1.2]
  have hq : ContinuousOn (fun p : ℝ × ℝ => angularQ p.1 p.2) K := by
    unfold angularQ
    fun_prop
  have hinv : ContinuousOn (fun p : ℝ × ℝ => (angularQ p.1 p.2^(n+2))⁻¹) K :=
    (hq.pow (n+2)).inv₀ (fun p hp => pow_ne_zero _
      (angularQ_pos p.1 p.2 (hbounds p hp).1 (hbounds p hp).2).ne')
  have hc : ContinuousOn (fun p : ℝ × ℝ => angularPowerDerivative n p.1 p.2) K :=
    (show ContinuousOn (fun p : ℝ × ℝ => 2*((n+1 : ℕ) : ℝ)*(Real.cos p.2-p.1)) K by
      fun_prop).mul hinv
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hn : Ioo lo hi ∈ 𝓝 r := Ioo_mem_nhds (by dsimp [lo]; linarith) (by dsimp [hi]; linarith)
  have hrange : ∀ t ∈ Ioo lo hi, 0 ≤ t ∧ t < 1 := by
    intro t ht
    dsimp [lo,hi] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2*Real.pi)))
    (F := fun t θ => angularPower (n+1) t θ)
    (F' := fun t θ => angularPowerDerivative n t θ) (bound := fun _ => C) hn
    (by filter_upwards [hn] with t ht
        exact (angularPower_continuous (n+1) t (hrange t ht).1 (hrange t ht).2).aestronglyMeasurable.restrict)
    ((angularPower_continuous (n+1) r hr0.le hr1).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((angularPowerDerivative_continuous n r hr0.le hr1).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
        intro t ht
        exact hC (t,θ) ⟨⟨ht.1.le,ht.2.le⟩,⟨hθ.1.le,hθ.2⟩⟩)
    (integrable_const C)
    (by filter_upwards with θ
        intro t ht
        exact angularPower_hasDerivAt n t θ (hrange t ht).1 (hrange t ht).2)).2
  exact hd.const_mul (2*Real.pi)⁻¹

private theorem angularPower_recurrence (n : ℕ) (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r*angularPowerDerivative n r θ =
      ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularPower (n+2) r θ-angularPower (n+1) r θ) := by
  have hq := (angularQ_pos r θ hr0 hr1).ne'
  unfold angularPowerDerivative angularPower
  simp only [pow_succ]
  field_simp [hq, pow_ne_zero n hq]
  unfold angularQ
  ring

private theorem angularMean_recurrence (n : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    r*deriv (angularMean (n+1)) r =
      ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularMean (n+2) r-angularMean (n+1) r) := by
  have h1 : IntegrableOn (angularPower (n+1) r) (Ioc 0 (2*Real.pi)) :=
    (angularPower_continuous (n+1) r hr0.le hr1).integrableOn_Icc.mono_set
    (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  have h2 : IntegrableOn (angularPower (n+2) r) (Ioc 0 (2*Real.pi)) :=
    (angularPower_continuous (n+2) r hr0.le hr1).integrableOn_Icc.mono_set
    (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 2*Real.pi))
  rw [(angularMean_hasDerivAt n r hr0 hr1).deriv]
  have hi : (∫ θ : ℝ in Ioc 0 (2*Real.pi), r*angularPowerDerivative n r θ) =
      ∫ θ : ℝ in Ioc 0 (2*Real.pi),
        ((n+1 : ℕ) : ℝ)*((1-r^(2 : ℕ))*angularPower (n+2) r θ-angularPower (n+1) r θ) := by
    apply integral_congr_ae
    filter_upwards with θ
    exact angularPower_recurrence n r θ hr0.le hr1
  rw [integral_const_mul, integral_const_mul, integral_sub (h2.const_mul _) h1,
    integral_const_mul] at hi
  unfold angularMean
  linear_combination (2*Real.pi)⁻¹*hi

private theorem angularDen_pos (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < 1-r^(2 : ℕ) := by
  nlinarith [mul_pos (sub_pos.mpr hr1) (show 0 < 1+r by linarith)]

private theorem angularDen_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => 1-t^(2 : ℕ)) (-2*r) r := by
  convert! (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2) using 1
  simp

private theorem angularMean_two (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    angularMean 2 r = (1+r^(2 : ℕ))/(1-r^(2 : ℕ))^(3 : ℕ) := by
  have hn := (angularDen_pos r hr0.le hr1).ne'
  have hd : HasDerivAt (fun t : ℝ => (1-t^(2 : ℕ))⁻¹) (2*r/(1-r^(2 : ℕ))^(2 : ℕ)) r := by
    convert! (angularDen_hasDerivAt r).inv hn using 1
    simp
  have he : angularMean 1 =ᶠ[𝓝 r] (fun t : ℝ => (1-t^(2 : ℕ))⁻¹) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with t ht
    exact angularMean_one t ht.1.le ht.2
  have h := angularMean_recurrence 0 r hr0 hr1
  rw [(hd.congr_of_eventuallyEq he).deriv, angularMean_one r hr0.le hr1] at h
  simp only [Nat.zero_add, Nat.cast_one, one_mul] at h
  field_simp [hn] at h ⊢
  nlinarith [h]

private theorem angularMean_three (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    angularMean 3 r = (1+4*r^(2 : ℕ)+r^(4 : ℕ))/(1-r^(2 : ℕ))^(5 : ℕ) := by
  have hn := (angularDen_pos r hr0.le hr1).ne'
  have hnum : HasDerivAt (fun t : ℝ => 1+t^(2 : ℕ)) (2*r) r := by
    convert! (hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow 2) using 1
    simp
  have hd : HasDerivAt (fun t : ℝ => (1+t^(2 : ℕ))/(1-t^(2 : ℕ))^(3 : ℕ))
      (4*r*(2+r^(2 : ℕ))/(1-r^(2 : ℕ))^(4 : ℕ)) r := by
    convert! hnum.div ((angularDen_hasDerivAt r).pow 3) (pow_ne_zero _ hn) using 1
    dsimp
    field_simp [hn]
    ring
  have he : angularMean 2 =ᶠ[𝓝 r] (fun t : ℝ => (1+t^(2 : ℕ))/(1-t^(2 : ℕ))^(3 : ℕ)) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with t ht
    exact angularMean_two t ht.1 ht.2
  have h := angularMean_recurrence 1 r hr0 hr1
  rw [(hd.congr_of_eventuallyEq he).deriv, angularMean_two r hr0 hr1] at h
  simp only [Nat.reduceAdd, Nat.cast_ofNat] at h
  field_simp [hn] at h ⊢
  nlinarith [h]

private theorem higherAngular_eq_mean (n : ℕ) (r : ℝ) :
    fzzScreeningHigherAngular n r = angularMean n r := by
  rw [fzzScreeningHigherAngular, Real.circleAverage_eq_circleAverage_zero_one,
    Real.circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  simp only [add_zero, angularMean, angularPower, pow_mul, norm_circle_eq_angularQ]

private theorem angularRadius_range (u : ℝ) :
    0 < fzzScreeningAngularRadius u ∧ fzzScreeningAngularRadius u < 1 := by
  have hp := Real.exp_pos u
  constructor
  · unfold fzzScreeningAngularRadius
    positivity
  · rw [fzzScreeningAngularRadius, inv_lt_one₀ (by positivity)]
    linarith

/-- Parameter differentiation of the original angular integral gives its exact recurrence. -/
theorem fzzScreeningHigherAngular_recurrence (n : ℕ) (u : ℝ) :
    fzzScreeningAngularRadius u *
        deriv (fzzScreeningHigherAngular (n+1)) (fzzScreeningAngularRadius u) =
      ((n+1 : ℕ) : ℝ)*((1-fzzScreeningAngularRadius u^(2 : ℕ))*
        fzzScreeningHigherAngular (n+2) (fzzScreeningAngularRadius u)-
        fzzScreeningHigherAngular (n+1) (fzzScreeningAngularRadius u)) := by
  have he : fzzScreeningHigherAngular (n+1) = angularMean (n+1) :=
    funext (higherAngular_eq_mean (n+1))
  rw [he, higherAngular_eq_mean]
  exact angularMean_recurrence n _ (angularRadius_range u).1 (angularRadius_range u).2

/-- The original inverse fourth-power average. -/
theorem fzzScreeningHigherAngular_two (u : ℝ) :
    fzzScreeningHigherAngular 2 (fzzScreeningAngularRadius u) =
      (1+fzzScreeningAngularRadius u^(2 : ℕ))/(1-fzzScreeningAngularRadius u^(2 : ℕ))^(3 : ℕ) := by
  rw [higherAngular_eq_mean]
  exact angularMean_two _ (angularRadius_range u).1 (angularRadius_range u).2

/-- The original inverse sixth-power average needed by the `k=4` collision. -/
theorem fzzScreeningHigherAngular_three (u : ℝ) :
    fzzScreeningHigherAngular 3 (fzzScreeningAngularRadius u) =
      (1+4*fzzScreeningAngularRadius u^(2 : ℕ)+fzzScreeningAngularRadius u^(4 : ℕ))/
        (1-fzzScreeningAngularRadius u^(2 : ℕ))^(5 : ℕ) := by
  rw [higherAngular_eq_mean]
  exact angularMean_three _ (angularRadius_range u).1 (angularRadius_range u).2

private theorem cubic_remainder (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    fzzScreeningHigherAngular 3 r =
      1+9*r^(2 : ℕ)+36*r^(4 : ℕ)+r^(6 : ℕ)*fzzScreeningCubicAngularRemainder r := by
  rw [higherAngular_eq_mean, angularMean_three r hr0 hr1]
  unfold fzzScreeningCubicAngularRemainder
  field_simp [(angularDen_pos r hr0.le hr1).ne']
  ring

/-- All three singular radial coefficients are derived from the original source. -/
theorem fzzScreeningHigherAngular_three_remainder (u : ℝ) :
    fzzScreeningHigherAngular 3 (fzzScreeningAngularRadius u) =
      1+9*fzzScreeningAngularRadius u^(2 : ℕ)+36*fzzScreeningAngularRadius u^(4 : ℕ)+
        fzzScreeningAngularRadius u^(6 : ℕ)*
          fzzScreeningCubicAngularRemainder (fzzScreeningAngularRadius u) :=
  cubic_remainder _ (angularRadius_range u).1 (angularRadius_range u).2

private theorem cubicRemainder_continuousOn :
    ContinuousOn fzzScreeningCubicAngularRemainder (Icc 0 (1/2 : ℝ)) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro r hr
    exact pow_ne_zero _ (angularDen_pos r hr.1 (by linarith [hr.2])).ne'

/-- After angular integration, subtracting these coefficients leaves an admitted radial source. -/
theorem fzzScreeningHigherAngular_three_subtracted_integrable :
    IntegrableOn (fun r : ℝ => (r^(5 : ℕ))⁻¹*(fzzScreeningHigherAngular 3 r-1-9*r^(2 : ℕ)-36*r^(4 : ℕ)))
      (Ioc 0 (1/2 : ℝ)) := by
  have hi : IntegrableOn (fun r : ℝ => r*fzzScreeningCubicAngularRemainder r)
      (Ioc 0 (1/2 : ℝ)) :=
    ((continuous_id.continuousOn.mul cubicRemainder_continuousOn).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [cubic_remainder r hr.1 (by linarith [hr.2])]
  field_simp [hr.1.ne']
  ring

private theorem cubicPrimitive_hasDerivAt (r : ℝ) (hr : 0 < r) :
    HasDerivAt fzzScreeningCubicCollisionPrimitive
      ((r^(5 : ℕ))⁻¹+9*(r^(3 : ℕ))⁻¹+36*r⁻¹) r := by
  have h4 := ((hasDerivAt_id r).pow 4).inv (pow_ne_zero _ hr.ne')
  have h2 := ((hasDerivAt_id r).pow 2).inv (pow_ne_zero _ hr.ne')
  have h := ((h4.neg.div_const 4).sub ((h2.const_mul 9).div_const 2)).add
    ((Real.hasDerivAt_log hr.ne').const_mul 36)
  convert! h using 1
  dsimp
  field_simp [hr.ne']
  ring

private theorem cubic_angular_cutoff_identity (ε : ℝ) (hε : 0 < ε) (hεR : ε ≤ 1/2) :
    (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherAngular 3 r)+
        fzzScreeningCubicCollisionPrimitive ε =
      (∫ r : ℝ in ε..(1/2), r*fzzScreeningCubicAngularRemainder r)+
        fzzScreeningCubicCollisionPrimitive (1/2) := by
  have hp : ContinuousOn (fun r : ℝ => (r^(5 : ℕ))⁻¹+9*(r^(3 : ℕ))⁻¹+36*r⁻¹) (Icc ε (1/2)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact (continuous_id.continuousOn.pow 5).inv₀
          (fun r hr => pow_ne_zero _ (hε.trans_le hr.1).ne')
      · exact continuousOn_const.mul ((continuous_id.continuousOn.pow 3).inv₀
          (fun r hr => pow_ne_zero _ (hε.trans_le hr.1).ne'))
    · exact continuousOn_const.mul (continuous_id.continuousOn.inv₀
        (fun r hr => (hε.trans_le hr.1).ne'))
  have hrem : ContinuousOn (fun r : ℝ => r*fzzScreeningCubicAngularRemainder r)
      (Icc ε (1/2)) := (continuous_id.continuousOn.mul cubicRemainder_continuousOn).mono
    (fun r hr => ⟨hε.le.trans hr.1,hr.2⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => cubicPrimitive_hasDerivAt r (by
      rw [uIcc_of_le hεR] at hr
      exact hε.trans_le hr.1)) (hp.intervalIntegrable_of_Icc hεR)
  have he : (∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherAngular 3 r) =
      ∫ r : ℝ in ε..(1/2), (r^(5 : ℕ))⁻¹+9*(r^(3 : ℕ))⁻¹+36*r⁻¹+
        r*fzzScreeningCubicAngularRemainder r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hεR] at hr
    have hr0 := hε.trans_le hr.1
    dsimp only
    rw [cubic_remainder r hr0 (by linarith [hr.2])]
    field_simp [hr0.ne']
  rw [he, intervalIntegral.integral_add (hp.intervalIntegrable_of_Icc hεR)
    (hrem.intervalIntegrable_of_Icc hεR), hi]
  ring

private theorem cubic_remainder_cutoff_limit :
    Tendsto (fun T : ℝ => ∫ r : ℝ in (Real.exp (-T))..(1/2),
      r*fzzScreeningCubicAngularRemainder r) atTop
      (𝓝 (∫ r : ℝ in (0 : ℝ)..(1/2), r*fzzScreeningCubicAngularRemainder r)) := by
  let f := fun r : ℝ => r*fzzScreeningCubicAngularRemainder r
  have hi : IntegrableOn f (Ioc 0 (1/2)) :=
    ((continuous_id.continuousOn.mul cubicRemainder_continuousOn).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hd := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict (Ioc (0 : ℝ) (1/2)))
    (F := fun T : ℝ => (Ioi (Real.exp (-T))).indicator f) (f := f) (fun r => ‖f r‖)
    (Eventually.of_forall (fun T => hi.aestronglyMeasurable.indicator measurableSet_Ioi))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun r => by
      by_cases hr : r ∈ Ioi (Real.exp (-T))
      · simp [indicator_of_mem hr]
      · simp [indicator_of_notMem hr]))) hi.norm (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        apply tendsto_const_nhds.congr'
        filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
          (gt_mem_nhds hr.1)] with T hT
        exact (indicator_of_mem hT f).symm)
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) ≤ (1/2 : ℝ) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))).mono (fun T hT => hT.le)
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1/2)]
  apply hd.congr'
  filter_upwards [he] with T hT
  rw [setIntegral_indicator measurableSet_Ioi, intervalIntegral.integral_of_le hT]
  have hs : Ioc (0 : ℝ) (1/2) ∩ Ioi (Real.exp (-T)) = Ioc (Real.exp (-T)) (1/2) := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_,hr⟩,hTr⟩
      exact ⟨hTr,hr⟩
    · rintro ⟨hTr,hr⟩
      exact ⟨⟨(Real.exp_pos _).trans hTr,hr⟩,hTr⟩
  rw [hs]

/-- The original angular source has the forced two-power and logarithmic cutoff correction. -/
theorem fzzScreeningHigherAngular_three_cutoff_limit :
    Tendsto (fun T : ℝ => 2*Real.pi*
      ((∫ r : ℝ in (Real.exp (-T))..(1/2), (r^(5 : ℕ))⁻¹*fzzScreeningHigherAngular 3 r)+
        fzzScreeningCubicCollisionPrimitive (Real.exp (-T)))) atTop
      (𝓝 (2*Real.pi*((∫ r : ℝ in (0 : ℝ)..(1/2),
        r*fzzScreeningCubicAngularRemainder r)+fzzScreeningCubicCollisionPrimitive (1/2)))) := by
  have hd := (cubic_remainder_cutoff_limit.add_const
    (fzzScreeningCubicCollisionPrimitive (1/2))).const_mul (2*Real.pi)
  apply hd.congr'
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1/2))] with T hT
  rw [cubic_angular_cutoff_identity _ (Real.exp_pos _) hT.le]

end GaloisForLFunctions.RHTower
