import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact restoration of the higher original screening polynomial

The original fifth Taylor polynomial has six nonzero angular slots, through
radial degree ten. Their complete coefficients are derived from admitted cosine
integrals. In particular, the two nonconstant pole coefficients are `β²/4` and
`β²(β-2)²/64`. Every coefficient is analytic in the original exponent.

Polar change of variables and product integrability precede Fubini. In the
original local convergence chamber `α>-2`, integrating the full polynomial
restores all six radial terms. Adding them to the previously admitted fifth
remainder gives exactly the original plane-position integral. The finite terms
of degrees six, eight and ten are retained alongside the three pole terms.

This module does not evaluate the totalized rational expression at its poles.
The explicit pole-cleared source, its higher Gamma continuation, marked finite
jets, complete normalization and mixed Ward producer still require proofs.
No RH hypothesis, source stationarity or physical phase selection is assumed.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem cosine_first : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

private theorem cosine_second : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^2) = Real.pi := by
  rw [integral_cos_sq]
  simp

private theorem cosine_third : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^3) = 0 := by
  rw [integral_cos_pow_three]
  simp

private theorem cosine_fourth : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^4) = 3*Real.pi/4 := by
  rw [show (4:ℕ)=2+2 by rfl, integral_cos_pow, cosine_second]
  simp
  ring

private theorem cosine_fifth : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^5) = 0 := by
  rw [show (5:ℕ)=3+2 by rfl, integral_cos_pow, cosine_third]
  simp

private theorem quintic_cosine_integral (a b c d e f : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi,
      a+b*Real.cos θ+c*Real.cos θ^2+d*Real.cos θ^3+e*Real.cos θ^4+f*Real.cos θ^5) =
        2*Real.pi*a+Real.pi*c+(3*Real.pi/4)*e := by
  have hi (n : ℕ) : IntervalIntegrable (fun θ : ℝ => Real.cos θ^n) volume 0 (2*Real.pi) :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h0 : IntervalIntegrable (fun _ : ℝ => a) volume 0 (2*Real.pi) := intervalIntegrable_const
  have h1 := (hi 1).const_mul b
  have h2 := (hi 2).const_mul c
  have h3 := (hi 3).const_mul d
  have h4 := (hi 4).const_mul e
  have h5 := (hi 5).const_mul f
  simp only [pow_one] at h1
  rw [intervalIntegral.integral_add ((((h0.add h1).add h2).add h3).add h4) h5,
    intervalIntegral.integral_add (((h0.add h1).add h2).add h3) h4,
    intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    cosine_first, cosine_second, cosine_third, cosine_fourth, cosine_fifth,
    mul_zero, add_zero, sub_zero, smul_eq_mul]
  ring

private theorem q_first (r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, (r^2-2*r*Real.cos θ)) = 2*Real.pi*r^2 := by
  have h := quintic_cosine_integral (r^2) (-2*r) 0 0 0 0
  simpa only [zero_mul, add_zero, neg_mul, sub_eq_add_neg, mul_zero] using h

private theorem q_second (r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, (r^2-2*r*Real.cos θ)^2) =
      2*Real.pi*(r^4+2*r^2) := by
  have h := quintic_cosine_integral (r^4) (-4*r^3) (4*r^2) 0 0 0
  have he : (fun θ : ℝ => (r^2-2*r*Real.cos θ)^2) =
      (fun θ : ℝ => r^4+(-4*r^3)*Real.cos θ+(4*r^2)*Real.cos θ^2+
        0*Real.cos θ^3+0*Real.cos θ^4+0*Real.cos θ^5) := by funext θ; ring
  rw [he,h]
  ring

private theorem q_third (r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, (r^2-2*r*Real.cos θ)^3) =
      2*Real.pi*(r^6+6*r^4) := by
  have h := quintic_cosine_integral (r^6) (-6*r^5) (12*r^4) (-8*r^3) 0 0
  have he : (fun θ : ℝ => (r^2-2*r*Real.cos θ)^3) =
      (fun θ : ℝ => r^6+(-6*r^5)*Real.cos θ+(12*r^4)*Real.cos θ^2+
        (-8*r^3)*Real.cos θ^3+0*Real.cos θ^4+0*Real.cos θ^5) := by funext θ; ring
  rw [he,h]
  ring

private theorem q_fourth (r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, (r^2-2*r*Real.cos θ)^4) =
      2*Real.pi*(r^8+12*r^6+6*r^4) := by
  have h := quintic_cosine_integral (r^8) (-8*r^7) (24*r^6) (-32*r^5) (16*r^4) 0
  have he : (fun θ : ℝ => (r^2-2*r*Real.cos θ)^4) =
      (fun θ : ℝ => r^8+(-8*r^7)*Real.cos θ+(24*r^6)*Real.cos θ^2+
        (-32*r^5)*Real.cos θ^3+(16*r^4)*Real.cos θ^4+0*Real.cos θ^5) := by funext θ; ring
  rw [he,h]
  ring

private theorem q_fifth (r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, (r^2-2*r*Real.cos θ)^5) =
      2*Real.pi*(r^10+20*r^8+30*r^6) := by
  have h := quintic_cosine_integral (r^10) (-10*r^9) (40*r^8) (-80*r^7) (80*r^6) (-32*r^5)
  have he : (fun θ : ℝ => (r^2-2*r*Real.cos θ)^5) =
      (fun θ : ℝ => r^10+(-10*r^9)*Real.cos θ+(40*r^8)*Real.cos θ^2+
        (-80*r^7)*Real.cos θ^3+(80*r^6)*Real.cos θ^4+(-32*r^5)*Real.cos θ^5) :=
    by funext θ; ring
  rw [he,h]
  ring

/-- The exact generalized binomial coefficient retained in the original subtraction. -/
def fzzScreeningFifthBinomial (β : ℝ) (j : ℕ) : ℝ :=
  (descPochhammer ℝ j).eval (β/2) / (j.factorial : ℝ)

/-- All radial coefficients of the full fifth polynomial, including the finite tail. -/
def fzzScreeningFifthAngularCoefficient (β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => fzzScreeningFifthBinomial β 1 + 2*fzzScreeningFifthBinomial β 2
  | 2 => fzzScreeningFifthBinomial β 2 + 6*fzzScreeningFifthBinomial β 3 + 6*fzzScreeningFifthBinomial β 4
  | 3 => fzzScreeningFifthBinomial β 3 + 12*fzzScreeningFifthBinomial β 4 + 30*fzzScreeningFifthBinomial β 5
  | 4 => fzzScreeningFifthBinomial β 4 + 20*fzzScreeningFifthBinomial β 5
  | 5 => fzzScreeningFifthBinomial β 5
  | _ => 0

/-- The full angular polynomial has six radial terms, through degree ten. -/
def fzzScreeningFifthAngularPolynomial (β r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 6, fzzScreeningFifthAngularCoefficient β k * r^(2*k)

private theorem binomial_zero (β : ℝ) : fzzScreeningFifthBinomial β 0 = 1 := by
  simp [fzzScreeningFifthBinomial]

private theorem binomial_succ (β : ℝ) (n : ℕ) :
    fzzScreeningFifthBinomial β (n+1) =
      fzzScreeningFifthBinomial β n * (β/2-n)/(n+1) := by
  unfold fzzScreeningFifthBinomial
  rw [descPochhammer_succ_right]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The second radial coefficient is derived from the complete pointwise polynomial. -/
theorem fzzScreeningFifthAngularCoefficient_one (β : ℝ) :
    fzzScreeningFifthAngularCoefficient β 1 = β^2/4 := by
  simp only [fzzScreeningFifthAngularCoefficient]
  simp only [binomial_succ β 1, binomial_succ β 0, binomial_zero]
  norm_num
  ring

/-- The fourth-degree coefficient produces the third collision pole. -/
theorem fzzScreeningFifthAngularCoefficient_two (β : ℝ) :
    fzzScreeningFifthAngularCoefficient β 2 = β^2*(β-2)^2/64 := by
  simp only [fzzScreeningFifthAngularCoefficient]
  simp only [binomial_succ β 3, binomial_succ β 2, binomial_succ β 1,
    binomial_succ β 0, binomial_zero]
  norm_num
  ring

private theorem taylor_circle_integral (β r : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi, fzzScreeningFifthTaylor β (circleMap 0 r θ)) =
      2*Real.pi*fzzScreeningFifthAngularPolynomial β r := by
  have he : (fun θ : ℝ => fzzScreeningFifthTaylor β (circleMap 0 r θ)) =
      (fun θ : ℝ => ∑ j ∈ Finset.range 6,
        fzzScreeningFifthBinomial β j * (r^2-2*r*Real.cos θ)^j) := by
    funext θ
    unfold fzzScreeningFifthTaylor fzzScreeningFifthBinomial
    simp only [norm_circleMap_zero, sq_abs, circleMap_zero_re]
    congr 1
    funext j
    ring
  rw [he, intervalIntegral.integral_finsetSum (fun j _ =>
    (show Continuous (fun θ : ℝ => fzzScreeningFifthBinomial β j *
      (r^2-2*r*Real.cos θ)^j) by fun_prop).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    q_first, q_second, q_third, q_fourth, q_fifth, binomial_zero]
  unfold fzzScreeningFifthAngularPolynomial
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    fzzScreeningFifthAngularCoefficient, mul_zero, pow_zero, one_mul]
  norm_num only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  ring

/-- Angular integration retains every coefficient of the actual subtracted polynomial. -/
theorem fzzScreeningFifthTaylor_circleAverage (β r : ℝ) :
    Real.circleAverage (fzzScreeningFifthTaylor β) 0 r =
      fzzScreeningFifthAngularPolynomial β r := by
  rw [Real.circleAverage_def, smul_eq_mul, taylor_circle_integral]
  field_simp [Real.pi_ne_zero]

private def taylorPolar (α β : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1^(α+1) * fzzScreeningFifthTaylor β (circleMap 0 p.1 p.2)

private theorem taylor_polar_integrable (α β : ℝ) (ha : -2 < α) :
    IntegrableOn (taylorPolar α β) (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hr : IntegrableOn (fun r : ℝ => r^(α+1)) (Ioo 0 (1/2)) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
    linarith
  have hi := hr.mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioo (-Real.pi) Real.pi)))
  simp only [mul_one] at hi
  have hc : Continuous (fun p : ℝ × ℝ => fzzScreeningFifthTaylor β (circleMap 0 p.1 p.2)) := by
    unfold fzzScreeningFifthTaylor circleMap
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn _ (Icc (0:ℝ) (1/2) ×ˢ Icc (-Real.pi) Real.pi))
  rw [Measure.volume_eq_prod]
  change Integrable (taylorPolar α β) ((volume.prod volume).restrict
    (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi))
  rw [← Measure.prod_restrict]
  apply (hi.const_mul C).mono' (by unfold taylorPolar; exact
    (by unfold fzzScreeningFifthTaylor circleMap; fun_prop))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
    (by unfold taylorPolar fzzScreeningFifthTaylor circleMap; fun_prop) (by fun_prop))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  change ‖r^(α+1)*fzzScreeningFifthTaylor β (circleMap 0 r θ)‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (hC (r,θ) ⟨⟨hr.1.le,hr.2.le⟩,⟨hθ.1.le,hθ.2.le⟩⟩) (Real.rpow_nonneg hr.1.le (α+1))

private theorem taylor_disk_polar (α β : ℝ) :
    (∫ z : ℂ in ball 0 (1/2), ‖z‖^α*fzzScreeningFifthTaylor β z) =
      ∫ p : ℝ × ℝ in Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi, taylorPolar α β p := by
  let B := ball (0 : ℂ) (1/2)
  have hB : MeasurableSet B := measurableSet_ball
  have h := Complex.integral_comp_polarCoord_symm
    (B.indicator (fun z : ℂ => ‖z‖^α*fzzScreeningFifthTaylor β z))
  rw [integral_indicator hB] at h
  rw [← h, polarCoord_target]
  have he : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 • B.indicator (fun z : ℂ => ‖z‖^α*fzzScreeningFifthTaylor β z)
        (Complex.polarCoord.symm p) =
      (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi).indicator (taylorPolar α β) p := by
    rintro ⟨r,θ⟩ ⟨hr,hθ⟩
    change 0 < r at hr
    have hs : Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
    have hn : ‖circleMap 0 r θ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
    have hm : circleMap 0 r θ ∈ B ↔ r ∈ Ioo 0 (1/2) := by
      simp only [B, mem_ball_zero_iff, hn, mem_Ioo, hr, true_and]
    rw [hs]
    by_cases hx : r ∈ Ioo 0 (1/2)
    · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem
        (show (r,θ) ∈ Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi from ⟨hx,hθ⟩), smul_eq_mul]
      simp only [taylorPolar, hn, Real.rpow_add hr, Real.rpow_one]
      ring
    · rw [indicator_of_notMem (mt hm.mp hx), indicator_of_notMem
        (fun hh => hx hh.1), smul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) he,
    setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hs : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) ∩
      (Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi) =
        Ioo 0 (1/2) ×ˢ Ioo (-Real.pi) Real.pi :=
    inter_eq_self_of_subset_right (Set.prod_mono (fun _ hr => hr.1) subset_rfl)
  rw [hs]

private theorem taylor_angle_integral (β r : ℝ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, fzzScreeningFifthTaylor β (circleMap 0 r θ)) =
      2*Real.pi*fzzScreeningFifthAngularPolynomial β r := by
  have h := Real.circleAverage_eq_integral_add
    (f := fzzScreeningFifthTaylor β) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right
      (fun θ : ℝ => fzzScreeningFifthTaylor β (circleMap 0 r θ)) (-Real.pi), zero_add,
    show 2*Real.pi+-Real.pi = Real.pi by ring, smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo, fzzScreeningFifthTaylor_circleAverage] at h
  rw [h]
  field_simp [Real.pi_ne_zero]

private theorem taylor_disk_angular (α β : ℝ) (ha : -2 < α) :
    (∫ z : ℂ in ball 0 (1/2), ‖z‖^α*fzzScreeningFifthTaylor β z) =
      2*Real.pi*(∫ r : ℝ in Ioo 0 (1/2), r^(α+1)*fzzScreeningFifthAngularPolynomial β r) := by
  rw [taylor_disk_polar α β, Measure.volume_eq_prod,
    setIntegral_prod _ (taylor_polar_integrable α β ha)]
  simp_rw [taylorPolar, integral_const_mul, taylor_angle_integral]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  ring


/-- All six integrated polynomial terms in the original admission chamber. -/
def fzzScreeningFifthCounterterm (α β : ℝ) : ℝ :=
  2*Real.pi * ∑ k ∈ Finset.range 6,
    fzzScreeningFifthAngularCoefficient β k *
      (1/2 : ℝ)^(α+2*(k:ℝ)+2)/(α+2*(k:ℝ)+2)

private theorem taylor_weight_integrable (α β : ℝ) (ha : -2 < α) :
    IntegrableOn (fun z : ℂ => ‖z‖^α*fzzScreeningFifthTaylor β z) (ball 0 (1/2)) := by
  have hi := (fzzScreeningPlaneKernel_integrable_zero_iff α 0).mpr ha
  change IntegrableOn (fun z : ℂ => ‖z‖^α * ‖z-1‖^(0:ℝ)) (ball 0 (1/2)) at hi
  simp only [Real.rpow_zero, mul_one] at hi
  exact hi.mul_continuousOn_of_subset
    (by unfold fzzScreeningFifthTaylor; fun_prop)
    measurableSet_ball (isCompact_closedBall (0 : ℂ) (1/2)) ball_subset_closedBall

private theorem radial_power_integrable (α : ℝ) (k : ℕ) (ha : -2 < α) :
    IntegrableOn (fun r : ℝ => r^(α+2*(k:ℝ)+1)) (Ioo 0 (1/2)) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  linarith

private theorem radial_power_integral (α : ℝ) (k : ℕ) (ha : -2 < α) :
    (∫ r : ℝ in Ioo 0 (1/2), r^(α+2*(k:ℝ)+1)) =
      (1/2 : ℝ)^(α+2*(k:ℝ)+2)/(α+2*(k:ℝ)+2) := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
    integral_rpow (Or.inl (by linarith : -1 < α+2*(k:ℝ)+1)),
    show α+2*(k:ℝ)+1+1 = α+2*(k:ℝ)+2 by ring,
    Real.zero_rpow (by linarith : α+2*(k:ℝ)+2 ≠ 0), sub_zero]

private theorem taylor_weight_integral (α β : ℝ) (ha : -2 < α) :
    (∫ z : ℂ in ball 0 (1/2), ‖z‖^α*fzzScreeningFifthTaylor β z) =
      fzzScreeningFifthCounterterm α β := by
  rw [taylor_disk_angular α β ha]
  have he : (fun r : ℝ => r^(α+1)*fzzScreeningFifthAngularPolynomial β r) =ᶠ[
      ae (volume.restrict (Ioo 0 (1/2)))]
      (fun r : ℝ => ∑ k ∈ Finset.range 6,
        fzzScreeningFifthAngularCoefficient β k * r^(α+2*(k:ℝ)+1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [fzzScreeningFifthAngularPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Real.rpow_natCast r (2*k)]
    rw [show r^(α+1)*(fzzScreeningFifthAngularCoefficient β k*r^((2*k:ℕ):ℝ)) =
      fzzScreeningFifthAngularCoefficient β k*(r^(α+1)*r^((2*k:ℕ):ℝ)) by ring,
      ← Real.rpow_add hr.1]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae he, integral_finsetSum (Finset.range 6) (fun k _ =>
    (radial_power_integrable α k ha).const_mul (fzzScreeningFifthAngularCoefficient β k))]
  simp_rw [integral_const_mul, radial_power_integral α _ ha]
  unfold fzzScreeningFifthCounterterm
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The full pointwise polynomial is admitted before integrating its angular terms. -/
theorem fzzScreeningFifthTaylor_weight_integrable (u β : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖^(-2+Real.exp u)*fzzScreeningFifthTaylor β z)
      (ball 0 (1/2)) :=
  taylor_weight_integrable _ β (by linarith [Real.exp_pos u])

/-- Restoring the polynomial retains the three pole terms and all three finite terms. -/
theorem fzzScreeningFifthTaylor_weight_integral (u β : ℝ) :
    (∫ z : ℂ in ball 0 (1/2), ‖z‖^(-2+Real.exp u)*fzzScreeningFifthTaylor β z) =
      fzzScreeningFifthCounterterm (-2+Real.exp u) β :=
  taylor_weight_integral _ β (by linarith [Real.exp_pos u])

/-- The restored local source equals the original integral throughout its admission chamber. -/
theorem fzzScreeningFifthSubtracted_original_integral (u β : ℝ) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningPlaneKernel (-2+Real.exp u) β z) =
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (-2+Real.exp u) β z) +
        fzzScreeningFifthCounterterm (-2+Real.exp u) β := by
  have ha : -2 < -2+Real.exp u := by linarith [Real.exp_pos u]
  have hk := (fzzScreeningPlaneKernel_integrable_zero_iff (-2+Real.exp u) β).mpr ha
  have ht := fzzScreeningFifthTaylor_weight_integrable u β
  have he : fzzScreeningFifthSubtracted (-2+Real.exp u) β =
      fun z : ℂ => fzzScreeningPlaneKernel (-2+Real.exp u) β z -
        ‖z‖^(-2+Real.exp u)*fzzScreeningFifthTaylor β z := by
    funext z
    unfold fzzScreeningFifthSubtracted fzzScreeningPlaneKernel
    ring
  rw [he, integral_sub hk ht, fzzScreeningFifthTaylor_weight_integral]
  ring


private theorem binomial_analytic (β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun b => fzzScreeningFifthBinomial b n) β := by
  have h : AnalyticAt ℝ (fun b : ℝ => (descPochhammer ℝ n).eval (b/2)) β :=
    ((analyticAt_id (𝕜 := ℝ) (z := β)).div_const).aeval_polynomial (descPochhammer ℝ n)
  exact h.div_const

/-- Every restored coefficient is an analytic function of the original exponent. -/
theorem fzzScreeningFifthAngularCoefficient_analytic (β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun b => fzzScreeningFifthAngularCoefficient b n) β := by
  rcases n with _ | (_ | (_ | (_ | (_ | (_ | n)))))
  · exact analyticAt_const
  · exact (binomial_analytic β 1).add (analyticAt_const.mul (binomial_analytic β 2))
  · exact ((binomial_analytic β 2).add (analyticAt_const.mul (binomial_analytic β 3))).add
      (analyticAt_const.mul (binomial_analytic β 4))
  · exact ((binomial_analytic β 3).add (analyticAt_const.mul (binomial_analytic β 4))).add
      (analyticAt_const.mul (binomial_analytic β 5))
  · exact (binomial_analytic β 4).add (analyticAt_const.mul (binomial_analytic β 5))
  · exact binomial_analytic β 5
  · exact analyticAt_const


end GaloisForLFunctions.RHTower
