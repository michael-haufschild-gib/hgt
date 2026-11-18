import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.CountingHolography.Sections.ThePrimeProfileOfThreeSquareConductors
import Mathlib.NumberTheory.AbelSummation

/-!
# Proper prime-power mass in a moving spline window

The cumulative mass of proper powers is asymptotic to the square root.
Abel summation transfers this to the compact spline profile at each
moving long lag of a square conductor.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Finset ArithmeticFunction
open ArithmeticWeightTheory ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge
open _root_.RHTower.WeilDeletion SquareRootThreshold

private abbrev powerMass (x : ℝ) := Chebyshev.psi x-Chebyshev.theta x
private def powerWeight (k : ℕ) : ℝ := if k.Prime then 0 else vonMangoldt k

/-- The first surviving prime exponent is two. Higher powers contribute
a vanishing fraction of the cumulative proper-power mass. -/
private theorem power_mass_limit : Tendsto (fun x : ℝ => powerMass x/Real.sqrt x) atTop (𝓝 1) := by
  have hs := _root_.RHTower.tendsto_psi_div_self.comp Real.tendsto_sqrt_atTop
  let C := 2*(Real.log 4+4)
  have he : Tendsto (fun x : ℝ => C*x^(-(1/6):ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).const_mul C
  have hu := hs.add he
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs hu
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have h := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi (zero_le_one.trans hx)
    rw [show x^(2:ℝ)⁻¹=Real.sqrt x by rw [Real.sqrt_eq_rpow,one_div]] at h
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
    linarith only [h,Chebyshev.psi_nonneg (x^(3:ℝ)⁻¹),Chebyshev.psi_nonneg (x^(7:ℝ)⁻¹)]
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx₀ := zero_lt_one.trans_le hx
    have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    rw [show x^(2:ℝ)⁻¹=Real.sqrt x by rw [Real.sqrt_eq_rpow,one_div]] at h
    have h₅ := Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (5:ℝ)⁻¹ ≤ (3:ℝ)⁻¹))
    have h₃ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx₀.le ((3:ℝ)⁻¹))
    have hs' : Real.sqrt x*x^(-(1/6):ℝ)=x^(3:ℝ)⁻¹ := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add hx₀]; norm_num
    change powerMass x/Real.sqrt x ≤ Chebyshev.psi (Real.sqrt x)/Real.sqrt x+C*x^(-(1/6):ℝ)
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hx₀),add_mul,div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx₀).ne']
    dsimp only [C,powerMass]
    linarith only [h,h₅,h₃,congrArg (fun y : ℝ => 2*(Real.log 4+4)*y) hs']

private theorem power_prefix (y : ℝ) : ∑ k ∈ Icc 0 ⌊y⌋₊, powerWeight k = powerMass y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,sum_filter]
  have hs : Icc 0 ⌊y⌋₊=insert 0 (Ioc 0 ⌊y⌋₊) := by
    ext k; simp only [mem_Icc,mem_insert,mem_Ioc]; omega
  rw [hs,Finset.sum_insert (by simp)]
  simp only [powerWeight,Nat.not_prime_zero,if_false,vonMangoldt_apply_zero,zero_add]
  exact sum_congr rfl fun k _ => by by_cases h : k.Prime <;> simp [h]

private theorem scaled_power_mass {v : ℝ} (hv : 0 < v) :
    Tendsto (fun X : ℝ => powerMass (X*v)/Real.sqrt X) atTop (𝓝 (Real.sqrt v)) := by
  have h := (power_mass_limit.comp (tendsto_id.atTop_mul_const hv)).mul_const (Real.sqrt v)
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  change powerMass (X*v)/Real.sqrt (X*v)*Real.sqrt v=_
  rw [Real.sqrt_mul hX.le]
  field_simp [(Real.sqrt_pos.mpr hX).ne',(Real.sqrt_pos.mpr hv).ne']

/-- Abel summation of the proper-power rows on a fixed interval of
relative degrees. The limiting cumulative mass at relative degree v is √v. -/
private theorem moving_power_sum {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {W : ℝ → ℝ}
    (hd : ∀ v : ℝ, 0 < v → DifferentiableAt ℝ W v)
    (hc : ContinuousOn (deriv W) (Set.Ioi 0)) :
    Tendsto (fun X : ℝ => (∑ k ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, W (k/X)*powerWeight k)/Real.sqrt X) atTop
      (𝓝 (W b*Real.sqrt b-W a*Real.sqrt a-∫ v in Set.Ioc a b, deriv W v*Real.sqrt v)) := by
  let μ := volume.restrict (Set.Ioc a b)
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hab' : Set.Icc a b ⊆ Set.Ioi 0 := fun _ hv => ha.trans_le hv.1
  have hm (X : ℝ) : AEStronglyMeasurable (fun v : ℝ => deriv W v*(powerMass (X*v)/Real.sqrt X)) μ := by
    exact (((hc.mono (Set.Ioc_subset_Icc_self.trans hab')).aestronglyMeasurable measurableSet_Ioc).mul
      (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).comp
        (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable)
  have hi : Integrable (fun v : ℝ => |deriv W v|*(|D|*Real.sqrt b)) μ :=
    (((hc.mono hab').abs.mul continuousOn_const).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ᵐ v : ℝ ∂μ, ‖deriv W v*(powerMass (X*v)/Real.sqrt X)‖ ≤
      |deriv W v|*(|D|*Real.sqrt b) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with v hv
    have hv₀ := ha.trans hv.1
    have hm₀ : 0 ≤ powerMass (X*v) := sub_nonneg.mpr (Chebyshev.theta_le_psi _)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hm₀ (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hX)).mpr
    calc powerMass (X*v) ≤ |D|*Real.sqrt (X*v) := (hD _).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
      _ ≤ (|D|*Real.sqrt b)*Real.sqrt X := by
        rw [Real.sqrt_mul hX.le,mul_assoc, mul_comm (Real.sqrt b)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv.2) (Real.sqrt_nonneg X)) (abs_nonneg D)
  have hlim : Tendsto (fun X : ℝ => ∫ v, deriv W v*(powerMass (X*v)/Real.sqrt X) ∂μ)
      atTop (𝓝 (∫ v, deriv W v*Real.sqrt v ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hm) hbound hi (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with v hv
      exact (scaled_power_mass (ha.trans hv.1)).const_mul _)
  have H := (((scaled_power_mass (ha.trans_le hab)).const_mul (W b)).sub
    ((scaled_power_mass ha).const_mul (W a))).sub hlim
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  let f := fun t : ℝ => W (t/X)
  have hpos {t : ℝ} (ht : t ∈ Set.Icc (a*X) (b*X)) : 0 < t/X := div_pos ((mul_pos ha hX).trans_le ht.1) hX
  have hder {t : ℝ} (ht : t ∈ Set.Icc (a*X) (b*X)) : HasDerivAt f (deriv W (t/X)/X) t := by
    simpa only [f,Function.comp_def,id_eq,one_div,div_eq_mul_inv,one_mul] using
      (hd _ (hpos ht)).hasDerivAt.comp t ((hasDerivAt_id t).div_const X)
  have hcont : ContinuousOn (fun t : ℝ => deriv W (t/X)/X) (Set.Icc (a*X) (b*X)) :=
    (hc.comp (continuous_id.div_const X).continuousOn (fun _ ht => hpos ht)).div_const _
  have hAbel := sum_mul_eq_sub_sub_integral_mul powerWeight (mul_nonneg ha.le hX.le)
    (mul_le_mul_of_nonneg_right hab hX.le) (fun t ht => (hder ht).differentiableAt)
    ((hcont.congr (fun _ ht => (hder ht).deriv)).integrableOn_Icc)
  simp_rw [power_prefix] at hAbel
  have hscale : (∫ t in Set.Ioc (a*X) (b*X), deriv f t*powerMass t) =
      ∫ v in Set.Ioc a b, deriv W v*powerMass (X*v) := by
    rw [← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_right hab hX.le),← intervalIntegral.integral_of_le hab]
    calc
      _ = ∫ t in (a*X)..(b*X), X⁻¹*((fun v => deriv W v*powerMass (X*v)) (t/X)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (mul_le_mul_of_nonneg_right hab hX.le)] at ht
        rw [(hder ht).deriv,show X*(t/X)=t by field_simp]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div _ hX.ne',
          mul_div_cancel_right₀ _ hX.ne',mul_div_cancel_right₀ _ hX.ne',smul_eq_mul,
          ← mul_assoc,inv_mul_cancel₀ hX.ne',one_mul]
  change W b*(powerMass (X*b)/Real.sqrt X)-W a*(powerMass (X*a)/Real.sqrt X)-
    (∫ v in Set.Ioc a b, deriv W v*(powerMass (X*v)/Real.sqrt X)) = _
  rw [hscale] at hAbel
  dsimp only [f] at hAbel
  rw [mul_div_cancel_right₀ _ hX.ne',mul_div_cancel_right₀ _ hX.ne'] at hAbel
  have hi' : (∫ v in Set.Ioc a b, deriv W v*(powerMass (X*v)/Real.sqrt X)) =
      (∫ v in Set.Ioc a b, deriv W v*powerMass (X*v))/Real.sqrt X := by
    simp only [div_eq_mul_inv,← mul_assoc,integral_mul_const]
  rw [hAbel,hi',mul_comm X b,mul_comm X a]
  ring

private abbrev low := Real.exp (-9)
private abbrev high := Real.exp 8
private def rootProfile (v : ℝ) := (2/Real.sqrt v)*splineAutoCorr (-Real.log v)

/-- The integrated contribution of all proper powers to one moving long lag. -/
def longProperPowerContact (X : ℝ) : ℝ :=
  ∑ k ∈ Ioc ⌊Real.exp (-9)*X⌋₊ ⌊Real.exp 8*X⌋₊,
    (2/Real.sqrt k)*splineAutoCorr (Real.log X-Real.log k)*powerWeight k

/-- Both long lags see the same proper-power limit, independently of
their centers. Its relative-degree profile has the square-root density. -/
theorem longProperPowerContact_limit : ∃ c : ℝ, Tendsto longProperPowerContact atTop (𝓝 c) := by
  have hH : ContDiff ℝ 1 splineAutoCorr := by
    rw [show splineAutoCorr = upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact (contDiff_upow one_pos 6).of_le (by norm_num)
  have hc : ContDiffOn ℝ 1 rootProfile (Set.Ioi 0) := by
    intro v hv
    have hv' : 0 < v := hv
    apply ContDiffAt.contDiffWithinAt
    unfold rootProfile
    exact ((contDiffAt_const.div (Real.contDiffAt_sqrt hv'.ne') (Real.sqrt_pos.mpr hv').ne').mul
      (hH.contDiffAt.comp v (Real.contDiffAt_log hv'.ne').neg))
  obtain h := moving_power_sum (Real.exp_pos (-9)) (Real.exp_le_exp.mpr (by norm_num : (-9:ℝ) ≤ 8))
    (fun v hv => ((hc.contDiffAt (Ioi_mem_nhds hv)).differentiableAt (by norm_num)))
    (hc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl)
  refine ⟨_,h.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [longProperPowerContact,Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hlow : low*X < (k:ℝ) := (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast (mem_Ioc.mp hk).1)
  have hk₀ := (mul_pos (Real.exp_pos _) hX).trans hlow
  unfold rootProfile
  rw [Real.log_div hk₀.ne' hX.ne',Real.sqrt_div hk₀.le,neg_sub]
  field_simp [(Real.sqrt_pos.mpr hk₀).ne',(Real.sqrt_pos.mpr hX).ne']

#print axioms longProperPowerContact_limit

end GaloisForLFunctions.CountingHolography.Sections
