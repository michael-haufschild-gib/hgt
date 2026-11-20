import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ExponentialTypeOfCascadedTimeWindows
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.AZeroSetForTheDyadicSincPulse
import GaloisForLFunctions.RHTower.XiGaussianHeatPoleHyperplaneCriterion
import GaloisForLFunctions.RHTower.Sieve.LogLogSmall

/-!
# The sum of window widths is the exact exponential type

On the imaginary axis every rectangular-window factor has modulus at
least one. A finite prefix gives a lower exponential rate equal to its
sum of widths. Taking all prefixes attains the upper rate of the entire
product. In particular the unweighted dyadic cascade has type two.
-/

noncomputable section
open Complex Filter Topology
open RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

private def axisFactor (r y : ℝ) := ‖rectangularWindow r ((y:ℂ)*I)‖

private theorem axis_factor_eq {r y : ℝ} (hr : 0 < r) (hy : 0 < y) :
    axisFactor r y=Real.sinh (r*y)/(r*y) := by
  have hp : 0 < 2*(r*y) := by positivity
  have he : (r:ℂ)*((y:ℂ)*I)=((2*(r*y):ℝ):ℂ)*(I/2) := by push_cast; ring
  rw [axisFactor,rectangularWindow,he,norm_sinc_I_half hp,show 2*(r*y)/2=r*y by ring]

private theorem axis_one {r y : ℝ} (hr : 0 < r) (hy : 0 < y) : 1 ≤ axisFactor r y := by
  rw [axis_factor_eq hr hy,le_div_iff₀ (mul_pos hr hy),one_mul]
  exact Real.self_le_sinh_iff.mpr (mul_pos hr hy).le

private theorem axis_upper {r y : ℝ} (hr : 0 < r) (hy : 0 < y) :
    axisFactor r y ≤ Real.exp (r*y) := by
  have h := norm_entireSinc_le_exp_abs_im ((r:ℂ)*((y:ℂ)*I))
  simpa [axisFactor,rectangularWindow,Complex.mul_im,abs_of_pos (mul_pos hr hy)] using h

private theorem single_axis_rate {r : ℝ} (hr : 0 < r) :
    Tendsto (fun y : ℝ => Real.log (axisFactor r y)/y) atTop (𝓝 r) := by
  have ht : Tendsto (fun y : ℝ => Real.log y/y) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using RHTower.Sieve.tendsto_log_div_rpow (δ:=1) one_pos
  have hc := (tendsto_const_nhds (x:=Real.log (4*r))).div_atTop (tendsto_id (α:=ℝ))
  have hlow := (tendsto_const_nhds (x:=r)).sub (hc.add ht)
  simp only [add_zero,sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (tendsto_const_nhds (x:=r))
  · filter_upwards [eventually_gt_atTop (1/r),eventually_gt_atTop (0:ℝ)] with y hry hy
    have h₁ : 1 ≤ r*y := by
      have h := (div_lt_iff₀ hr).mp hry
      linarith only [h]
    have hq := div_le_div_of_nonneg_right (quarter_exp_le_sinh h₁) (mul_pos hr hy).le
    have hbd : Real.exp (r*y)/(4*r*y) ≤ axisFactor r y := by
      rw [axis_factor_eq hr hy]
      calc Real.exp (r*y)/(4*r*y) = (Real.exp (r*y)/4)/(r*y) := by
             field_simp [hr.ne',hy.ne'] <;> ring
           _ ≤ _ := hq
    have hlog := Real.log_le_log (by positivity) hbd
    rw [Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
      Real.log_mul (by positivity : 4*r≠0) hy.ne'] at hlog
    change r-(Real.log (4*r)/y+Real.log y/y) ≤ _
    apply (le_div_iff₀ hy).mpr
    calc _ = r*y-(Real.log (4*r)+Real.log y) := by field_simp [hy.ne'] <;> ring
         _ ≤ _ := hlog
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    apply (div_le_iff₀ hy).mpr
    simpa only [Real.log_exp] using
      Real.log_le_log (one_pos.trans_le (axis_one hr hy)) (axis_upper hr hy)

private theorem prefix_le_axis {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n≤1)
    (hs : Summable r) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    ∏ j ∈ Finset.range N, axisFactor (r j) y ≤ ‖windowSpectrum r ((y:ℂ)*I)‖ := by
  let P (k : ℕ) := ∏ j ∈ Finset.range k, axisFactor (r j) y
  have hm : Monotone P := monotone_nat_of_le_succ fun n => by
    change P n ≤ ∏ j ∈ Finset.range (n+1), axisFactor (r j) y
    rw [Finset.prod_range_succ]
    exact le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (axis_one (hr n).1 hy)
  have h := (windowSpectrum_hasProd (fun n => ⟨(hr n).1.le,(hr n).2⟩) hs ((y:ℂ)*I)).tendsto_prod_nat.norm
  apply ge_of_tendsto h
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [norm_prod]
  exact hm hn

/-- The logarithmic growth rate on the positive imaginary axis attains
the total half-width of the boxes. -/
theorem windowSpectrum_exact_type {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n≤1)
    (hs : Summable r) :
    Tendsto (fun y : ℝ => Real.log ‖windowSpectrum r ((y:ℂ)*I)‖/y) atTop
      (𝓝 (∑' j, r j)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨N,hN⟩ := (hs.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds hb)).exists
    have hlim : Tendsto (fun y : ℝ => ∑ j ∈ Finset.range N, Real.log (axisFactor (r j) y)/y)
        atTop (𝓝 (∑ j ∈ Finset.range N, r j)) :=
      tendsto_finsetSum _ fun j _ => single_axis_rate (hr j).1
    filter_upwards [hlim.eventually (lt_mem_nhds hN),eventually_gt_atTop (0:ℝ)] with y hy hypos
    apply hy.trans_le
    rw [←Finset.sum_div,←Real.log_prod (fun j _ => (one_pos.trans_le (axis_one (hr j).1 hypos)).ne')]
    exact div_le_div_of_nonneg_right (Real.log_le_log (Finset.prod_pos fun j _ =>
      one_pos.trans_le (axis_one (hr j).1 hypos)) (prefix_le_axis hr hs N hypos)) hypos.le
  · intro b hb
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hp := prefix_le_axis hr hs 0 hy
    simp only [Finset.range_zero,Finset.prod_empty] at hp
    have h := windowSpectrum_strip_bound hr hs 0 ((y:ℂ)*I)
    simp only [pow_zero,mul_one,Finset.range_zero,Finset.prod_empty,one_mul,
      Complex.mul_I_im,Complex.ofReal_re,abs_of_pos hy] at h
    have hlog := Real.log_le_log (one_pos.trans_le hp) h
    rw [Real.log_exp] at hlog
    exact ((div_le_iff₀ hy).mpr hlog).trans_lt hb

/-- The sharp rate is two for one window of width 2⁻ʲ at every scale j. -/
theorem dyadicPulseSpectrum_exact_type :
    Tendsto (fun y : ℝ => Real.log ‖dyadicPulseSpectrum ((y:ℂ)*I)‖/y) atTop (𝓝 2) := by
  simpa only [pulseWindowWidth,tsum_geometric_two] using
    windowSpectrum_exact_type (r:=pulseWindowWidth)
      (fun j => ⟨pulseWindowWidth_pos j,pulseWindowWidth_le_one j⟩) summable_geometric_two

#print axioms windowSpectrum_exact_type
#print axioms dyadicPulseSpectrum_exact_type
end GaloisForLFunctions.BlackHoleRingdown
