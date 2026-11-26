import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowLogPowerSchedule

/-! # Prime counts in translated packets of relative width a/t -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Filter Topology Real _root_.RHTower.Sieve

/-- Primes between exp(t+v) and exp(t+v)(1+a/t). -/
def packet (t v a : ℝ) := primesIn (exp (t+v)) (exp (t+v)*(1+a/t))

/-- Multiplying counts by this common factor leaves a finite, nonzero packet density. -/
def scale (t : ℝ) := t^2/exp t

theorem scale_nonneg (t : ℝ) : 0 ≤ scale t := div_nonneg (sq_nonneg _) (exp_pos _).le

theorem small_width (a : ℝ) : Tendsto (fun t : ℝ => a/t) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul a

theorem logWidth_limit (a : ℝ) : Tendsto (fun t : ℝ => log (1+a/t)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add (small_width a)
  rw [add_zero] at h
  simpa only [log_one,Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp h

private def expectedCount (t v a : ℝ) := a/t*exp (t+v)/(t+v)

private theorem center_ratio {v : ℝ → ℝ} {V : ℝ} (hv : Tendsto v atTop (𝓝 V)) :
    Tendsto (fun t => t/(t+v t)) atTop (𝓝 1) := by
  have hz := hv.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  rw [mul_zero] at hz
  have h := (tendsto_const_nhds (x := (1:ℝ))).add hz
  rw [add_zero] at h
  have hi := h.inv₀ one_ne_zero
  rw [inv_one] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  change (1+v t*t⁻¹)⁻¹ = t/(t+v t)
  have he : 1+v t*t⁻¹ = (t+v t)/t := by rw [add_div,div_self ht.ne',div_eq_mul_inv]
  rw [he,inv_div]

private theorem relative_count {v : ℝ → ℝ} {V a : ℝ} (hv : Tendsto v atTop (𝓝 V)) (ha : 0 < a) :
    Tendsto (fun t => ((packet t (v t) a).card : ℝ)/expectedCount t (v t) a) atTop (𝓝 1) := by
  have hg : Tendsto (fun t => t+v t) atTop atTop := tendsto_id.atTop_add hv
  have hZ := tendsto_exp_atTop.comp hg
  obtain ⟨C,hC,hcount⟩ := exists_card_primesIn_window
  have hdecay := hZ.eventually (eventually_two_mul_exp_neg_sqrt_log_le_log_rpow_neg
    (B := 1/a) (K := 1) (by positivity) hC)
  have eligible : ∀ᶠ t : ℝ in atTop, exp (-C*sqrt (t+v t)) ≤ a/t := by
    filter_upwards [hdecay,eventually_gt_atTop (0:ℝ),hg.eventually_gt_atTop 0,
      (center_ratio hv).eventually_lt_const (one_lt_two : (1:ℝ)<2)] with t he ht hc hr
    simp only [Function.comp_apply,log_exp,Real.rpow_neg_one] at he
    have hlarge := (div_lt_iff₀ hc).mp hr
    have hs : 2*(1/a)*exp (-C*sqrt (t+v t))*(t+v t) ≤ 1 :=
      (le_div_iff₀ hc).mp (by simpa only [one_div] using he)
    have hh := mul_le_mul_of_nonneg_right hs ha.le
    have heq : 2*(1/a)*exp (-C*sqrt (t+v t))*(t+v t)*a = exp (-C*sqrt (t+v t))*(2*(t+v t)) := by
      field_simp
    rw [heq,one_mul] at hh
    exact (le_div_iff₀ ht).mpr ((mul_le_mul_of_nonneg_left hlarge.le (exp_pos _).le).trans hh)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hZ.eventually (hcount (ε/2) (half_pos hε)),eligible,
    (small_width a).eventually_lt_const zero_lt_one,eventually_gt_atTop (0:ℝ),hg.eventually_gt_atTop 0]
    with t h he h1 ht hc
  obtain ⟨lo,hi⟩ := h (a/t) (by simpa only [Function.comp_apply,log_exp] using he) h1.le
  simp only [Function.comp_apply,log_exp] at lo hi
  have hm : 0 < expectedCount t (v t) a := div_pos (mul_pos (div_pos ha ht) (exp_pos _)) hc
  have l := (le_div_iff₀ hm).mpr lo
  have u := (div_le_iff₀ hm).mpr hi
  rw [Real.dist_eq,abs_lt]
  change 1-ε/2 ≤ ((packet t (v t) a).card : ℝ)/expectedCount t (v t) a at l
  change ((packet t (v t) a).card : ℝ)/expectedCount t (v t) a ≤ 1+ε/2 at u
  constructor <;> linarith only [l,u,hε]

/-- On the common scale exp(t)/t² the count tends to a exp(V), including moving centers v(t) → V. -/
theorem count_limit {v : ℝ → ℝ} {V a : ℝ} (hv : Tendsto v atTop (𝓝 V)) (ha : 0 < a) :
    Tendsto (fun t => scale t*((packet t (v t) a).card : ℝ)) atTop (𝓝 (a*exp V)) := by
  have r := (center_ratio hv).mul ((Real.continuous_exp.tendsto V).comp hv)
  have m := r.const_mul a
  rw [one_mul] at m
  have z := (relative_count hv ha).mul m
  rw [one_mul] at z
  apply z.congr'
  have hg : Tendsto (fun t => t+v t) atTop atTop := tendsto_id.atTop_add hv
  filter_upwards [eventually_gt_atTop (0:ℝ),hg.eventually_gt_atTop 0] with t ht hc
  dsimp only [scale,expectedCount,Function.comp_apply]
  rw [exp_add]
  field_simp [ht.ne',hc.ne',ha.ne',(exp_pos _).ne']

#print axioms count_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
