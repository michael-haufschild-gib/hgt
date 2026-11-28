import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Quadrature
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Entropy asymptotics at the critical elementary mass scale -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Filter Real
open scoped Topology

def scale (N : ℕ) := log (log N)

theorem scale_growth : Tendsto scale atTop atTop := Crossover.logEnergy_growth

private theorem small_of_scaled {p : ℕ → ℝ} {v : ℝ}
    (h : Tendsto (fun N => scale N*p N) atTop (𝓝 v)) : Tendsto p atTop (𝓝 0) := by
  apply (h.div_atTop scale_growth).congr'
  filter_upwards [scale_growth.eventually_gt_atTop 0] with N hp
  exact mul_div_cancel_left₀ (p N) hp.ne'

theorem linear_scale {p : ℕ → ℝ} {v : ℝ} (h : Tendsto (fun N => scale N*p N) atTop (𝓝 v)) :
    Tendsto (fun N => scale N*(2*p N*(1-p N))) atTop (𝓝 (2*v)) := by
  have lim := (h.const_mul 2).mul ((small_of_scaled h).const_sub 1)
  rw [sub_zero,mul_one] at lim
  exact lim.congr fun _ => by ring

/-- For a small branch of weight p, the logarithmic singularity contributes
exactly the limit of Lp, including when that limit is zero. -/
theorem entropy_scale {p : ℕ → ℝ} {v : ℝ} (box : ∀ N, 0≤p N ∧ p N≤1)
    (h : Tendsto (fun N => scale N*p N) atTop (𝓝 v)) :
    Tendsto (fun N => scale N*binEntropy (p N)/log (scale N)) atTop (𝓝 v) := by
  let R (N : ℕ) := scale N*negMulLog (1-p N)/log (scale N)
  have ht := tendsto_log_atTop.comp scale_growth
  have remn : Tendsto R atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h.div_atTop ht)
    · filter_upwards [scale_growth.eventually_gt_atTop 1] with N hL
      exact div_nonneg (mul_nonneg (one_pos.trans hL).le (negMulLog_nonneg (sub_nonneg.mpr (box N).2)
        (sub_le_self _ (box N).1))) (log_pos hL).le
    · filter_upwards [scale_growth.eventually_gt_atTop 1] with N hL
      apply div_le_div_of_nonneg_right _ (log_pos hL).le
      apply mul_le_mul_of_nonneg_left _ (one_pos.trans hL).le
      simpa only [sub_sub_cancel] using negMulLog_le_one_sub_self (sub_nonneg.mpr (box N).2)
  have tiny := ((continuous_negMulLog.tendsto v).comp h).div_atTop ht
  have lim := (h.add tiny).add remn
  rw [add_zero,add_zero] at lim
  apply lim.congr'
  filter_upwards [scale_growth.eventually_gt_atTop 1] with N hL
  change scale N*p N+negMulLog (scale N*p N)/log (scale N)+R N=_
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub,negMulLog_mul]
  unfold R
  change scale N*p N+(p N*(-(scale N)*log (scale N))+scale N*negMulLog (p N))/log (scale N)+_=_
  field_simp [(log_pos hL).ne']
  ring

theorem positive_entropy_growth {p : ℕ → ℝ} {v : ℝ} (hv : 0<v) (hv' : v<1) (h : Tendsto p atTop (𝓝 v)) :
    Tendsto (fun N => scale N*(2*p N*(1-p N))) atTop atTop ∧
    Tendsto (fun N => scale N*binEntropy (p N)/log (scale N)) atTop atTop := by
  have left := (h.const_mul 2).mul (h.const_sub 1)
  have right : Tendsto (fun N => binEntropy (p N)) atTop (𝓝 (binEntropy v)) := by
    simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact ((continuous_negMulLog.tendsto v).comp h).add
      ((continuous_negMulLog.tendsto (1-v)).comp (h.const_sub 1))
  refine ⟨Tendsto.atTop_mul_pos (mul_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hv')) scale_growth left,?_⟩
  have lim := Tendsto.atTop_mul_pos (binEntropy_pos hv hv') (x_log_x_atTop.comp scale_growth) right
  exact lim.congr fun N => div_mul_eq_mul_div _ _ _

#print axioms linear_scale
#print axioms entropy_scale
#print axioms positive_entropy_growth

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
