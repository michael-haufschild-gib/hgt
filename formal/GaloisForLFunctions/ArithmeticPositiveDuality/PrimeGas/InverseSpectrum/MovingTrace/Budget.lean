import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.HeightIndex
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.ClockMasks
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Sufficient clock-dependent trace budgets in the summable and matched regimes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open scoped NNReal

/-- Uniform disappearance of the relative partition inside one prescribed nonnegative trace budget. -/
def clockBudgetStable (σ : ℝ) (B : ℝ → ℝ≥0) : Prop :=
  0 < σ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
    ∀ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      traceLoss (projected P) ≤ (B t:ℝ) → ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ < ε

/-- The budget scale jumps at the abscissa of absolute summability. -/
def clockBudgetExponent (σ : ℝ) : ℝ := if σ ≤ 1 then 2/σ else 1

theorem matched_budget_stable {σ : ℝ} (hs : 0 < σ) (h₁ : σ ≤ 1) (B : ℝ → ℝ≥0)
    (hB : Tendsto (fun t : ℝ => t^(2/σ)*(B t:ℝ)) atTop (𝓝 0)) : clockBudgetStable σ B := by
  let p := 2/σ
  have hp : 0 < p := div_pos (by norm_num) hs
  have hq : max 1 (2/σ) = p := max_eq_right ((one_le_div hs).mpr (h₁.trans (by norm_num)))
  obtain ⟨_,_,C,hC,hbound⟩ := clock_coefficient_power_bounds hs
  simp only [hq] at hbound
  refine ⟨hs,?_⟩
  intro ε hε
  have he := hB.const_mul C
  rw [mul_zero] at he
  filter_upwards [eventually_ge_atTop (1:ℝ),he.eventually_lt_const (Real.rpow_pos_of_pos hε p)] with t ht hsmall
  intro P dim hc hd
  let z : ℂ := ⟨σ,t⟩
  have h := (optimalTraceCoefficient_isLeast 0 (z := z) hs).1 P dim hc
  change ‖relativePartition (physicalSpectrum P dim hc) z‖^(max 1 (2/σ)) ≤ _ at h
  rw [hq] at h
  have hb := mul_le_mul (hbound t ht).2 hd (traceLoss_nonneg P dim hc)
    (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans ht) p))
  have hstrict := ((h.trans hb).trans_eq (mul_assoc _ _ _)).trans_lt hsmall
  exact lt_of_not_ge (fun hn => hstrict.not_ge (Real.rpow_le_rpow hε.le hn hp.le))

private theorem individual_chord {σ t : ℝ} (hs : 1 < σ) (ht : 1 ≤ t) (P : Projection)
    (dim : MissingDimension P 1) (hc : Conserving (projected P)) (k : ℕ) {E : ℝ} (hd : traceLoss (projected P) ≤ E) :
    ‖complexDrop (physicalSpectrum P dim hc) k (⟨σ,t⟩:ℂ)‖ ≤ ((σ+1)/occupationWeight k)*(t*E) := by
  let b := physicalSpectrum P dim hc
  let a := occupationWeight k
  let x := (b k).val
  have ha : 0 < a := occupationWeight_pos _
  have hx : 0 ≤ x := (band_pos b k).le
  have hdiff : 0 ≤ a-x := sub_nonneg.mpr (b k).property.2
  have hi := (summable_spectralDrop quadraticResponse b).le_tsum k (fun j _ => drop_nonneg quadraticResponse b j)
  change a^2-x^2 ≤ relativeReading quadraticResponse b at hi
  rw [quadratic_physicalReading P dim hc] at hi
  have hcost : (a-x)*a ≤ E := (show (a-x)*a ≤ a^2-x^2 by nlinarith only [mul_nonneg hdiff hx]).trans (hi.trans hd)

  have he := complexDrop_bound b k unitExponent (z := ⟨σ,t⟩) hs.le
  change _ ≤ (‖(⟨σ,t⟩:ℂ)‖/1)*(a^(1:ℝ)-x^(1:ℝ)) at he
  rw [div_one,Real.rpow_one,Real.rpow_one] at he
  have hu := mul_le_mul (clock_height_norm_bounds (zero_lt_one.trans hs) ht).2 ((le_div_iff₀ ha).mpr hcost)
    hdiff (mul_nonneg (add_pos (zero_lt_one.trans hs) zero_lt_one).le (zero_le_one.trans ht))
  exact (he.trans hu).trans_eq (by dsimp only [a]; ring)

/-- Absolute summability suppresses all high levels independently of the clock. The finite levels vanish as soon as tB tends to zero. -/
theorem summable_budget_stable {σ : ℝ} (hs : 1 < σ) (B : ℝ → ℝ≥0)
    (hB : Tendsto (fun t : ℝ => t*(B t:ℝ)) atTop (𝓝 0)) : clockBudgetStable σ B := by
  let cap (k : ℕ) := 2*occupationWeight k^σ
  let f (t : ℝ) (k : ℕ) := min (cap k) (((σ+1)/occupationWeight k)*(t*(B t:ℝ)))
  have hσ := zero_lt_one.trans hs
  have hcap (k : ℕ) : 0 ≤ cap k := mul_nonneg (by norm_num) (Real.rpow_nonneg (occupationWeight_pos k).le _)
  have hsum : Summable cap := ((summable_band_rpow_iff (hotEdge 0) σ).mpr hs).mul_left 2
  have hn (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : 0 ≤ f t k := le_min (hcap k) (mul_nonneg
    (div_nonneg (add_pos hσ zero_lt_one).le (occupationWeight_pos k).le) (mul_nonneg ht (B t).coe_nonneg))
  have hlim (k : ℕ) : Tendsto (fun t => f t k) atTop (𝓝 0) := by
    have he := (tendsto_const_nhds (x := cap k)).min (hB.const_mul ((σ+1)/occupationWeight k))
    simpa only [mul_zero,min_eq_right (hcap k)] using he
  have htotal : Tendsto (fun t => ∑' k, f t k) atTop (𝓝 0) := by
    have he := tendsto_tsum_of_dominated_convergence hsum hlim (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      intro k
      rw [Real.norm_of_nonneg (hn t ht k)]
      exact min_le_left _ _)
    simpa only [tsum_zero] using he
  refine ⟨hσ,?_⟩
  intro ε hε
  filter_upwards [eventually_ge_atTop (1:ℝ),htotal.eventually_lt_const hε] with t ht hsmall
  intro P dim hc hd
  let b := physicalSpectrum P dim hc
  let z : ℂ := ⟨σ,t⟩
  have hz : 0 < z.re := hσ
  have hnorm := (summable_complexDrop b hz).norm
  have hf := Summable.of_nonneg_of_le (hn t (zero_le_one.trans ht)) (fun k => min_le_left (cap k) _) hsum
  refine ((norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum (fun k => le_min ?_ (individual_chord hs ht P dim hc k hd)) hf)).trans_lt hsmall
  rw [clockMask_represents]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.rpow_nonneg (occupationWeight_pos _).le _) (clockMask_mem b hz.le k).2) (by norm_num)

#print axioms matched_budget_stable
#print axioms summable_budget_stable

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
