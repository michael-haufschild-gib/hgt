import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.PNat.Basic

/-!+# First moments of finite short Fourier sums

Each supported integer contributes on an interval of length `d h` in the
starting point. Integrating this support bound also pays the small-window
part of a partial-summation integral, with no cancellation assumption.
-/

noncomputable section

namespace TwinPrime.ShortFourier

open MeasureTheory
open scoped NNReal

/-- Each integer is carried by the interval `[d(n-h),dn]` of starting points. -/
def window (c : ℕ → ℂ) (s : Finset ℕ) (d h x : ℝ) : ℂ :=
  ∑ n ∈ s, (Set.Icc (d * ((n : ℝ) - h)) (d * n)).indicator (fun _ => c n) x

/-- The first moment over all starting points. -/
def firstMoment (c : ℕ → ℂ) (s : Finset ℕ) (d h : ℝ) : ℝ :=
  ∫ x : ℝ, ‖window c s d h x‖

private theorem integrable_term (c : ℕ → ℂ) (d h : ℝ) (n : ℕ) :
    Integrable ((Set.Icc (d * ((n : ℝ) - h)) (d * n)).indicator (fun _ => c n)) := by
  exact (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (by finiteness)).integrable_indicator measurableSet_Icc

/-- Every finite moving-window sum is integrable in its starting point. -/
theorem integrable_window (c : ℕ → ℂ) (s : Finset ℕ) (d h : ℝ) :
    Integrable (window c s d h) :=
  integrable_finsetSum s fun n _ => integrable_term c d h n

private theorem integral_norm_term (c : ℕ → ℂ) (d h : ℝ) (n : ℕ) :
    (∫ x : ℝ, ‖(Set.Icc (d * ((n : ℝ) - h)) (d * n)).indicator
      (fun _ => c n) x‖) = max (d * h) 0 * ‖c n‖ := by
  simp_rw [norm_indicator_eq_indicator_norm]
  rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc]
  rw [show d * (n : ℝ) - d * ((n : ℝ) - h) = d * h by ring]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

/-- Support length controls the first moment for arbitrary coefficients. -/
theorem firstMoment_le (c : ℕ → ℂ) (s : Finset ℕ) (d h : ℝ) :
    firstMoment c s d h ≤ max (d * h) 0 * ∑ n ∈ s, ‖c n‖ := by
  have hi := (integrable_window c s d h).norm
  have hj := integrable_finsetSum s fun n _ => (integrable_term c d h n).norm
  calc firstMoment c s d h
      ≤ ∫ x : ℝ, ∑ n ∈ s, ‖(Set.Icc (d * ((n : ℝ) - h)) (d * n)).indicator
          (fun _ => c n) x‖ :=
        integral_mono hi hj fun x => norm_sum_le _ _
    _ = ∑ n ∈ s, max (d * h) 0 * ‖c n‖ := by
        rw [integral_finsetSum s fun n _ => (integrable_term c d h n).norm]
        exact Finset.sum_congr rfl fun n _ => integral_norm_term c d h n
    _ = max (d * h) 0 * ∑ n ∈ s, ‖c n‖ := (Finset.mul_sum _ _ _).symm

theorem firstMoment_nonneg (c : ℕ → ℂ) (s : Finset ℕ) (d h : ℝ) :
    0 ≤ firstMoment c s d h := integral_nonneg fun _ => norm_nonneg _


/-- The moving-window sum is jointly measurable in length and starting point. -/
theorem measurable_window (c : ℕ → ℂ) (s : Finset ℕ) (d : ℝ) :
    Measurable (Function.uncurry (window c s d)) := by
  classical
  apply Finset.measurable_sum
  intro n _
  have hm : MeasurableSet {p : ℝ × ℝ | d * ((n : ℝ) - p.1) ≤ p.2 ∧ p.2 ≤ d * n} :=
    (measurableSet_le (by fun_prop) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  change Measurable ({p : ℝ × ℝ | d * ((n : ℝ) - p.1) ≤ p.2 ∧ p.2 ≤ d * n}.indicator
    (fun _ => c n))
  exact measurable_const.indicator hm

/-- Integrating out the starting point preserves measurability. -/
theorem stronglyMeasurable_firstMoment (c : ℕ → ℂ) (s : Finset ℕ) (d : ℝ) :
    StronglyMeasurable (firstMoment c s d) :=
  (measurable_window c s d).stronglyMeasurable.norm.integral_prod_right

/-- The first moment is integrable over every bounded nonnegative range of lengths. -/
theorem integrableOn_firstMoment (c : ℕ → ℂ) (s : Finset ℕ) (d B : ℝ≥0) :
    IntegrableOn (firstMoment c s d) (Set.Icc 0 (B : ℝ)) := by
  have hg : IntegrableOn (fun h : ℝ => (d : ℝ) * h * ∑ n ∈ s, ‖c n‖)
      (Set.Icc 0 (B : ℝ)) := (by fun_prop : Continuous _).integrableOn_Icc
  refine hg.mono' (stronglyMeasurable_firstMoment c s d).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (firstMoment_nonneg c s d h)]
  simpa only [max_eq_left (mul_nonneg d.coe_nonneg hh.1)] using firstMoment_le c s d h

/-- Integrating the support-length bound gives the exact quadratic endpoint cost. -/
theorem integral_firstMoment_le (c : ℕ → ℂ) (s : Finset ℕ) (d B : ℝ≥0) :
    (∫ h in Set.Icc 0 (B : ℝ), firstMoment c s d h)
      ≤ (d : ℝ) * (B : ℝ) ^ 2 / 2 * ∑ n ∈ s, ‖c n‖ := by
  have hg : IntegrableOn (fun h : ℝ => (d : ℝ) * h * ∑ n ∈ s, ‖c n‖)
      (Set.Icc 0 (B : ℝ)) := (by fun_prop : Continuous _).integrableOn_Icc
  calc (∫ h in Set.Icc 0 (B : ℝ), firstMoment c s d h)
      ≤ ∫ h in Set.Icc 0 (B : ℝ), (d : ℝ) * h * ∑ n ∈ s, ‖c n‖ := by
        refine setIntegral_mono_on (integrableOn_firstMoment c s d B) hg
          measurableSet_Icc fun h hh => ?_
        simpa only [max_eq_left (mul_nonneg d.coe_nonneg hh.1)] using firstMoment_le c s d h
    _ = (d : ℝ) * (B : ℝ) ^ 2 / 2 * ∑ n ∈ s, ‖c n‖ := by
        rw [show (fun h : ℝ => (d : ℝ) * h * ∑ n ∈ s, ‖c n‖)
          = (fun h => ((d : ℝ) * ∑ n ∈ s, ‖c n‖) * h) by funext h; ring]
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le B.coe_nonneg, integral_id]
        ring

/-- The actual Liouville coefficient with an additive Fourier phase. -/
def liouvillePhase (α : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.liouville n : ℂ) *
    Complex.exp (((2 * Real.pi * α * n : ℝ) : ℂ) * Complex.I)

theorem norm_liouvillePhase_le_one (α : ℝ) (n : ℕ) : ‖liouvillePhase α n‖ ≤ 1 := by
  rw [liouvillePhase, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  by_cases hn : n = 0
  · simp [hn]
  · simp [ArithmeticFunction.liouville_apply hn]

private theorem sum_norm_liouvillePhase_le (s : Finset ℕ) (α : ℝ) :
    ∑ n ∈ s, ‖liouvillePhase α n‖ ≤ (s.card : ℝ) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    (Finset.sum_le_sum fun n (_ : n ∈ s) => norm_liouvillePhase_le_one α n)

/-- The actual Liouville first moment is bounded by length times support size. -/
theorem firstMoment_liouville_le (s : Finset ℕ) (α : ℝ) (d h : ℝ≥0) :
    firstMoment (liouvillePhase α) s d h ≤ (d : ℝ) * h * s.card := by
  have hb := firstMoment_le (liouvillePhase α) s d h
  rw [max_eq_left (mul_nonneg d.coe_nonneg h.coe_nonneg)] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (sum_norm_liouvillePhase_le s α) (by positivity))

/-- The quadratic endpoint bound for the actual Liouville row. -/
theorem integral_firstMoment_liouville_le (s : Finset ℕ) (α : ℝ) (d B : ℝ≥0) :
    (∫ h in Set.Icc 0 (B : ℝ), firstMoment (liouvillePhase α) s d h)
      ≤ (d : ℝ) * (B : ℝ) ^ 2 / 2 * s.card :=
  (integral_firstMoment_le (liouvillePhase α) s d B).trans
    (mul_le_mul_of_nonneg_left (sum_norm_liouvillePhase_le s α) (by positivity))

/-- The small-window contribution weighted by the partial-summation coefficient. -/
def endpointCost (s : Finset ℕ) (α : ℝ) (d W q : ℕ+) (H : ℝ≥0) : ℝ :=
  (W : ℝ) / ((H : ℝ) * q) *
    ∫ h in Set.Icc 0 ((H : ℝ) * q / (W : ℝ) ^ 3),
      firstMoment (liouvillePhase α) s d h

/-- Exact parameter dependence of the weighted small-window contribution. -/
theorem endpointCost_le (s : Finset ℕ) (α : ℝ) (d W q : ℕ+) (H : ℝ≥0) :
    endpointCost s α d W q H ≤ (d : ℝ) * s.card * H * q / (2 * (W : ℝ) ^ 5) := by
  by_cases hH : (H : ℝ) = 0
  · simp [endpointCost, hH]
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  have hW : (0 : ℝ) < W := by exact_mod_cast W.pos
  have hq : (0 : ℝ) < q := by exact_mod_cast q.pos
  have hi := integral_firstMoment_liouville_le s α ⟨d, hd.le⟩
    ⟨(H : ℝ) * q / (W : ℝ) ^ 3, by positivity⟩
  calc endpointCost s α d W q H
      ≤ (W : ℝ) / ((H : ℝ) * q) *
          ((d : ℝ) * ((H : ℝ) * q / (W : ℝ) ^ 3) ^ 2 / 2 * s.card) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (d : ℝ) * s.card * H * q / (2 * (W : ℝ) ^ 5) := by
        field_simp [hH, ne_of_gt hq, ne_of_gt hW]

/-- For `d,q ≤ W`, the partial-summation endpoint costs at most `|s| H/(2 W³)`. -/
theorem endpointCost_le_of_bounded_parameters (s : Finset ℕ) (α : ℝ) (H : ℝ≥0)
    (W : ℕ+) (d q : Fin (W : ℕ)) :
    endpointCost s α ⟨d.val + 1, Nat.succ_pos _⟩ W ⟨q.val + 1, Nat.succ_pos _⟩ H
      ≤ (s.card : ℝ) * H / (2 * (W : ℝ) ^ 3) := by
  have hW : (0 : ℝ) < W := by exact_mod_cast W.pos
  have hd : (d.val : ℝ) + 1 ≤ W := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  have hq : (q.val : ℝ) + 1 ≤ W := by exact_mod_cast Nat.succ_le_of_lt q.isLt
  have hdq : ((d.val : ℝ) + 1) * ((q.val : ℝ) + 1) ≤ (W : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hd hq (by positivity) hW.le
  have hi := endpointCost_le s α ⟨d.val + 1, Nat.succ_pos _⟩ W
    ⟨q.val + 1, Nat.succ_pos _⟩ H
  change _ ≤ ((d.val + 1 : ℕ) : ℝ) * (s.card : ℝ) * (H : ℝ) *
    ((q.val + 1 : ℕ) : ℝ) / (2 * (W : ℝ) ^ 5) at hi
  simp only [Nat.cast_add, Nat.cast_one] at hi
  calc endpointCost s α ⟨d.val + 1, Nat.succ_pos _⟩ W ⟨q.val + 1, Nat.succ_pos _⟩ H
      ≤ (((d.val : ℝ) + 1) * ((q.val : ℝ) + 1)) * ((s.card : ℝ) * H) /
          (2 * (W : ℝ) ^ 5) := by
        convert hi using 1
        ring
    _ ≤ (W : ℝ) ^ 2 * ((s.card : ℝ) * H) / (2 * (W : ℝ) ^ 5) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdq (by positivity)) (by positivity)
    _ = (s.card : ℝ) * H / (2 * (W : ℝ) ^ 3) := by
        field_simp [ne_of_gt hW]


/-- Above the split point, every divided window has the required minimum length. -/
theorem minimum_window_le (H u : ℝ≥0) (W q : ℕ+) (k : Fin (q : ℕ)) :
    (H : ℝ) / (W : ℝ) ^ 3
      ≤ ((H : ℝ) * q / (W : ℝ) ^ 3 + u) / ((k.val : ℝ) + 1) := by
  have hk : (k.val : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt k.isLt
  have hq := mul_le_mul_of_nonneg_left hk
    (show 0 ≤ (H : ℝ) / (W : ℝ) ^ 3 by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (k.val : ℝ) + 1)).2
  calc (H : ℝ) / (W : ℝ) ^ 3 * ((k.val : ℝ) + 1)
      ≤ (H : ℝ) / (W : ℝ) ^ 3 * q := hq
    _ ≤ (H : ℝ) * q / (W : ℝ) ^ 3 + u := by
        rw [div_mul_eq_mul_div]
        exact le_add_of_nonneg_right u.coe_nonneg

/-- The split point precedes the partial-summation endpoint when `d,q ≤ W`. -/
theorem split_le_endpoint (H : ℝ≥0) (W : ℕ+) (d q : Fin (W : ℕ)) :
    (H : ℝ) * ((q.val : ℝ) + 1) / (W : ℝ) ^ 3
      ≤ (H : ℝ) / ((d.val : ℝ) + 1) := by
  have hW : (1 : ℝ) ≤ W := by exact_mod_cast Nat.succ_le_of_lt W.pos
  have hd : (d.val : ℝ) + 1 ≤ W := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  have hq : (q.val : ℝ) + 1 ≤ W := by exact_mod_cast Nat.succ_le_of_lt q.isLt
  have hdq : ((q.val : ℝ) + 1) * ((d.val : ℝ) + 1) ≤ (W : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hq hd (by positivity) (by positivity)
  have hpow : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ 3 := by
    simpa only [mul_one, ← pow_succ] using mul_le_mul_of_nonneg_left hW (sq_nonneg (W : ℝ))
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (W : ℝ) ^ 3)
    (by positivity : (0 : ℝ) < (d.val : ℝ) + 1)).2
  calc (H : ℝ) * ((q.val : ℝ) + 1) * ((d.val : ℝ) + 1)
      = (H : ℝ) * (((q.val : ℝ) + 1) * ((d.val : ℝ) + 1)) := by ring
    _ ≤ (H : ℝ) * (W : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (hdq.trans hpow) H.coe_nonneg


/-- For positive dilation, the indicators select the usual short Fourier window. -/
theorem window_eq_short_sum (c : ℕ → ℂ) (s : Finset ℕ) (d : ℕ+) (h x : ℝ) :
    window c s d h x =
      ∑ n ∈ s.filter (fun n : ℕ => x / (d : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x / (d : ℝ) + h), c n := by
  classical
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  have heq (n : ℕ) : x ∈ Set.Icc ((d : ℝ) * ((n : ℝ) - h)) ((d : ℝ) * n) ↔
      x / (d : ℝ) ≤ n ∧ (n : ℝ) ≤ x / (d : ℝ) + h := by
    constructor
    · intro hn
      constructor
      · apply (div_le_iff₀ hd).2
        simpa only [mul_comm] using hn.2
      · have ht : (n : ℝ) - h ≤ x / (d : ℝ) := by
          apply (le_div_iff₀ hd).2
          simpa only [mul_comm] using hn.1
        linarith only [ht]
    · intro hn
      constructor
      · have ht : (n : ℝ) - h ≤ x / (d : ℝ) := by linarith only [hn.2]
        simpa only [mul_comm] using (le_div_iff₀ hd).1 ht
      · simpa only [mul_comm] using (div_le_iff₀ hd).1 hn.1
  rw [window, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => by simp only [Set.indicator_apply, heq n]

/-- Restricting to positive integers up to `N` replaces support size by `N`. -/
theorem endpointCost_on_initialSegment_le (s : Finset ℕ) (N : ℕ) (α : ℝ) (H : ℝ≥0)
    (W : ℕ+) (d q : Fin (W : ℕ)) :
    endpointCost (s ∩ Finset.Icc 1 N) α ⟨d.val + 1, Nat.succ_pos _⟩ W
      ⟨q.val + 1, Nat.succ_pos _⟩ H ≤ (N : ℝ) * H / (2 * (W : ℝ) ^ 3) := by
  have hc : (s ∩ Finset.Icc 1 N).card ≤ N := by
    simpa using Finset.card_le_card (Finset.inter_subset_right (s₂ := Finset.Icc 1 N) (s₁ := s))
  exact (endpointCost_le_of_bounded_parameters (s ∩ Finset.Icc 1 N) α H W d q).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) H.coe_nonneg) (by positivity))

end TwinPrime.ShortFourier

end
