import GaloisForLFunctions.HilbertMetric.Spectral.DiagonalCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Concentric shell trace coefficients

For the mixed boundary problem in Hong (arXiv:2611.16596, §5), the degree-zero
datum comes from the eigenvalue, while the higher degrees come from the trace.
Pairing complementary powers of the inner radius gives positive factors in the
denominator and explicit attenuation bounds.
-/

open Filter
open scoped NNReal Topology

namespace GaloisForLFunctions.HilbertMetric.ShellTrace

noncomputable section

/-- Inner radius of a concentric shell of outer radius one. -/
abbrev Radius := Set.Ioo (0 : ℝ) 1

/-- The degree-`l` mixed Steklov level from radial separation in dimension three. -/
def level (a : Radius) (l : ℕ) : ℝ :=
  ((l : ℝ) + (l + 1 : ℝ) * (a : ℝ) ^ (2 * l + 1)) / (1 - (a : ℝ) ^ (2 * l + 1))

private def gapNumerator (a : ℝ) (l : ℕ) : ℝ :=
  ((l : ℝ) + (l + 1 : ℝ) * a ^ (2 * l + 1)) * (1 - a) -
    a * (1 - a ^ (2 * l + 1))

/-- Pair the powers with exponents `k+1` and `2l-k` in the geometric sum. -/
private theorem gapNumerator_eq_sum (a : ℝ) (l : ℕ) :
    gapNumerator a l = (1 - a) * ∑ k ∈ Finset.range l,
      (1 - a ^ (k + 1)) * (1 - a ^ (2 * l - k)) := by
  have hreflect :
      (∑ k ∈ Finset.range l, a ^ (2 * l - k)) =
        ∑ k ∈ Finset.range l, a ^ (l + k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => a ^ (l + k + 1)) l]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    have := Finset.mem_range.mp hk
    omega
  have hsplit :
      (∑ k ∈ Finset.range l, a ^ (k + 1)) +
        (∑ k ∈ Finset.range l, a ^ (2 * l - k)) =
          (∑ k ∈ Finset.range (2 * l + 1), a ^ k) - 1 := by
    rw [hreflect, Finset.sum_range_succ', pow_zero, two_mul, Finset.sum_range_add]
    ring
  have hprod (k : ℕ) (hk : k ∈ Finset.range l) :
      (1 - a ^ (k + 1)) * (1 - a ^ (2 * l - k)) =
        (1 + a ^ (2 * l + 1)) - a ^ (k + 1) - a ^ (2 * l - k) := by
    have he : k + 1 + (2 * l - k) = 2 * l + 1 := by
      have := Finset.mem_range.mp hk
      omega
    rw [← he, pow_add]
    ring
  have hsum :
      (∑ k ∈ Finset.range l, (1 - a ^ (k + 1)) * (1 - a ^ (2 * l - k))) =
      (l : ℝ) * (1 + a ^ (2 * l + 1)) -
        ((∑ k ∈ Finset.range (2 * l + 1), a ^ k) - 1) := by
    rw [Finset.sum_congr rfl hprod, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linear_combination -hsplit
  have hgeom := geom_sum_mul_neg a (2 * l + 1)
  rw [hsum, gapNumerator]
  linear_combination hgeom

private theorem gapNumerator_bounds (a : Radius) (l : ℕ) :
    (l : ℝ) * (1 - (a : ℝ)) ^ 3 ≤ gapNumerator a l ∧
      gapNumerator a l ≤ (l : ℝ) * (1 - (a : ℝ)) := by
  have ha : 0 < (a : ℝ) := a.2.1
  have hb : (a : ℝ) < 1 := a.2.2
  have hpos : 0 ≤ 1 - (a : ℝ) := sub_nonneg.mpr hb.le
  have hpow (n : ℕ) (hn : 1 ≤ n) : (a : ℝ) ^ n ≤ (a : ℝ) := by
    simpa only [pow_one] using pow_le_pow_of_le_one ha.le hb.le hn
  have hterm (k : ℕ) (hk : k ∈ Finset.range l) :
      (1 - (a : ℝ)) ^ 2 ≤ (1 - (a : ℝ) ^ (k + 1)) * (1 - (a : ℝ) ^ (2 * l - k)) ∧
        (1 - (a : ℝ) ^ (k + 1)) * (1 - (a : ℝ) ^ (2 * l - k)) ≤ 1 := by
    have h₁ := sub_le_sub_left (hpow (k + 1) (by omega)) 1
    have h₂ := sub_le_sub_left (hpow (2 * l - k) (by
      have := Finset.mem_range.mp hk
      omega)) 1
    refine ⟨?_, ?_⟩
    · rw [pow_two]
      exact mul_le_mul h₁ h₂ hpos (hpos.trans h₁)
    · simpa only [one_mul] using
        mul_le_mul (sub_le_self 1 (pow_nonneg ha.le (k + 1)))
          (sub_le_self 1 (pow_nonneg ha.le (2 * l - k))) (hpos.trans h₂) zero_le_one
  rw [gapNumerator_eq_sum]
  constructor
  · calc
      _ = (1 - (a : ℝ)) * ∑ _ ∈ Finset.range l, (1 - (a : ℝ)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => (hterm k hk).1) hpos
  · calc
      _ ≤ (1 - (a : ℝ)) * ∑ _ ∈ Finset.range l, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => (hterm k hk).2) hpos
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, mul_comm]

theorem level_zero (a : Radius) : level a 0 = (a : ℝ) / (1 - (a : ℝ)) := by
  simp [level]

/-- Every angular level is strictly separated from the radial level. -/
theorem level_zero_lt (a : Radius) (n : ℕ) : level a 0 < level a (n + 1) := by
  have h₁ : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
  have h₂ : 0 < 1 - (a : ℝ) ^ (2 * (n + 1) + 1) :=
    sub_pos.mpr (pow_lt_one₀ a.2.1.le a.2.2 (by omega))
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hd := (mul_pos hn (pow_pos h₁ 3)).trans_le (gapNumerator_bounds a (n + 1)).1
  rw [level_zero, level, div_lt_div_iff₀ h₁ h₂]
  exact sub_pos.mp hd

/-- Degree zero is measured by the eigenvalue shift. -/
def radialGain (a : Radius) : ℝ := 1 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) ^ 2)

/-- The normalized trace gain for angular degree `n+1`. -/
def angularGain (a : Radius) (n : ℕ) : ℝ :=
  (2 * (n + 1 : ℕ) + 1 : ℝ) * (a : ℝ) ^ (n + 1) /
    (Real.sqrt (4 * Real.pi) * gapNumerator a (n + 1))

/-- The cleared denominator is the radial gap times the two trace normalizers. -/
theorem angularGain_eq_level_gap (a : Radius) (n : ℕ) :
    angularGain a n =
      (2 * (n + 1 : ℕ) + 1 : ℝ) * (a : ℝ) ^ (n + 1) /
        (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) *
          (1 - (a : ℝ) ^ (2 * (n + 1) + 1)) * (level a (n + 1) - level a 0)) := by
  have h₁ : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
  have h₂ : 0 < 1 - (a : ℝ) ^ (2 * (n + 1) + 1) :=
    sub_pos.mpr (pow_lt_one₀ a.2.1.le a.2.2 (by omega))
  unfold angularGain
  congr 1
  rw [level_zero, level, gapNumerator]
  field_simp [h₁.ne', h₂.ne']

/-- Explicit positive constants sandwich the trace gain at every angular degree. -/
theorem angularGain_bounds (a : Radius) (n : ℕ) :
    2 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ))) * (a : ℝ) ^ (n + 1)
        ≤ angularGain a n ∧
      angularGain a n ≤
        3 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) ^ 3) * (a : ℝ) ^ (n + 1) := by
  have h₁ : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
  have hs : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hp : 0 ≤ (a : ℝ) ^ (n + 1) := pow_nonneg a.2.1.le _
  obtain ⟨hl, hu⟩ := gapNumerator_bounds a (n + 1)
  have hd : 0 < gapNumerator a (n + 1) :=
    (mul_pos (by linarith only [hn]) (pow_pos h₁ 3)).trans_le hl
  have hmin : (2 : ℝ) * (↑(n + 1) : ℝ) ≤ 2 * ↑(n + 1) + 1 := by linarith
  have hmax : (2 : ℝ) * (↑(n + 1) : ℝ) + 1 ≤ 3 * ↑(n + 1) := by linarith only [hn]
  unfold angularGain
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  constructor
  · apply (div_le_div_iff₀ (mul_pos hs h₁) (mul_pos hs hd)).mpr
    calc
      _ ≤ (2 * (a : ℝ) ^ (n + 1)) * (Real.sqrt (4 * Real.pi) *
            ((↑(n + 1) : ℝ) * (1 - (a : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hs.le) (by positivity)
      _ = (2 * ↑(n + 1) * (a : ℝ) ^ (n + 1)) *
          (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmin hp) (mul_pos hs h₁).le
  · apply (div_le_div_iff₀ (mul_pos hs hd) (mul_pos hs (pow_pos h₁ 3))).mpr
    calc
      _ ≤ (3 * ↑(n + 1) * (a : ℝ) ^ (n + 1)) *
          (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hp)
          (mul_pos hs (pow_pos h₁ 3)).le
      _ = (3 * (a : ℝ) ^ (n + 1)) * (Real.sqrt (4 * Real.pi) *
            ((↑(n + 1) : ℝ) * (1 - (a : ℝ)) ^ 3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hs.le) (by positivity)

theorem angularGain_pos (a : Radius) (n : ℕ) : 0 < angularGain a n := by
  have ha : 0 < (a : ℝ) := a.2.1
  have hb : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
  exact (show 0 < 2 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ))) * (a : ℝ) ^ (n + 1) by
    positivity).trans_le (angularGain_bounds a n).1

/-- High angular degrees vanish in the trace, despite every gain being positive. -/
theorem angularGain_tendsto_zero (a : Radius) :
    Tendsto (angularGain a) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => (angularGain_pos a n).le)
    (fun n => (angularGain_bounds a n).2) ?_
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one a.2.1.le a.2.2).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_apply, mul_zero] using hp.const_mul
    (3 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) ^ 3))

/-- A single unit harmonic defeats any proposed uniform inverse bound. -/
theorem no_uniform_angular_inverse_bound (a : Radius) :
    ¬ ∃ C : ℝ, ∀ n, 1 ≤ C * angularGain a n := by
  rintro ⟨C, hC⟩
  have hz : Tendsto (fun n => C * angularGain a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (angularGain_tendsto_zero a).const_mul C
  obtain ⟨n, hn⟩ := (hz.eventually_lt_const zero_lt_one).exists
  exact (not_lt_of_ge (hC n)) hn

/-- The radial eigenvalue datum and the angular trace data are measured together. -/
def gain (a : Radius) : ℕ → Set.Ioi (0 : ℝ)
  | 0 => ⟨radialGain a, by
      change 0 < radialGain a
      have : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
      unfold radialGain
      positivity⟩
  | n + 1 => ⟨angularGain a n, angularGain_pos a n⟩

/-- A positive common prefactor for radial and angular gains. -/
def gainFloor (a : Radius) : ℝ :=
  min (radialGain a) (2 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ))))

private theorem gainFloor_pos (a : Radius) : 0 < gainFloor a := by
  have : 0 < 1 - (a : ℝ) := sub_pos.mpr a.2.2
  exact lt_min (show 0 < (gain a 0 : ℝ) from (gain a 0).2) (by positivity)

private theorem gainFloor_mul_pow_le (a : Radius) (l : ℕ) :
    gainFloor a * (a : ℝ) ^ l ≤ (gain a l : ℝ) := by
  cases l with
  | zero =>
    rw [pow_zero, mul_one]
    change min (radialGain a) _ ≤ radialGain a
    exact min_le_left _ _
  | succ n =>
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (pow_nonneg a.2.1.le _)).trans (angularGain_bounds a n).1

/-- At every resolution threshold the data determine the retained modes, including
the mean displacement from the eigenvalue. -/
theorem modal_measure_injective {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Radius) (degree : ι → ℕ) :
    Function.Injective (fun signal : ι → E => fun i => (gain a (degree i) : ℝ) • signal i) :=
  DiagonalCutoff.measure_injective fun i => gain a (degree i)

/-- The multiplier defining the squared modal Sobolev norm. -/
def sobolevWeight (s : ℝ≥0) (l : ℕ) : ℝ :=
  (1 + (l : ℝ) * (l + 1 : ℝ)) ^ (s : ℝ)

/-- The shell cutoff pays exponential noise amplification and an inverse Sobolev
factor for the discarded signal. The sum permits arbitrary harmonic multiplicities. -/
theorem cutoff_squared_error {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Radius)
    (degree : ι → ℕ) (L : ℕ) (s : ℝ≥0) (signal noise : ι → E) :
    (∑ i, ‖DiagonalCutoff.recover (Finset.univ.filter fun j => degree j ≤ L)
      (fun j => gain a (degree j))
      (fun j => (gain a (degree j) : ℝ) • signal j + noise j) i - signal i‖ ^ 2) ≤
      ((gainFloor a * (a : ℝ) ^ L) ^ 2)⁻¹ * (∑ i, ‖noise i‖ ^ 2) +
      (sobolevWeight s (L + 1))⁻¹ * (∑ i, sobolevWeight s (degree i) * ‖signal i‖ ^ 2) := by
  rw [DiagonalCutoff.squared_error]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  apply add_le_add
  · rw [Finset.mul_sum]
    have hc : 0 < gainFloor a * (a : ℝ) ^ L := mul_pos (gainFloor_pos a) (pow_pos a.2.1 _)
    calc
      _ ≤ ∑ i with degree i ≤ L, ((gainFloor a * (a : ℝ) ^ L) ^ 2)⁻¹ * ‖noise i‖ ^ 2 := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have hg : 0 < (gain a (degree i) : ℝ) := (gain a (degree i)).2
        have hle : gainFloor a * (a : ℝ) ^ L ≤ (gain a (degree i) : ℝ) :=
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one a.2.1.le a.2.2.le (Finset.mem_filter.mp hi).2)
            (gainFloor_pos a).le).trans (gainFloor_mul_pow_le a _)
        rw [inv_pow]
        exact (inv_le_inv₀ (sq_pos_of_pos hg) (sq_pos_of_pos hc)).mpr
          ((sq_le_sq₀ hc.le hg.le).mpr hle)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro i _ _
        positivity)
  · rw [Finset.mul_sum]
    have hw : 0 < sobolevWeight s (L + 1) := by unfold sobolevWeight; positivity
    calc
      _ ≤ ∑ i with L < degree i,
          (sobolevWeight s (L + 1))⁻¹ * (sobolevWeight s (degree i) * ‖signal i‖ ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hdeg : ((L + 1 : ℕ) : ℝ) ≤ (degree i : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hi).2
        have hle : sobolevWeight s (L + 1) ≤ sobolevWeight s (degree i) := by
          unfold sobolevWeight
          refine Real.rpow_le_rpow (by positivity) (add_le_add le_rfl ?_) s.2
          exact mul_le_mul hdeg (add_le_add hdeg le_rfl) (by positivity) (by positivity)
        rw [inv_mul_eq_div, le_div_iff₀ hw, mul_comm (‖signal i‖ ^ 2)]
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro i _ _
        unfold sobolevWeight
        positivity)

#print axioms angularGain_eq_level_gap
#print axioms no_uniform_angular_inverse_bound
#print axioms modal_measure_injective
#print axioms cutoff_squared_error

end

end GaloisForLFunctions.HilbertMetric.ShellTrace
