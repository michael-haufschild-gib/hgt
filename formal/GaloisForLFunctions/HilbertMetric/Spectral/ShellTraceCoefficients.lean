import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Concentric shell trace coefficients

For the mixed boundary problem, the degree-zero datum comes from the eigenvalue,
while the higher degrees come from the trace. Pairing complementary powers of the
inner radius gives positive factors in the denominator and explicit attenuation bounds.
-/

open Filter
open scoped Topology

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
  ring

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
  simpa only [mul_zero] using hp.const_mul
    (3 / (Real.sqrt (4 * Real.pi) * (1 - (a : ℝ)) ^ 3))

end

end GaloisForLFunctions.HilbertMetric.ShellTrace
