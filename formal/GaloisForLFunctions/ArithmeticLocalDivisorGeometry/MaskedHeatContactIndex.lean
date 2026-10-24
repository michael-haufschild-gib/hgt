import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedHeatIndex

/-!
# The exact coefficient order controlling masked-pair contact

Within the entire rational threshold bracket, the minimizing integer index is `m / 2`.
The minimum is strict. Thus the growing family of coefficient inequalities has a single
active member at first contact, at an order determined exactly by the central multiplicity.
-/

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

theorem maskedHeatIndex_sub (m k h : ℕ) (t : ℝ) :
    maskedHeatIndex m t k - maskedHeatIndex m t h =
      ((k : ℝ) - h) * ((k : ℝ) + h + 1 - 2 * ((2 * m + 2 : ℝ) * (2 * m + 1)) * t) := by
  unfold maskedHeatIndex
  ring

private theorem middle_index_bracket (m : ℕ) :
    (8 * m + 10 : ℝ) * (m / 2 : ℕ) < (2 * m + 2 : ℝ) * (2 * m + 1) ∧
      (2 * m + 2 : ℝ) * (2 * m + 1) <
        (8 * m + 5 : ℝ) * (((m / 2 : ℕ) : ℝ) + 1) := by
  have hh := Nat.cast_nonneg (α := ℝ) (m / 2)
  by_cases he : m % 2 = 0
  · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show m = 2 * (m / 2) by omega)
    rw [hm]
    constructor <;> nlinarith only [hh]
  · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show m = 2 * (m / 2) + 1 by omega)
    rw [hm]
    constructor <;> nlinarith only [hh]

/-- The minimizer stays in one open unit interval throughout the threshold bracket. -/
theorem maskedHeatIndex_middle_location (m : ℕ) {t : ℝ}
    (hlo : 1 ≤ (8 * m + 10 : ℝ) * t) (hhi : (8 * m + 5 : ℝ) * t ≤ 1) :
    ((m / 2 : ℕ) : ℝ) < ((2 * m + 2 : ℝ) * (2 * m + 1)) * t ∧
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * t < ((m / 2 : ℕ) : ℝ) + 1 := by
  have ht : 0 < t := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ (8 * m + 10 : ℝ) by positivity) (le_of_not_gt hn)
    linarith only [hlo, hp]
  obtain ⟨hl, hu⟩ := middle_index_bracket m
  have hl' := mul_lt_mul_of_pos_right hl ht
  have hu' := mul_lt_mul_of_pos_right hu ht
  have hlower := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) (m / 2))
  have hupper := mul_le_mul_of_nonneg_left hhi (show 0 ≤ ((m / 2 : ℕ) : ℝ) + 1 by positivity)
  constructor <;> nlinarith only [hl', hu', hlower, hupper]

/-- Strict integer minimization of the completed-square index. -/
theorem maskedHeatIndex_strict_min {m h k : ℕ} {t : ℝ}
    (hlo : (h : ℝ) < ((2 * m + 2 : ℝ) * (2 * m + 1)) * t)
    (hhi : ((2 * m + 2 : ℝ) * (2 * m + 1)) * t < (h : ℝ) + 1)
    (hne : k ≠ h) : maskedHeatIndex m t h < maskedHeatIndex m t k := by
  rw [← sub_pos, maskedHeatIndex_sub]
  rcases lt_or_gt_of_ne hne with hk | hk
  · have hstep : (k : ℝ) + 1 ≤ h := by exact_mod_cast (show k + 1 ≤ h by omega)
    apply mul_pos_of_neg_of_neg
    · linarith only [hstep]
    · linarith only [hstep, hlo]
  · have hstep : (h : ℝ) + 1 ≤ k := by exact_mod_cast (show h + 1 ≤ k by omega)
    apply mul_pos
    · linarith only [hstep]
    · linarith only [hstep, hhi]

/-- Throughout the threshold bracket, the exact middle index strictly controls all others. -/
theorem maskedHeatIndex_middle_strict_min (m k : ℕ) {t : ℝ}
    (hlo : 1 ≤ (8 * m + 10 : ℝ) * t) (hhi : (8 * m + 5 : ℝ) * t ≤ 1)
    (hk : k ≠ m / 2) : maskedHeatIndex m t (m / 2) < maskedHeatIndex m t k := by
  obtain ⟨hl, hu⟩ := maskedHeatIndex_middle_location m hlo hhi
  exact maskedHeatIndex_strict_min hl hu hk

/-- A single coefficient inequality certifies the whole finite index family in the bracket. -/
theorem maskedHeatIndex_all_iff_middle (m : ℕ) {t : ℝ}
    (hlo : 1 ≤ (8 * m + 10 : ℝ) * t) (hhi : (8 * m + 5 : ℝ) * t ≤ 1) :
    (∀ k ≤ m + 1, 0 ≤ maskedHeatIndex m t k) ↔ 0 ≤ maskedHeatIndex m t (m / 2) := by
  constructor
  · exact fun h => h _ (by omega)
  · intro h k _
    rcases eq_or_ne k (m / 2) with rfl | hk
    · exact h
    · exact h.trans (maskedHeatIndex_middle_strict_min m k hlo hhi hk).le

theorem maskedHeatIndex_rounding_remainder (m k : ℕ) (t : ℝ) :
    maskedHeatIndex m t k =
      ((k : ℝ) - ((2 * m + 2 : ℝ) * (2 * m + 1)) * t) *
        ((k : ℝ) + 1 - ((2 * m + 2 : ℝ) * (2 * m + 1)) * t) +
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * t * ((8 * m + 10 : ℝ) * t - 1) := by
  unfold maskedHeatIndex
  ring

/-- The lower rational bound is strictly below the first contact, for every multiplicity. -/
theorem maskedHeatIndex_middle_neg_at_lower (m : ℕ) :
    maskedHeatIndex m (1 / (8 * m + 10 : ℝ)) (m / 2) < 0 := by
  have hd : 0 < (8 * m + 10 : ℝ) := by positivity
  have ht : 0 < 1 / (8 * m + 10 : ℝ) := by positivity
  have heq : (8 * m + 10 : ℝ) * (1 / (8 * m + 10 : ℝ)) = 1 := by field_simp
  have hupper : (8 * m + 5 : ℝ) * (1 / (8 * m + 10 : ℝ)) ≤ 1 := by
    nlinarith only [heq, ht]
  obtain ⟨hl, hu⟩ := maskedHeatIndex_middle_location m heq.ge hupper
  rw [maskedHeatIndex_rounding_remainder, heq, sub_self, mul_zero, add_zero]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hl) (sub_pos.mpr hu)

theorem maskedHeatIndex_time_sub (m k : ℕ) (s t : ℝ) :
    maskedHeatIndex m t k - maskedHeatIndex m s k =
      ((2 * m + 2 : ℝ) * (2 * m + 1)) * (t - s) *
        (((2 * m + 4 : ℝ) * (2 * m + 3)) * (t + s) - 2 * ((k : ℝ) + 1)) := by
  unfold maskedHeatIndex
  ring

/-- The controlling coefficient crosses zero only once in the whole threshold bracket. -/
theorem maskedHeatIndex_middle_strictMono (m : ℕ) {s t : ℝ}
    (hlo : 1 ≤ (8 * m + 10 : ℝ) * s) (hhi : (8 * m + 5 : ℝ) * s ≤ 1)
    (hst : s < t) : maskedHeatIndex m s (m / 2) < maskedHeatIndex m t (m / 2) := by
  have hl := (maskedHeatIndex_middle_location m hlo hhi).1
  have hC : 0 < (2 * m + 4 : ℝ) * (2 * m + 3) := by positivity
  have hc : ((m / 2 : ℕ) : ℝ) + 1 < ((2 * m + 4 : ℝ) * (2 * m + 3)) * s := by
    nlinarith only [hl, hlo]
  have hct := mul_lt_mul_of_pos_left hst hC
  rw [← sub_pos, maskedHeatIndex_time_sub]
  apply mul_pos (mul_pos (by positivity) (sub_pos.mpr hst))
  linarith only [hc, hct]

/-- The active even degree is half the total degree, up to the exact parity correction. -/
theorem maskedPair_contact_degree (m : ℕ) :
    2 * (m + 1 - m / 2) = m + 2 + m % 2 := by omega

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
