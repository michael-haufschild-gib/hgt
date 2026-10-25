import GaloisForLFunctions.BezoutValuationIncidence.VaughanTailPowerGainsAtEveryPositiveDamping

/-!
The optimal reciprocal-tail and empty-leg energy decay indices recover the
zeta zero abscissa. Finite Abel inversion identifies the full rate sets across
positive damping, while sharp endpoint statements retain their distinct
power and little-o behavior.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A pointwise Möbius power bound gives the same upper bound on the zero abscissa. -/
theorem zetaZeroAbscissa_le_of_moebius_power_bound {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hM : ∀ n : ℕ, 1 ≤ n → |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ β) :
    zetaZeroAbscissa ≤ β := by
  have hsum (X : ℕ) : (∑ k ∈ range (X + 1), ‖mobiusMertensPartialSum k‖) ≤
      C * ((X : ℝ) + 1) ^ (1 + β) := by
    calc
      _ ≤ ∑ _k ∈ range (X + 1), C * ((X : ℝ) + 1) ^ β := by
        apply sum_le_sum
        intro k hk
        rw [norm_mobiusMertensPartialSum_eq_abs_sum]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · simp only [Icc_eq_empty (by norm_num), sum_empty, abs_zero]
          positivity
        · have hkX : (k : ℝ) ≤ (X : ℝ) + 1 := by exact_mod_cast (mem_range.mp hk).le
          exact (hM k hk1).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg k) hkX hβ) hC)
      _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul, Real.rpow_add (by positivity), Real.rpow_one]
        push_cast
        ring
  have h := zetaZeroAbscissa_le_of_sum_norm_mertens_le (by linarith only [hβ]) hsum
  linarith only [h]

/-- Every exponent strictly above the zero abscissa bounds the actual Möbius partial sums. -/
theorem exists_moebius_power_bound_of_abscissa_lt {β : ℝ} (hβ : zetaZeroAbscissa < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ β := by
  have hβ0 : 0 ≤ β := by linarith only [half_le_zetaZeroAbscissa, hβ]
  obtain ⟨C, hC, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa
    (β - zetaZeroAbscissa) (sub_pos.mpr hβ)
  refine ⟨C * 2 ^ β, by positivity, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := hM n
  rw [norm_mobiusMertensPartialSum_eq_abs_sum, add_sub_cancel] at h
  calc
    _ ≤ C * ((n : ℝ) + 1) ^ β := h
    _ ≤ C * (2 * (n : ℝ)) ^ β :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [hn1]) hβ0) hC
    _ = _ := by rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]; ring

/-- A signed reciprocal-tail gain bounds the zero abscissa quantitatively. -/
theorem zetaZeroAbscissa_le_one_sub_of_vaughan_tail_power {ε η K : ℝ}
    (hε : 0 ≤ ε) (hη : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hF : ∀ n : ℕ, 1 ≤ n → |pmPronicVaughanReciprocalTail ε n| ≤
      K * (n : ℝ) ^ (-ε - η)) : zetaZeroAbscissa ≤ 1 - η := by
  apply zetaZeroAbscissa_le_of_moebius_power_bound
    (C := |pmPronicVaughanReciprocalTail ε 0| + 2 ^ (1 + ε) * K +
      ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1))
  · have hpos : 0 < 1 - η := sub_pos.mpr hη1
    positivity
  · linarith only [hη1]
  · exact fun n hn => abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings hε hη hη1 hK hF hn

/-- Every strict gain below the zero-free width is realized by the actual signed tail. -/
theorem exists_vaughan_tail_power_of_lt_one_sub_abscissa {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 ≤ η) (hηΘ : η < 1 - zetaZeroAbscissa) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |pmPronicVaughanReciprocalTail ε n| ≤ K * (n : ℝ) ^ (-ε - η) := by
  let β : ℝ := (zetaZeroAbscissa + 1 - η) / 2
  have hΘβ : zetaZeroAbscissa < β := by dsimp only [β]; linarith only [hηΘ]
  have hβ1 : β < 1 := by dsimp only [β]; linarith only [hηΘ, hη]
  have hgain : η ≤ 1 - β := by dsimp only [β]; linarith only [hηΘ]
  obtain ⟨C, hC, hM⟩ := exists_moebius_power_bound_of_abscissa_lt hΘβ
  refine ⟨(2 + 1 / ε) * C, by positivity, fun n hn => ?_⟩
  refine (abs_pmPronicVaughanReciprocalTail_le_of_mertens_rate hε hβ1 hC hM hn).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith only [hgain]))
    (by positivity)

/-- The nonnegative tail exponents, with a harmless upper cutoff beyond their possible range. -/
def pmPronicVaughanTailPowerRates (ε : ℝ) : Set ℝ :=
  {η | 0 ≤ η ∧ η < 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
    |pmPronicVaughanReciprocalTail ε n| ≤ K * (n : ℝ) ^ (-ε - η)}

/-- All tail exponents lie below the zero-free width. -/
theorem pmPronicVaughanTailPowerRates_le {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : η ∈ pmPronicVaughanTailPowerRates ε) :
    η ≤ 1 - zetaZeroAbscissa := by
  obtain ⟨hη0, hη1, K, hK, hF⟩ := hη
  rcases eq_or_lt_of_le hη0 with hzero | hpos
  · rw [← hzero]
    linarith only [zetaZeroAbscissa_le_one]
  · have h := zetaZeroAbscissa_le_one_sub_of_vaughan_tail_power hε hpos hη1 hK hF
    linarith only [h]

/-- Every nonnegative strict exponent below the zero-free width is a tail rate. -/
theorem mem_pmPronicVaughanTailPowerRates_of_lt {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 ≤ η) (hηΘ : η < 1 - zetaZeroAbscissa) :
    η ∈ pmPronicVaughanTailPowerRates ε := by
  refine ⟨hη, ?_, exists_vaughan_tail_power_of_lt_one_sub_abscissa hε hη hηΘ⟩
  linarith only [half_le_zetaZeroAbscissa, hηΘ]

/-- The absolute tail estimate always provides the zero saving exponent. -/
theorem zero_mem_pmPronicVaughanTailPowerRates {ε : ℝ} (hε : 0 < ε) :
    0 ∈ pmPronicVaughanTailPowerRates ε := by
  refine ⟨le_rfl, zero_lt_one, 2 + 1 / ε, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_scaled_pmPronicVaughanSmallDensity_tail_le hε n
  change |(n : ℝ) ^ ε * pmPronicVaughanReciprocalTail ε n| ≤ 2 + 1 / ε at h
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 ε)] at h
  have hdiv : |pmPronicVaughanReciprocalTail ε n| ≤ (2 + 1 / ε) / (n : ℝ) ^ ε :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hn0 ε)).mpr (by simpa only [mul_comm] using h)
  simpa only [sub_zero, Real.rpow_neg hn0.le, div_eq_mul_inv] using hdiv

/-- The supremum of the nonnegative powers saved by the actual reciprocal tail. -/
def pmPronicVaughanTailDecayIndex (ε : ℝ) : ℝ := sSup (pmPronicVaughanTailPowerRates ε)

/-- The exact signed-tail decay index is the zero-free width. -/
theorem pmPronicVaughanTailDecayIndex_eq {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanTailDecayIndex ε = 1 - zetaZeroAbscissa := by
  have hz := zero_mem_pmPronicVaughanTailPowerRates hε
  have hne : (pmPronicVaughanTailPowerRates ε).Nonempty := ⟨0, hz⟩
  have hb : BddAbove (pmPronicVaughanTailPowerRates ε) :=
    ⟨1 - zetaZeroAbscissa, fun η hη => pmPronicVaughanTailPowerRates_le hε.le hη⟩
  have hs0 : 0 ≤ sSup (pmPronicVaughanTailPowerRates ε) := le_csSup hb hz
  apply le_antisymm
  · exact csSup_le hne (fun η hη => pmPronicVaughanTailPowerRates_le hε.le hη)
  · by_contra h
    have hlt : sSup (pmPronicVaughanTailPowerRates ε) < 1 - zetaZeroAbscissa := lt_of_not_ge h
    let η : ℝ := (sSup (pmPronicVaughanTailPowerRates ε) + 1 - zetaZeroAbscissa) / 2
    have hη0 : 0 ≤ η := by dsimp only [η]; linarith only [hs0, zetaZeroAbscissa_le_one]
    have hηΘ : η < 1 - zetaZeroAbscissa := by dsimp only [η]; linarith only [hlt]
    have hη := le_csSup hb (mem_pmPronicVaughanTailPowerRates_of_lt hε hη0 hηΘ)
    dsimp only [η] at hη
    linarith only [hη, hlt]

/-- The decay index is independent of the positive damping used to read it. -/
theorem pmPronicVaughanTailDecayIndex_independent {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) :
    pmPronicVaughanTailDecayIndex ε = pmPronicVaughanTailDecayIndex κ := by
  rw [pmPronicVaughanTailDecayIndex_eq hε, pmPronicVaughanTailDecayIndex_eq hκ]

/-- Square-cutoff normalized energy rates are measured in the cutoff variable. -/
def pmPronicVaughanSquareEnergyPowerRates (ε : ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ < 4 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    pmPronicVaughanCentredGram ε n n (n ^ 2) 3 3 / ((n ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
      C * (n : ℝ) ^ (-δ)}

/-- Quartic comparison identifies each energy exponent with one quarter of its tail exponent scale. -/
theorem mem_pmPronicVaughanSquareEnergyPowerRates_iff {ε δ : ℝ} (hε : 0 < ε) :
    δ ∈ pmPronicVaughanSquareEnergyPowerRates ε ↔
      δ / 4 ∈ pmPronicVaughanTailPowerRates ε := by
  constructor
  · rintro ⟨hδ0, hδ4, C, hC, hE⟩
    refine ⟨by linarith only [hδ0], by linarith only [hδ4],
      Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)), Real.sqrt_nonneg _, ?_⟩
    exact fun n hn => abs_pmPronicVaughanReciprocalTail_le_of_square_energy_power hε hC hE hn
  · rintro ⟨hδ0, hδ4, K, hK, hF⟩
    refine ⟨by linarith only [hδ0], by linarith only [hδ4],
      pmPronicPowerDensity ε ^ 2 * K ^ 4, by positivity, fun n hn => ?_⟩
    have h := pmPronicVaughanCentredGram_square_power_bound_of_tail hε hK hF hn
    simpa only [show 4 * (δ / 4) = δ by ring] using h

/-- The supremum of the powers saved by normalized square-cutoff empty-leg energy. -/
def pmPronicVaughanSquareEnergyDecayIndex (ε : ℝ) : ℝ :=
  sSup (pmPronicVaughanSquareEnergyPowerRates ε)

/-- The exact square energy index is four times the zero-free width. -/
theorem pmPronicVaughanSquareEnergyDecayIndex_eq {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanSquareEnergyDecayIndex ε = 4 * (1 - zetaZeroAbscissa) := by
  have hz : 0 ∈ pmPronicVaughanSquareEnergyPowerRates ε :=
    (mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mpr
      (by simpa only [zero_div] using zero_mem_pmPronicVaughanTailPowerRates hε)
  have hne : (pmPronicVaughanSquareEnergyPowerRates ε).Nonempty := ⟨0, hz⟩
  have hupper (δ : ℝ) (hδ : δ ∈ pmPronicVaughanSquareEnergyPowerRates ε) :
      δ ≤ 4 * (1 - zetaZeroAbscissa) := by
    have h := pmPronicVaughanTailPowerRates_le hε.le
      ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mp hδ)
    linarith only [h]
  have hb : BddAbove (pmPronicVaughanSquareEnergyPowerRates ε) := ⟨_, hupper⟩
  have hs0 : 0 ≤ sSup (pmPronicVaughanSquareEnergyPowerRates ε) := le_csSup hb hz
  apply le_antisymm
  · exact csSup_le hne hupper
  · by_contra h
    have hlt : sSup (pmPronicVaughanSquareEnergyPowerRates ε) < 4 * (1 - zetaZeroAbscissa) := lt_of_not_ge h
    let δ : ℝ := (sSup (pmPronicVaughanSquareEnergyPowerRates ε) + 4 * (1 - zetaZeroAbscissa)) / 2
    have hδ0 : 0 ≤ δ / 4 := by dsimp only [δ]; linarith only [hs0, zetaZeroAbscissa_le_one]
    have hδΘ : δ / 4 < 1 - zetaZeroAbscissa := by dsimp only [δ]; linarith only [hlt]
    have hδmem := (mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mpr
      (mem_pmPronicVaughanTailPowerRates_of_lt hε hδ0 hδΘ)
    have hδ := le_csSup hb hδmem
    dsimp only [δ] at hδ
    linarith only [hδ, hlt]

/-- A positive tail decay index is precisely a fixed zero-free strip. -/
theorem pmPronicVaughanTailDecayIndex_pos_iff {ε : ℝ} (hε : 0 < ε) :
    0 < pmPronicVaughanTailDecayIndex ε ↔ zetaZeroAbscissa < 1 := by
  rw [pmPronicVaughanTailDecayIndex_eq hε]
  exact sub_pos

/-- RH is exactly the maximal possible signed-tail decay index. -/
theorem pmPronicVaughanTailDecayIndex_eq_half_iff {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanTailDecayIndex ε = 1 / 2 ↔ RiemannHypothesis := by
  rw [pmPronicVaughanTailDecayIndex_eq hε, ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor <;> intro h <;> linarith only [h]

/-- RH is exactly the maximal possible square energy decay index. -/
theorem pmPronicVaughanSquareEnergyDecayIndex_eq_two_iff {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanSquareEnergyDecayIndex ε = 2 ↔ RiemannHypothesis := by
  rw [pmPronicVaughanSquareEnergyDecayIndex_eq hε, ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor <;> intro h <;> linarith only [h]

/-- No signed reciprocal-tail gain can exceed one half. -/
theorem not_exists_vaughan_tail_power_gt_half {ε η : ℝ}
    (hε : 0 ≤ ε) (hη : 1 / 2 < η) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |pmPronicVaughanReciprocalTail ε n| ≤ K * (n : ℝ) ^ (-ε - η) := by
  rintro ⟨K, hK, hF⟩
  let τ : ℝ := min η (3 / 4)
  have hτhalf : 1 / 2 < τ := lt_min hη (by norm_num)
  have hτ0 : 0 < τ := (by norm_num : (0 : ℝ) < 1 / 2).trans hτhalf
  have hτ1 : τ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hF' (n : ℕ) (hn : 1 ≤ n) :
      |pmPronicVaughanReciprocalTail ε n| ≤ K * (n : ℝ) ^ (-ε - τ) :=
    (hF n hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by have := min_le_left η (3 / 4); dsimp only [τ]; linarith only [this])) hK)
  have h := zetaZeroAbscissa_le_one_sub_of_vaughan_tail_power hε hτ0 hτ1 hK hF'
  linarith only [h, half_le_zetaZeroAbscissa, hτhalf]

/-- No normalized square-cutoff empty-leg energy gain can exceed two in the cutoff variable. -/
theorem not_exists_vaughan_square_energy_power_gt_two {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 2 < δ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      pmPronicVaughanCentredGram ε n n (n ^ 2) 3 3 / ((n ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
        C * (n : ℝ) ^ (-δ) := by
  rintro ⟨C, hC, hE⟩
  apply not_exists_vaughan_tail_power_gt_half hε.le (by linarith only [hδ] : 1 / 2 < δ / 4)
  exact ⟨Real.sqrt (Real.sqrt (2 * C / pmPronicPowerDensity ε ^ 2)), Real.sqrt_nonneg _,
    fun n hn => abs_pmPronicVaughanReciprocalTail_le_of_square_energy_power hε hC hE hn⟩

/-- RH is equivalent to every strict tail gain below one half, without an endpoint assertion. -/
theorem riemannHypothesis_iff_all_strict_vaughan_tail_powers {ε : ℝ}
    (hε : 0 < ε) :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
        |pmPronicVaughanReciprocalTail ε n| ≤ K * (n : ℝ) ^ (-ε - η) := by
  constructor
  · intro hRH η hη0 hηhalf
    apply exists_vaughan_tail_power_of_lt_one_sub_abscissa hε hη0.le
    rw [zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH]
    linarith only [hηhalf]
  · intro hall
    apply zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mp
    apply le_antisymm _ half_le_zetaZeroAbscissa
    by_contra h
    have hΘ : 1 / 2 < zetaZeroAbscissa := lt_of_not_ge h
    let η : ℝ := (1 - zetaZeroAbscissa + 1 / 2) / 2
    have hη0 : 0 < η := by dsimp only [η]; linarith only [zetaZeroAbscissa_le_one]
    have hηhalf : η < 1 / 2 := by dsimp only [η]; linarith only [hΘ]
    obtain ⟨K, hK, hF⟩ := hall η hη0 hηhalf
    have hbound := zetaZeroAbscissa_le_one_sub_of_vaughan_tail_power hε.le hη0
      (hηhalf.trans (by norm_num)) hK hF
    dsimp only [η] at hbound
    linarith only [hbound, hΘ]

/-- RH is equivalent to all strict square energy gains below two. -/
theorem riemannHypothesis_iff_all_strict_vaughan_square_energy_powers {ε : ℝ}
    (hε : 0 < ε) :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → δ < 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        pmPronicVaughanCentredGram ε n n (n ^ 2) 3 3 / ((n ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
          C * (n : ℝ) ^ (-δ) := by
  rw [riemannHypothesis_iff_all_strict_vaughan_tail_powers hε]
  constructor
  · intro hall δ hδ0 hδ2
    have htail : δ / 4 ∈ pmPronicVaughanTailPowerRates ε :=
      ⟨by linarith only [hδ0], by linarith only [hδ2],
        hall (δ / 4) (by linarith only [hδ0]) (by linarith only [hδ2])⟩
    exact ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mpr htail).2.2
  · intro hall η hη0 hηhalf
    have henergy : 4 * η ∈ pmPronicVaughanSquareEnergyPowerRates ε :=
      ⟨by linarith only [hη0], by linarith only [hηhalf],
        hall (4 * η) (by linarith only [hη0]) (by linarith only [hηhalf])⟩
    have htail := ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mp henergy).2.2
    simpa only [show 4 * η / 4 = η by ring] using htail

/-- A positive tail saving holds exactly when the corresponding actual Mertens bound holds. -/
theorem mem_pmPronicVaughanTailPowerRates_iff_moebius_power
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (hη1 : η < 1) :
    η ∈ pmPronicVaughanTailPowerRates ε ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ (1 - η) := by
  constructor
  · rintro ⟨_, _, K, hK, hF⟩
    refine ⟨|pmPronicVaughanReciprocalTail ε 0| + 2 ^ (1 + ε) * K +
      ((1 + ε) * 2 ^ ε) * K * (1 / (1 - η) + 1), ?_, fun n hn => ?_⟩
    · have hpos : 0 < 1 - η := sub_pos.mpr hη1
      positivity
    · exact abs_sum_moebiusReal_le_of_reciprocalTail_bound_all_dampings
        hε.le hη hη1 hK hF hn
  · rintro ⟨C, hC, hM⟩
    refine ⟨hη.le, hη1, (2 + 1 / ε) * C, by positivity, fun n hn => ?_⟩
    have h := abs_pmPronicVaughanReciprocalTail_le_of_mertens_rate hε
      (by linarith only [hη] : 1 - η < 1) hC hM hn
    simpa only [show 1 - (1 - η) = η by ring] using h

/-- The entire tail-rate set, including possible endpoint attainment, is independent of positive damping. -/
theorem pmPronicVaughanTailPowerRates_independent {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    pmPronicVaughanTailPowerRates ε = pmPronicVaughanTailPowerRates κ := by
  have hsub {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
      pmPronicVaughanTailPowerRates α ⊆ pmPronicVaughanTailPowerRates β := by
    intro η hη
    obtain ⟨hη0, hη1, hF⟩ := hη
    rcases eq_or_lt_of_le hη0 with hzero | hpos
    · subst η
      exact zero_mem_pmPronicVaughanTailPowerRates hβ
    · exact (mem_pmPronicVaughanTailPowerRates_iff_moebius_power hβ hpos hη1).mpr
        ((mem_pmPronicVaughanTailPowerRates_iff_moebius_power hα hpos hη1).mp ⟨hη0, hη1, hF⟩)
  exact Set.Subset.antisymm (hsub hε hκ) (hsub hκ hε)

/-- The complete normalized square energy-rate set is also independent of positive damping. -/
theorem pmPronicVaughanSquareEnergyPowerRates_independent {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) :
    pmPronicVaughanSquareEnergyPowerRates ε = pmPronicVaughanSquareEnergyPowerRates κ := by
  ext δ
  rw [mem_pmPronicVaughanSquareEnergyPowerRates_iff hε,
    mem_pmPronicVaughanSquareEnergyPowerRates_iff hκ,
    pmPronicVaughanTailPowerRates_independent hε hκ]

/-- Normalized empty-leg energy rates measured in the square horizon itself. -/
def pmPronicVaughanHorizonEnergyPowerRates (ε : ℝ) : Set ℝ :=
  {γ | 0 ≤ γ ∧ γ < 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    pmPronicVaughanCentredGram ε n n (n ^ 2) 3 3 / ((n ^ 2 : ℕ) : ℝ) ^ (1 - 2 * ε) ≤
      C * ((n ^ 2 : ℕ) : ℝ) ^ (-γ)}

/-- A square-horizon exponent is exactly half the corresponding cutoff exponent. -/
theorem mem_pmPronicVaughanHorizonEnergyPowerRates_iff {ε γ : ℝ} :
    γ ∈ pmPronicVaughanHorizonEnergyPowerRates ε ↔
      2 * γ ∈ pmPronicVaughanSquareEnergyPowerRates ε := by
  have hpow (n : ℕ) : ((n ^ 2 : ℕ) : ℝ) ^ (-γ) = (n : ℝ) ^ (-(2 * γ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  constructor
  · rintro ⟨hγ0, hγ2, C, hC, hE⟩
    exact ⟨by linarith only [hγ0], by linarith only [hγ2], C, hC,
      fun n hn => by simpa only [hpow] using hE n hn⟩
  · rintro ⟨hγ0, hγ2, C, hC, hE⟩
    exact ⟨by linarith only [hγ0], by linarith only [hγ2], C, hC,
      fun n hn => by simpa only [hpow] using hE n hn⟩

/-- The supremum of the empty-leg powers saved in the horizon variable. -/
def pmPronicVaughanHorizonEnergyDecayIndex (ε : ℝ) : ℝ :=
  sSup (pmPronicVaughanHorizonEnergyPowerRates ε)

/-- The exact horizon energy index is twice the zero-free width. -/
theorem pmPronicVaughanHorizonEnergyDecayIndex_eq {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanHorizonEnergyDecayIndex ε = 2 * (1 - zetaZeroAbscissa) := by
  have hz : 0 ∈ pmPronicVaughanHorizonEnergyPowerRates ε :=
    mem_pmPronicVaughanHorizonEnergyPowerRates_iff.mpr
      ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mpr
        (by simpa only [mul_zero, zero_div] using zero_mem_pmPronicVaughanTailPowerRates hε))
  have hne : (pmPronicVaughanHorizonEnergyPowerRates ε).Nonempty := ⟨0, hz⟩
  have hupper (γ : ℝ) (hγ : γ ∈ pmPronicVaughanHorizonEnergyPowerRates ε) :
      γ ≤ 2 * (1 - zetaZeroAbscissa) := by
    have h := pmPronicVaughanTailPowerRates_le hε.le
      ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mp
        (mem_pmPronicVaughanHorizonEnergyPowerRates_iff.mp hγ))
    linarith only [h]
  have hb : BddAbove (pmPronicVaughanHorizonEnergyPowerRates ε) := ⟨_, hupper⟩
  have hs0 : 0 ≤ sSup (pmPronicVaughanHorizonEnergyPowerRates ε) := le_csSup hb hz
  apply le_antisymm
  · exact csSup_le hne hupper
  · by_contra h
    have hlt : sSup (pmPronicVaughanHorizonEnergyPowerRates ε) < 2 * (1 - zetaZeroAbscissa) := lt_of_not_ge h
    let γ : ℝ := (sSup (pmPronicVaughanHorizonEnergyPowerRates ε) + 2 * (1 - zetaZeroAbscissa)) / 2
    have hγ0 : 0 ≤ (2 * γ) / 4 := by dsimp only [γ]; linarith only [hs0, zetaZeroAbscissa_le_one]
    have hγΘ : (2 * γ) / 4 < 1 - zetaZeroAbscissa := by dsimp only [γ]; linarith only [hlt]
    have hγmem : γ ∈ pmPronicVaughanHorizonEnergyPowerRates ε :=
      mem_pmPronicVaughanHorizonEnergyPowerRates_iff.mpr
        ((mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mpr
          (mem_pmPronicVaughanTailPowerRates_of_lt hε hγ0 hγΘ))
    have hγ := le_csSup hb hγmem
    dsimp only [γ] at hγ
    linarith only [hγ, hlt]

/-- RH is precisely the maximal possible square-horizon energy index. -/
theorem pmPronicVaughanHorizonEnergyDecayIndex_eq_one_iff {ε : ℝ} (hε : 0 < ε) :
    pmPronicVaughanHorizonEnergyDecayIndex ε = 1 ↔ RiemannHypothesis := by
  rw [pmPronicVaughanHorizonEnergyDecayIndex_eq hε, ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor <;> intro h <;> linarith only [h]

/-- A positive horizon energy index is precisely a fixed zero-free strip. -/
theorem pmPronicVaughanHorizonEnergyDecayIndex_pos_iff {ε : ℝ} (hε : 0 < ε) :
    0 < pmPronicVaughanHorizonEnergyDecayIndex ε ↔ zetaZeroAbscissa < 1 := by
  rw [pmPronicVaughanHorizonEnergyDecayIndex_eq hε]
  constructor <;> intro h <;> linarith only [h]

/-- The complete square-horizon rate set is independent of positive damping. -/
theorem pmPronicVaughanHorizonEnergyPowerRates_independent {ε κ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) :
    pmPronicVaughanHorizonEnergyPowerRates ε = pmPronicVaughanHorizonEnergyPowerRates κ := by
  ext γ
  rw [mem_pmPronicVaughanHorizonEnergyPowerRates_iff,
    mem_pmPronicVaughanHorizonEnergyPowerRates_iff,
    pmPronicVaughanSquareEnergyPowerRates_independent hε hκ]

#print axioms mem_pmPronicVaughanTailPowerRates_iff_moebius_power
#print axioms pmPronicVaughanTailPowerRates_independent
#print axioms pmPronicVaughanSquareEnergyPowerRates_independent
#print axioms mem_pmPronicVaughanHorizonEnergyPowerRates_iff
#print axioms pmPronicVaughanHorizonEnergyDecayIndex_eq
#print axioms pmPronicVaughanHorizonEnergyDecayIndex_eq_one_iff
#print axioms pmPronicVaughanHorizonEnergyDecayIndex_pos_iff
#print axioms pmPronicVaughanHorizonEnergyPowerRates_independent
#print axioms not_exists_vaughan_tail_power_gt_half
#print axioms not_exists_vaughan_square_energy_power_gt_two
#print axioms riemannHypothesis_iff_all_strict_vaughan_tail_powers
#print axioms riemannHypothesis_iff_all_strict_vaughan_square_energy_powers
#print axioms zero_mem_pmPronicVaughanTailPowerRates
#print axioms pmPronicVaughanTailDecayIndex_eq
#print axioms pmPronicVaughanTailDecayIndex_independent
#print axioms mem_pmPronicVaughanSquareEnergyPowerRates_iff
#print axioms pmPronicVaughanSquareEnergyDecayIndex_eq
#print axioms pmPronicVaughanTailDecayIndex_pos_iff
#print axioms pmPronicVaughanTailDecayIndex_eq_half_iff
#print axioms pmPronicVaughanSquareEnergyDecayIndex_eq_two_iff
#print axioms zetaZeroAbscissa_le_of_moebius_power_bound
#print axioms exists_moebius_power_bound_of_abscissa_lt
#print axioms zetaZeroAbscissa_le_one_sub_of_vaughan_tail_power
#print axioms exists_vaughan_tail_power_of_lt_one_sub_abscissa
#print axioms pmPronicVaughanTailPowerRates_le
#print axioms mem_pmPronicVaughanTailPowerRates_of_lt
end GaloisForLFunctions.BezoutValuationIncidence
