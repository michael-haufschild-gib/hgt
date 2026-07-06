import GaloisForLFunctions.RHTower.ValMeasure

/-!
# The limit valuation measure, its Stieltjes form, and the mean-valuation density

The valuation atomic measures `valMeasure T` increase with the height, so they have a monotone limit
`valMeasureInf = ⨆_n valMeasure n`, the total off-line valuation measure on ℝ; under RH it is the
zero measure.

Two derived objects live on the line:

* **(a) the Stieltjes measure** of the valuation content: the monotone content `T ↦ valMass T`
  induces a Stieltjes function whose measure assigns to `(a, b]` the enclosed valuation
  `valMass b − valMass a` (right-continuously normalised), a genuine Borel measure on ℝ.
* **(b) the mean-valuation density** `meanVal T = valMass T / (#enclosed heights)`, a rational line
  profile bounded below by the window depth; its staying `≥ 1` is the level-1 graded rung — every
  enclosed jump carries positive 2-adic valuation — and it is finite-carrier-shadowable through the
  filtration length.
-/

namespace RHTower

open Complex Set Metric MeasureTheory
open scoped ENNReal

/-! ## The monotone limit measure -/

/-- The valuation measures increase with the height: enclosing more zero heights only adds atoms. -/
theorem valMeasure_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : valMeasure T₁ ≤ valMeasure T₂ := by
  rw [valMeasure, valMeasure,
    ← Finset.sum_sdiff (Finset.image_subset_image (boxFinset_subset h))]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => Measure.zero_le _))

/-- **The limit valuation measure** on ℝ: the monotone supremum of the window measures, the total
off-line valuation measure. -/
noncomputable def valMeasureInf : Measure ℝ := ⨆ n : ℕ, valMeasure (n : ℝ)

theorem valMeasure_le_valMeasureInf (T : ℝ) : valMeasure T ≤ valMeasureInf :=
  le_trans (valMeasure_mono (Nat.le_ceil T)) (le_iSup (fun n : ℕ => valMeasure (n : ℝ)) ⌈T⌉₊)

/-- **Under RH the limit measure vanishes.**  With no off-line heights every window measure is zero,
so is their supremum. -/
theorem valMeasureInf_eq_zero_of_rh (h : RiemannHypothesis) : valMeasureInf = 0 := by
  have hz : ∀ n : ℕ, valMeasure (n : ℝ) = 0 := by
    intro n
    have hemp : (boxFinset (n : ℝ)).image Complex.im = ∅ := by
      rw [image_im_eq_empty_iff]
      exact rh_iff_forall_boxZeros_empty.mp h n
    rw [valMeasure, hemp, Finset.sum_empty]
  rw [valMeasureInf]
  simp only [hz, iSup_const]

/-! ## (a) The Stieltjes measure of the valuation content -/

/-- The valuation content is monotone as a real-valued distribution function. -/
theorem valMass_mono_real : Monotone (fun T => (valMass T : ℝ)) :=
  fun _ _ h => Nat.cast_le.mpr (valMass_mono h)

/-- **The valuation distribution function** as a Stieltjes function on ℝ: the right-continuous
normalisation of the valuation content `T ↦ valMass T`. -/
noncomputable def valDistribution : StieltjesFunction ℝ := valMass_mono_real.stieltjesFunction

/-- **The Stieltjes measure of the valuation content** on ℝ. -/
noncomputable def valStieltjesMeasure : Measure ℝ := valDistribution.measure

/-- **The Stieltjes measure of a window** is the enclosed valuation content over `(a, b]`. -/
theorem valStieltjesMeasure_Ioc (a b : ℝ) :
    valStieltjesMeasure (Set.Ioc a b)
      = ENNReal.ofReal (valDistribution b - valDistribution a) :=
  StieltjesFunction.measure_Ioc _ a b

/-! ## (b) The mean-valuation density -/

/-- **The mean-valuation density**: the average 2-adic valuation over the enclosed zero heights,
a rational-valued line profile. -/
noncomputable def meanVal (T : ℝ) : ℚ :=
  (valMass T : ℚ) / (((boxFinset T).image Complex.im).card : ℚ)

/-- **The mean density is bounded below by the window depth.**  If the depth is at least `k` then
the average valuation over the enclosed heights is at least `k`. -/
theorem le_meanVal_of_le_windowDepth {k : ℕ} {T : ℝ}
    (hne : ((boxFinset T).image Complex.im).Nonempty) (h : (k : ℕ∞) ≤ windowDepth T) :
    (k : ℚ) ≤ meanVal T := by
  set s := (boxFinset T).image Complex.im with hs
  rw [windowDepth, ← hs] at h
  have hcard : 0 < s.card := Finset.card_pos.mpr hne
  have hterm : ∀ t ∈ s, k ≤ filtrationLength t := by
    intro t ht
    have hle := Finset.le_inf_iff.mp h t ht
    exact_mod_cast hle
  have hsum : s.card * k ≤ valMass T := by
    rw [valMass, ← hs]
    calc s.card * k = ∑ _t ∈ s, k := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ t ∈ s, filtrationLength t := Finset.sum_le_sum hterm
  rw [meanVal, ← hs, le_div_iff₀ (by exact_mod_cast hcard : (0 : ℚ) < (s.card : ℚ))]
  calc (k : ℚ) * (s.card : ℚ) = ((s.card * k : ℕ) : ℚ) := by push_cast; ring
    _ ≤ (valMass T : ℚ) := by exact_mod_cast hsum

/-- **The level-1 graded rung.**  The window depth is at least `1` iff `V 1 T = 0` — every enclosed
jump carries positive 2-adic valuation (has even order). -/
theorem V_one_eq_zero_iff_one_le_windowDepth (T : ℝ) :
    V 1 T = 0 ↔ 1 ≤ windowDepth T := by
  rw [V_eq_zero_iff_le_windowDepth, Nat.cast_one]

/-- Positive valuation at every enclosed height is the depth-`≥1` graded rung. -/
theorem one_le_windowDepth_iff_forall_pos {T : ℝ} :
    1 ≤ windowDepth T ↔ ∀ t ∈ (boxFinset T).image Complex.im, 0 < filtrationLength t := by
  rw [windowDepth, show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from (Nat.cast_one).symm, Finset.le_inf_iff]
  refine forall₂_congr fun t _ => ?_
  rw [Nat.cast_le]
  exact Nat.one_le_iff_ne_zero.trans Nat.pos_iff_ne_zero.symm

/-- **The mean density is finite-carrier-shadowable.**  Its atom weights are the filtration lengths,
each of which agrees with the finite carrier's under the transport (`filtrationLength_eq_finite`); on
matching height data the whole mean-valuation profile is a decidable finite-carrier datum. -/
theorem meanVal_eq_of_filtrationLength_eq {T : ℝ} {g : ℝ → ℕ}
    (hg : ∀ t ∈ (boxFinset T).image Complex.im, filtrationLength t = g t) :
    meanVal T = (∑ t ∈ (boxFinset T).image Complex.im, g t : ℚ)
      / (((boxFinset T).image Complex.im).card : ℚ) := by
  rw [meanVal, valMass]
  congr 2
  push_cast
  exact Finset.sum_congr rfl (fun t ht => by rw [hg t ht])

end RHTower
