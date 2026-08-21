import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSelectedCount

/-!
# Parity forcing for Route-T physical packets

Spatial equation-(111) sees an amplitude band in its original cell indexing, whereas the selected
cell receiver counts reindexed even and odd fibres.  This module closes that interface exactly: a
large whole-band physical packet forces the second Maynard alternative for at least one reindexed
parity fibre, with no cardinality loss beyond the necessary half-packet threshold.
-/

noncomputable section
namespace RHTower.Sieve

open MeasureTheory

/-- A large whole-band packet chooses a parity packet; its exact original/reindexed cardinality
identity then turns the corresponding two-way Route-T receiver into its second alternative. -/
theorem routeT_parity_second_alternative_of_large_packet
    {q K : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
    {lambda N R H D V T x alpha : ℝ}
    (hB : B ⊆ Finset.range (2 * K)) (ha : Continuous a)
    (hlambda : 0 < lambda) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hD : D ≤ ‖maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1‖)
    (hV : 0 < V)
    (hsource : ∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V)
    (hlog : 0 ≤ Real.log T)
    (hthreshold : 4 * V * x ^ (1 - alpha) ≤ (D / 2) * (Real.log T) ^ q)
    (heven : IsRouteTMaynardTwoAlternative q
      ((maynardEvenCellFibre B K).card : ℝ) T x alpha)
    (hodd : IsRouteTMaynardTwoAlternative q
      ((maynardOddCellFibre B K).card : ℝ) T x alpha) :
    ((maynardEvenCellFibre B K).card : ℝ) ≤
        T * x ^ (1 + routeTGapMomentNu - 2 * alpha) ∨
      ((maynardOddCellFibre B K).card : ℝ) ≤
        T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hparity := large_maynardFixedAmbientPhysicalDefectPacket_even_or_odd
    B ha hlambda hN hR hH hD
  rcases hparity with hevenLarge | hoddLarge
  · left
    have hevenSubset : maynardEvenCells B ⊆ B := Finset.filter_subset _ _
    have hevenSource : ∀ m ∈ maynardEvenCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
      intro m hm u hu
      exact hsource m (hevenSubset hm) u hu
    have hevenUpper0 :=
      norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
        hlambda hN hR hH (show 0 ≤ 2 * V by positivity) hevenSource
    have hevenCard := card_maynardEvenCellFibre_eq_card_maynardEvenCells hB
    have hevenUpper :
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardEvenCells B)
          a lambda N R H 1‖ ≤
          4 * V * ((maynardEvenCellFibre B K).card : ℝ) := by
      calc
        _ ≤ 2 * (2 * V) * ((maynardEvenCells B).card : ℝ) := hevenUpper0
        _ = 4 * V * ((maynardEvenCellFibre B K).card : ℝ) := by
          rw [hevenCard]
          ring
    exact routeT_second_alternative_of_large_amplitudeBand_packet
      hV hlog hevenLarge hevenUpper hthreshold heven
  · right
    have hoddSubset : maynardOddCells B ⊆ B := Finset.filter_subset _ _
    have hoddSource : ∀ m ∈ maynardOddCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
      intro m hm u hu
      exact hsource m (hoddSubset hm) u hu
    have hoddUpper0 :=
      norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
        hlambda hN hR hH (show 0 ≤ 2 * V by positivity) hoddSource
    have hoddCard := card_maynardOddCellFibre_eq_card_maynardOddCells hB
    have hoddUpper :
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardOddCells B)
          a lambda N R H 1‖ ≤
          4 * V * ((maynardOddCellFibre B K).card : ℝ) := by
      calc
        _ ≤ 2 * (2 * V) * ((maynardOddCells B).card : ℝ) := hoddUpper0
        _ = 4 * V * ((maynardOddCellFibre B K).card : ℝ) := by
          rw [hoddCard]
          ring
    exact routeT_second_alternative_of_large_amplitudeBand_packet
      hV hlog hoddLarge hoddUpper hthreshold hodd

/-- Equation-(111) plus a two-way Route-T receiver has a uniform forced-second interpretation:
if the second count fails, the restricted bad set is null; otherwise its cardinal factor may be
replaced by the second-count scale. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_forced_second
    {q : ℕ} {S : Finset ℕ} {a : ℝ → ℂ}
    {x N R H D V T Y alpha : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hD : 0 < D) (hV : 0 < V) (hT : 0 ≤ T) (hY : 0 < Y)
    (hlog : 0 ≤ Real.log T)
    (hcellLog : 0 ≤ 1 + 2 * (1 + Real.log cellCount))
    (hS : S ⊆ Finset.range cellCount) (ha : Continuous a)
    (hsource : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V)
    (hthreshold : 4 * V * Y ^ (1 - alpha) ≤ D * (Real.log T) ^ q)
    (halt : IsRouteTMaynardTwoAlternative q (S.card : ℝ) T Y alpha) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} ≤
      (4 * (2 * x) * (4 * V) ^ 2 *
        (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
        (1 + 2 * (1 + Real.log cellCount))) / D ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  let bad : Set ℝ := {lambda | D ≤
    ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖}
  by_cases hsecond : (S.card : ℝ) ≤
      T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)
  · have hmeasure :=
      volume_maynardFixedAmbientPhysicalDefectPacket_large_le_card_of_source_bound
        hx hN hR hH (show 0 ≤ 2 * V by positivity) hD S hS a ha hsource
    have hC : 0 ≤ 4 * (2 * x) * (4 * V) ^ 2 := by positivity
    have hnumer :
        4 * (2 * x) * (4 * V) ^ 2 * (S.card : ℝ) *
            (1 + 2 * (1 + Real.log cellCount)) ≤
          4 * (2 * x) * (4 * V) ^ 2 *
            (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
              (1 + 2 * (1 + Real.log cellCount)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsecond hC) hcellLog
    calc
      μ.real bad ≤
          (4 * (2 * x) * (4 * V) ^ 2 * (S.card : ℝ) *
            (1 + 2 * (1 + Real.log cellCount))) / D ^ 2 := by
        simpa only [μ, bad, show 2 * (2 * V) = 4 * V by ring] using hmeasure
      _ ≤ (4 * (2 * x) * (4 * V) ^ 2 *
          (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
          (1 + 2 * (1 + Real.log cellCount))) / D ^ 2 :=
        div_le_div_of_nonneg_right hnumer (sq_nonneg D)
  · have hnull : ∀ᵐ lambda ∂μ, lambda ∉ bad := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
      intro hlambdaBad
      have hlambdaPos : 0 < lambda :=
        lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)
      have hupper0 :=
        norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
          hlambdaPos hN hR hH (show 0 ≤ 2 * V by positivity) hsource
      have hupper :
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ≤
            4 * V * (S.card : ℝ) := by
        calc
          _ ≤ 2 * (2 * V) * (S.card : ℝ) := hupper0
          _ = 4 * V * (S.card : ℝ) := by ring
      exact hsecond (routeT_second_alternative_of_large_amplitudeBand_packet
        hV hlog hlambdaBad hupper hthreshold halt)
    have hzero : μ bad = 0 := measure_eq_zero_iff_ae_notMem.mpr hnull
    have hrhs : 0 ≤
        (4 * (2 * x) * (4 * V) ^ 2 *
          (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
          (1 + 2 * (1 + Real.log cellCount))) / D ^ 2 := by
      positivity
    simpa only [μ, bad, Measure.real, hzero, ENNReal.toReal_zero] using hrhs

/-- A large whole-band packet is covered by its two half-threshold parity bad sets.  Each parity
set is then either null or controlled by the forced second count, so the complete spatial measure
pays exactly two identical second-count bounds and no uncontrolled first alternative. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_parity_forced_second
    {q K : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
    {x N R H D V T Y alpha : ℝ} {cellCount : ℕ}
    (hx : 1 ≤ x) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hD : 0 < D) (hV : 0 < V) (hT : 0 ≤ T) (hY : 0 < Y)
    (hlog : 0 ≤ Real.log T)
    (hcellLog : 0 ≤ 1 + 2 * (1 + Real.log cellCount))
    (hB : B ⊆ Finset.range (2 * K))
    (hBcell : B ⊆ Finset.range cellCount) (ha : Continuous a)
    (hsource : ∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V)
    (hthreshold : 4 * V * Y ^ (1 - alpha) ≤
      (D / 2) * (Real.log T) ^ q)
    (heven : IsRouteTMaynardTwoAlternative q
      ((maynardEvenCellFibre B K).card : ℝ) T Y alpha)
    (hodd : IsRouteTMaynardTwoAlternative q
      ((maynardOddCellFibre B K).card : ℝ) T Y alpha) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1‖} ≤
      2 * ((4 * (2 * x) * (4 * V) ^ 2 *
        (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  let E : Finset ℕ → ℝ → ℂ := fun S lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  let bad : Set ℝ := {lambda | D ≤ ‖E B lambda‖}
  let badEven : Set ℝ := {lambda | D / 2 ≤ ‖E (maynardEvenCells B) lambda‖}
  let badOdd : Set ℝ := {lambda | D / 2 ≤ ‖E (maynardOddCells B) lambda‖}
  have hsub : ∀ᵐ lambda ∂μ,
      lambda ∈ bad → lambda ∈ badEven ∪ badOdd := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    intro hlambdaBad
    have hlambdaPos : 0 < lambda :=
      lt_of_lt_of_le zero_lt_one (hx.trans hlambda.1)
    have hlarge : D ≤
        ‖maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1‖ := by
      simpa only [bad, E, Set.mem_setOf_eq] using hlambdaBad
    have hparity := large_maynardFixedAmbientPhysicalDefectPacket_even_or_odd
      B ha hlambdaPos hN hR hH hlarge
    rcases hparity with he | ho
    · apply Set.mem_union_left
      simpa only [badEven, E, Set.mem_setOf_eq] using he
    · apply Set.mem_union_right
      simpa only [badOdd, E, Set.mem_setOf_eq] using ho
  have hmonoReal : μ.real bad ≤ μ.real (badEven ∪ badOdd) := by
    have hmono : μ bad ≤ μ (badEven ∪ badOdd) := measure_mono_ae hsub
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) hmono
  have hunion : μ.real (badEven ∪ badOdd) ≤
      μ.real badEven + μ.real badOdd := measureReal_union_le _ _
  have hevenSubset : maynardEvenCells B ⊆ B := Finset.filter_subset _ _
  have hoddSubset : maynardOddCells B ⊆ B := Finset.filter_subset _ _
  have hevenRange : maynardEvenCells B ⊆ Finset.range cellCount :=
    hevenSubset.trans hBcell
  have hoddRange : maynardOddCells B ⊆ Finset.range cellCount :=
    hoddSubset.trans hBcell
  have hevenSource : ∀ m ∈ maynardEvenCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
    intro m hm u hu
    exact hsource m (hevenSubset hm) u hu
  have hoddSource : ∀ m ∈ maynardOddCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
    intro m hm u hu
    exact hsource m (hoddSubset hm) u hu
  have hevenAlt : IsRouteTMaynardTwoAlternative q
      ((maynardEvenCells B).card : ℝ) T Y alpha := by
    rw [← card_maynardEvenCellFibre_eq_card_maynardEvenCells hB]
    exact heven
  have hoddAlt : IsRouteTMaynardTwoAlternative q
      ((maynardOddCells B).card : ℝ) T Y alpha := by
    rw [← card_maynardOddCellFibre_eq_card_maynardOddCells hB]
    exact hodd
  have hevenMeasure :=
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_forced_second
      hx hN hR hH (show 0 < D / 2 by positivity) hV hT hY hlog hcellLog
      hevenRange ha hevenSource hthreshold hevenAlt
  have hoddMeasure :=
    volume_maynardFixedAmbientPhysicalDefectPacket_large_le_forced_second
      hx hN hR hH (show 0 < D / 2 by positivity) hV hT hY hlog hcellLog
      hoddRange ha hoddSource hthreshold hoddAlt
  let C : ℝ := (4 * (2 * x) * (4 * V) ^ 2 *
    (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
    (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2
  have hevenMeasure' : μ.real badEven ≤ C := by
    simpa only [μ, badEven, E, C] using hevenMeasure
  have hoddMeasure' : μ.real badOdd ≤ C := by
    simpa only [μ, badOdd, E, C] using hoddMeasure
  calc
    μ.real bad ≤ μ.real (badEven ∪ badOdd) := hmonoReal
    _ ≤ μ.real badEven + μ.real badOdd := hunion
    _ ≤ C + C := add_le_add hevenMeasure' hoddMeasure'
    _ = 2 * C := by ring
    _ = 2 * ((4 * (2 * x) * (4 * V) ^ 2 *
        (T * Y ^ (1 + routeTGapMomentNu - 2 * alpha)) *
        (1 + 2 * (1 + Real.log cellCount))) / (D / 2) ^ 2) := rfl

end RHTower.Sieve
