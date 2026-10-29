import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaIntervalRemainder
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellProfiles
import Mathlib.Algebra.Order.Chebyshev

/-!
# Upper Gamma bounds for disjoint step profiles

At most two disjoint supports contribute to each jump. Their sum therefore
costs at most twice the sum of their Gamma energies. An interval indicator
costs its width times a logarithm, by the exact exterior kernel formula.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals SpacingScaleHarmonicAnalysis HTGeometry BiarithmeticGaugeGeometry

private theorem sq_sum_sub_le_two {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, f i x = 0 ∨ f j x = 0) (x y : ℝ) :
    ((∑ i ∈ s, f i x) - ∑ i ∈ s, f i y) ^ 2 ≤
      2 * ∑ i ∈ s, (f i x - f i y) ^ 2 := by
  classical
  let A := s.filter fun i => f i x ≠ 0
  let B := s.filter fun i => f i y ≠ 0
  let U := A ∪ B
  have hcard (z : ℝ) : (s.filter fun i => f i z ≠ 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact (hd i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij z).elim
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hU : U.card ≤ 2 :=
    (Finset.card_union_le A B).trans (by
      dsimp only [A, B]
      have hx := hcard x
      have hy := hcard y
      omega)
  have hsub : U ⊆ s := by
    intro i hi
    exact (Finset.mem_union.mp hi).elim
      (fun h => (Finset.mem_filter.mp h).1) (fun h => (Finset.mem_filter.mp h).1)
  have hz (i : ι) (hi : i ∈ s) (hn : i ∉ U) : f i x - f i y = 0 := by
    have hx : f i x = 0 := by
      by_contra h; exact hn (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, h⟩)))
    have hy : f i y = 0 := by
      by_contra h; exact hn (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, h⟩)))
    rw [hx, hy, sub_self]
  have he : (∑ i ∈ U, (f i x - f i y)) = ∑ i ∈ s, (f i x - f i y) :=
    Finset.sum_subset hsub hz
  have he2 : (∑ i ∈ U, (f i x - f i y) ^ 2) =
      ∑ i ∈ s, (f i x - f i y) ^ 2 :=
    Finset.sum_subset hsub fun i hi hn => by rw [hz i hi hn]; norm_num
  rw [← Finset.sum_sub_distrib, ← he]
  calc
    _ ≤ (U.card : ℝ) * ∑ i ∈ U, (f i x - f i y) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ 2 * ∑ i ∈ U, (f i x - f i y) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hU)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [he2]

/-- Arbitrary signed profiles on disjoint supports have a uniform Gamma upper bound. -/
theorem levyEnergy_disjoint_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, BoundedVariationOn (f i) univ)
    (hc : ∀ i ∈ s, HasCompactSupport (f i))
    (hsv : BoundedVariationOn (fun x => ∑ i ∈ s, f i x) univ)
    (hsc : HasCompactSupport (fun x => ∑ i ∈ s, f i x))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, f i x = 0 ∨ f j x = 0) :
    levyEnergy (fun x => ∑ i ∈ s, f i x) ≤ 2 * ∑ i ∈ s, levyEnergy (f i) := by
  have hi (i : ι) (hi : i ∈ s) : Integrable (stationaryJump (f i)) archBase :=
    (memLp_levyRoot (hv i hi) (hc i hi)).integrable_sq.congr (levyRoot_sq_ae (f i))
  have hs : Integrable (stationaryJump (fun x => ∑ i ∈ s, f i x)) archBase :=
    (memLp_levyRoot hsv hsc).integrable_sq.congr (levyRoot_sq_ae _)
  have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  calc
    _ = ∫ e, stationaryJump (fun x => ∑ i ∈ s, f i x) e ∂archBase :=
      (stationaryEnergy_eq_levyEnergy hsv hsc).symm
    _ ≤ ∫ e, 2 * ∑ i ∈ s, stationaryJump (f i) e ∂archBase := by
      apply integral_mono_ae hs ((integrable_finsetSum s hi).const_mul 2)
      filter_upwards [ht] with e he
      have h := mul_le_mul_of_nonneg_left (sq_sum_sub_le_two s f hd e.2 (e.2 + e.1))
        (archLevyDensity_pos he).le
      simpa only [stationaryJump, difference, left, right, Finset.mul_sum, mul_assoc,
        mul_left_comm (archLevyDensity e.1) 2] using h
    _ = 2 * ∑ i ∈ s, levyEnergy (f i) := by
      rw [integral_const_mul, integral_finsetSum s hi]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact stationaryEnergy_eq_levyEnergy (hv i hi) (hc i hi)

/-- The quadratic triangle bound holds for compact BV sources, including step functions. -/
theorem levyEnergy_sub_le_two_bv {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    levyEnergy (fun x => f x - g x) ≤ 2 * levyEnergy f + 2 * levyEnergy g := by
  rw [← norm_levyVector_sub_sq hf hg hfc hgc,
    ← norm_levyVector_sq f hf hfc, ← norm_levyVector_sq g hg hgc]
  have hn := norm_sub_le (levyVector f hf hfc) (levyVector g hg hgc)
  have hs := sq_nonneg (‖levyVector f hf hfc‖ - ‖levyVector g hg hgc‖)
  nlinarith only [hn, hs, norm_nonneg (levyVector f hf hfc - levyVector g hg hgc),
    norm_nonneg (levyVector f hf hfc), norm_nonneg (levyVector g hg hgc)]

/-- The positive Gamma tail grows at most logarithmically as its cutoff approaches zero. -/
theorem gammaTailMass_le_log {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    gammaTailMass w ≤ gammaTailMass 1 + Real.exp (1 / 2) / 2 * Real.log (1 / w) := by
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc w 1) := by
    have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Icc w 1) :=
      continuousOn_inv₀.mono fun t ht => ne_of_gt (hw.trans_le ht.1)
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hmono : (∫ t in Ioc w 1, archLevyDensity t) ≤
      ∫ t in Ioc w 1, (Real.exp (1 / 2) / 2) * t⁻¹ := by
    apply setIntegral_mono_on (integrableOn_archLevyDensity_Ioc hw)
      (hinv.const_mul _) measurableSet_Ioc
    intro t ht
    have h := archLevyDensity_le_sqrt_e_div (hw.trans ht.1) ht.2
    simpa only [div_eq_mul_inv, mul_inv, mul_assoc] using h
  have hval : (∫ t in Ioc w 1, (Real.exp (1 / 2) / 2) * t⁻¹) =
      Real.exp (1 / 2) / 2 * Real.log (1 / w) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hw1,
      integral_inv_of_pos hw (by norm_num)]
  have hsplit : gammaTailMass w = (∫ t in Ioc w 1, archLevyDensity t) + gammaTailMass 1 := by
    unfold gammaTailMass
    rw [← Ioc_union_Ioi_eq_Ioi hw1]
    apply setIntegral_union (by
      apply disjoint_left.mpr
      intro t ht ht'; exact (not_lt_of_ge ht.2) ht') measurableSet_Ioi
      (integrableOn_archLevyDensity_Ioc hw)
      (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi (by norm_num))
  rw [hval] at hmono
  linarith only [hsplit, hmono]

private theorem gammaDifference_indicator_integral (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ x, ∫⁻ y, gammaDifference (S.indicator (fun _ => (1 : ℝ))) x y) =
      2 * ∫⁻ x in S, ∫⁻ y in Sᶜ, ENNReal.ofReal (archLevyDensity |y - x|) := by
  let K : ℝ → ℝ → ℝ≥0∞ := fun x y => ENNReal.ofReal (archLevyDensity |y - x|)
  have hm : Measurable (fun p : ℝ × ℝ => K p.1 p.2) :=
    ENNReal.measurable_ofReal.comp
      (measurable_archLevyDensity.comp (measurable_snd.sub measurable_fst).abs)
  have hrow (x : ℝ) : (∫⁻ y, gammaDifference (S.indicator (fun _ => (1 : ℝ))) x y) =
      S.indicator (fun x => ∫⁻ y in Sᶜ, K x y) x +
        Sᶜ.indicator (fun x => ∫⁻ y in S, K x y) x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, indicator_of_notMem (show x ∉ Sᶜ from not_not.mpr hx), add_zero,
        ← lintegral_indicator hS.compl]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ S <;> simp [gammaDifference, K, hx, hy]
    · rw [indicator_of_notMem hx, indicator_of_mem (show x ∈ Sᶜ from hx), zero_add,
        ← lintegral_indicator hS]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ S <;> simp [gammaDifference, K, hx, hy]
  rw [lintegral_congr hrow,
    lintegral_add_left ((hm.lintegral_prod_right' (ν := volume.restrict Sᶜ)).indicator hS),
    lintegral_indicator hS, lintegral_indicator hS.compl]
  have he : (∫⁻ x in Sᶜ, ∫⁻ y in S, K x y) = ∫⁻ x in S, ∫⁻ y in Sᶜ, K x y := by
    rw [lintegral_lintegral_swap hm.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro y
    simp only [K, abs_sub_comm]
  rw [he, two_mul]

/-- An actual logarithmic cell has only its two exterior boundary interactions. -/
theorem rawCell_gamma_eq_exterior (a : ℕ) :
    ENNReal.ofReal (levyEnergy (rawCell a)) =
      ∫⁻ x in Ioo (Real.log (a : ℝ)) (Real.log ((a + 1 : ℕ) : ℝ)),
        ∫⁻ y in Iio (Real.log (a : ℝ)) ∪ Ioi (Real.log ((a + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (archLevyDensity |y - x|) := by
  let L := Real.log (a : ℝ)
  let U := Real.log ((a + 1 : ℕ) : ℝ)
  have hleft : volume.restrict (Ico L U) = volume.restrict (Ioo L U) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ico.symm
  have hright : volume.restrict ((Ico L U)ᶜ) = volume.restrict (Iio L ∪ Ioi U) := by
    apply Measure.restrict_congr_set
    filter_upwards [Measure.ae_ne volume L, Measure.ae_ne volume U] with x hxL hxU
    change (¬(L ≤ x ∧ x < U)) = (x < L ∨ U < x)
    apply propext
    constructor
    · intro hn
      by_cases hx : x < L
      · exact Or.inl hx
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt fun h => hn ⟨le_of_not_gt hx, h⟩) hxU.symm)
    · intro h hn
      exact h.elim (fun h => (not_lt_of_ge hn.1) h) (fun h => (not_lt_of_ge h.le) hn.2)
  have h := gammaDifference_indicator_integral (Ico L U) measurableSet_Ico
  rw [show (Ico L U).indicator (fun _ => (1 : ℝ)) = rawCell a from rfl,
    gammaDifference_eq_two_levyEnergy (rawCell_bv a) (rawCell_compact a), hleft, hright] at h
  exact (ENNReal.mul_left_inj (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
    (by simpa only [mul_comm] using h)

/-- The full Gamma cost of a step cell is at most logarithmic per unit mass. -/
theorem rawCell_levyEnergy_le_log {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (rawCell a) ≤ logCellWidth a *
      (Real.exp (1 / 2) * Real.log (1 / logCellWidth a) +
        2 * gammaTailMass 1 + Real.exp (1 / 2)) := by
  have hw := logCellWidth_pos ha
  have hw1 : logCellWidth a ≤ 1 := (logCellWidth_le_inv ha).trans
    ((div_le_one (by exact_mod_cast (show 0 < a by omega))).mpr (by exact_mod_cast ha))
  have hab : Real.log (a : ℝ) < Real.log ((a + 1 : ℕ) : ℝ) := by
    exact Real.log_lt_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast Nat.lt_succ_self a)
  have hwidth : Real.log ((a + 1 : ℕ) : ℝ) - Real.log (a : ℝ) = logCellWidth a := by
    simp only [logCellWidth, Nat.cast_add, Nat.cast_one]
  have h := gamma_interval_exterior_kernel_le hab (by rwa [hwidth])
  rw [← rawCell_gamma_eq_exterior a, hwidth] at h
  have hr : levyEnergy (rawCell a) ≤ logCellWidth a *
      (2 * gammaTailMass (logCellWidth a) + Real.exp (1 / 2)) := by
    have ht0 := gammaTailMass_nonneg hw
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have ht := gammaTailMass_le_log hw hw1
  exact hr.trans (mul_le_mul_of_nonneg_left (by linarith only [ht]) hw.le)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
