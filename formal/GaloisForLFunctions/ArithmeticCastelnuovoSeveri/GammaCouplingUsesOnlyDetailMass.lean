import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaFiniteMeanZeroCoupling
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellGammaAccounting

/-!
# Complete-cell Gamma coupling factors through ordinary detail mass

Mean-zero cancellation removes every far charge from the coarse/detail pairing.
The remaining crossing measures have bounded mass per cell. Thus the actual
mixed Gamma form uses ordinary detail square mass, without its logarithmic cost.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals BiarithmeticGaugeGeometry HTGeometry

/-- The actual Gamma polarization between pair averages and balanced details. -/
def completeGammaMixed (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  levyEnergy (completePairProfile q d X) - levyEnergy (averageSectionProfile q X) -
    levyEnergy (haarSectionProfile d X)

/-- A jump-one balanced profile has absolute value at most one. -/
theorem abs_haarProfile_le_one {a : ℕ} (ha : 1 ≤ a) (x : ℝ) :
    |haarProfile a x| ≤ 1 := by
  have hl : 0 ≤ haarLeftCoeff a := div_nonneg
    (logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega)).le
    (add_pos (logCellWidth_pos (show 1 ≤ 2 * a by omega))
      (logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega))).le
  have hr : 0 ≤ haarRightCoeff a := div_nonneg
    (logCellWidth_pos (show 1 ≤ 2 * a by omega)).le
    (add_pos (logCellWidth_pos (show 1 ≤ 2 * a by omega))
      (logCellWidth_pos (show 1 ≤ 2 * a + 1 by omega))).le
  calc
    _ ≤ |haarLeftCoeff a * rawCell (2 * a) x| +
        |haarRightCoeff a * rawCell (2 * a + 1) x| := abs_sub _ _
    _ = haarLeftCoeff a * |rawCell (2 * a) x| +
        haarRightCoeff a * |rawCell (2 * a + 1) x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hl, abs_of_nonneg hr]
    _ ≤ haarLeftCoeff a + haarRightCoeff a := by
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left (rawCell_bound (2 * a) x) hl)
        (mul_le_mul_of_nonneg_left (rawCell_bound (2 * a + 1) x) hr)
    _ = 1 := haarCoeff_sum ha

/-- Pair width is bounded by a fixed multiple of its exact balanced square mass. -/
theorem logCellWidth_le_sixteen_haarMass {a : ℕ} (ha : 1 ≤ a) :
    logCellWidth a ≤ 16 * haarMass a := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one haR
  calc
    _ ≤ 1 / (a : ℝ) := logCellWidth_le_inv ha
    _ ≤ 16 * (1 / (4 * (a : ℝ) + 3)) := by
      rw [mul_one_div, div_le_div_iff₀ ha0 (by positivity)]
      linarith only [haR]
    _ ≤ _ := mul_le_mul_of_nonneg_left (haarMass_bounds ha).1 (by norm_num)

/-- Apart from null endpoints, every detail lies in one of its own open pair intervals. -/
theorem haarSectionProfile_zero_ae_pair_exterior (d : ℕ → ℝ) (X : ℕ) :
    ∀ᵐ x ∂volume, (∀ i : Finset.Icc 1 X,
      x ∉ Ioo (Real.log ((2 * (i : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ))) → haarSectionProfile d X x = 0 := by
  have hne : ∀ᵐ x ∂volume, ∀ a : ℕ, x ≠ Real.log ((2 * a : ℕ) : ℝ) :=
    ae_all_iff.mpr fun a => Measure.ae_ne volume _
  filter_upwards [hne] with x hx
  intro hout
  unfold haarSectionProfile
  apply Finset.sum_eq_zero
  intro a ha
  rw [haarProfile_zero_outside_pair (Finset.mem_Icc.mp ha).1, mul_zero]
  intro hi
  exact hout ⟨a, ha⟩ ⟨lt_of_le_of_ne hi.1 (Ne.symm (hx a)), hi.2⟩

/-- Exact symmetric integral representation of the complete-cell polarization. -/
theorem completeGammaMixed_eq_integral (q d : ℕ → ℝ) (X : ℕ) :
    completeGammaMixed q d X =
      ∫ p : ℝ × ℝ,
        (averageSectionProfile q X p.1 - averageSectionProfile q X p.2) *
          (haarSectionProfile d X p.1 - haarSectionProfile d X p.2) ∂gammaKernelMeasure :=
  (integral_gammaKernel_mixed (averageSectionProfile_bv q X) (haarSectionProfile_bv d X)
    (averageSectionProfile_compact q X) (haarSectionProfile_compact d X)).symm

/-- The full coarse/detail Gamma interaction is lower order in the detail variable. -/
theorem completeGammaMixed_sq_le (q d : ℕ → ℝ) (X : ℕ) :
    completeGammaMixed q d X ^ 2 ≤
      128 * Real.exp (1 / 2) * levyEnergy (averageSectionProfile q X) *
        ∫ x, haarSectionProfile d X x ^ 2 := by
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hab (i : S) : L i < U i := by
    apply sub_pos.mp
    rw [hwidth]
    exact logCellWidth_pos (hpos i)
  have hw (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    have hi := hpos i
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by positivity : (0 : ℝ) < (i : ℕ))).mpr (by exact_mod_cast hpos i))
  have hd : Pairwise (Function.onFun Disjoint (fun i : S => Ioo (L i) (U i))) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun he => hij (Subtype.ext he)
    apply disjoint_left.mpr
    intro x hi hj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have he : U i ≤ L j := Real.log_le_log (by have := hpos i; positivity)
        (by exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega))
      exact (not_lt_of_ge he) (hj.1.trans hi.2)
    · have he : U j ≤ L i := Real.log_le_log (by have := hpos j; positivity)
        (by exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega))
      exact (not_lt_of_ge he) (hi.1.trans hj.2)
  have hb (i : S) (x : ℝ) (hx : x ∈ Ioo (L i) (U i)) :
      haarSectionProfile d X x ^ 2 ≤ d i ^ 2 := by
    rw [haarSectionProfile_on_pair d (hpos i) (Finset.mem_Icc.mp i.property).2 hx, mul_pow]
    have hs : haarProfile i x ^ 2 ≤ 1 := by
      have ha := abs_haarProfile_le_one (hpos i) x
      have hm := mul_nonneg (sub_nonneg.mpr ha)
        (show 0 ≤ 1 + |haarProfile i x| by positivity)
      nlinarith only [hm, sq_abs (haarProfile i x)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (sq_nonneg (d i))
  have he := gamma_mixed_sq_le_interval_mass L U (fun i : S => q i) (fun i : S => d i ^ 2)
    (averageSectionProfile q X) (haarSectionProfile d X) hab hw hd
    (averageSectionProfile_bv q X) (haarSectionProfile_bv d X)
    (averageSectionProfile_compact q X) (haarSectionProfile_compact d X)
    (fun i _ hx => averageSectionProfile_eq_on_pair q (hpos i)
      (Finset.mem_Icc.mp i.property).2 hx)
    (fun i => setIntegral_haarSectionProfile_pair d (hpos i) (Finset.mem_Icc.mp i.property).2)
    (haarSectionProfile_zero_ae_pair_exterior d X) (fun i => sq_nonneg (d i)) hb
  have hmass : (∑ i : S, (U i - L i) * d i ^ 2) ≤
      16 * ∫ x, haarSectionProfile d X x ^ 2 := by
    rw [integral_haarSectionProfile_sq]
    conv_rhs => rw [← Finset.sum_coe_sort (Finset.Icc 1 X) (fun a => haarMass a * d a ^ 2)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hwidth]
    calc
      _ ≤ (16 * haarMass i) * d i ^ 2 :=
        mul_le_mul_of_nonneg_right (logCellWidth_le_sixteen_haarMass (hpos i)) (sq_nonneg _)
      _ = _ := by ring
  have hΓ : 0 ≤ levyEnergy (averageSectionProfile q X) := by
    rw [← norm_levyVector_sq _ (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)]
    exact sq_nonneg _
  refine he.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq ?_)
  ring

/-- Subtraction of detail coefficients is exact in the original Gamma polarization. -/
theorem completeGammaMixed_sub (q d e : ℕ → ℝ) (X : ℕ) :
    completeGammaMixed q (fun a => d a - e a) X =
      completeGammaMixed q d X - completeGammaMixed q e X := by
  have hp : haarSectionProfile (fun a => d a - e a) X =
      fun x => haarSectionProfile d X x - haarSectionProfile e X x := by
    funext x
    simp only [haarSectionProfile, sub_mul, Finset.sum_sub_distrib]
  rw [completeGammaMixed_eq_integral, completeGammaMixed_eq_integral,
    completeGammaMixed_eq_integral, hp]
  have hiD := integrable_gammaKernel_mixed (averageSectionProfile_bv q X)
    (haarSectionProfile_bv d X) (averageSectionProfile_compact q X) (haarSectionProfile_compact d X)
  have hiE := integrable_gammaKernel_mixed (averageSectionProfile_bv q X)
    (haarSectionProfile_bv e X) (averageSectionProfile_compact q X) (haarSectionProfile_compact e X)
  rw [← integral_sub hiD hiE]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
