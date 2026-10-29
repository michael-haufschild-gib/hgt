import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DisjointStepsHaveLogarithmicGammaCost
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellGammaAccounting
import GaloisForLFunctions.ArithmeticIndexDescent.TranslatedDetailsAreUniformlySmallInGammaEnergy
import GaloisForLFunctions.ArithmeticIndexDescent.OddHigherPrimePowersPayTheirWholeDetailBlock

/-!
# Homogeneous Gamma control of complete-cell averages and details

The Gamma norm on balanced pair details is equivalent to their logarithmically
weighted square mass. Exact variance payment then makes the actual pair-average
and detail projections bounded in the original homogeneous Gamma energy.
No additive square-mass error or support-dependent constant is needed.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open ArithmeticCastelnuovoSeveri.IntervalVariance BiarithmeticGaugeGeometry HTGeometry

/-- A fixed upper cost for either half of any complete logarithmic pair. -/
def haarGammaUpperConstant : ℝ := Real.exp (1 / 2) +
  (Real.exp (1 / 2) * Real.log 4 + 2 * gammaTailMass 1 + Real.exp (1 / 2)) / cellGammaWeight 1

theorem haarGammaUpperConstant_pos : 0 < haarGammaUpperConstant := by
  have hT : 0 ≤ gammaTailMass 1 := gammaTailMass_nonneg (by norm_num)
  have hκ : 0 < cellGammaWeight 1 := cellGammaWeight_pos (le_refl 1)
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold haarGammaUpperConstant
  positivity

private theorem half_cell_log_le {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) (hna : n ≤ 2 * a + 1) :
    Real.log (1 / logCellWidth n) ≤ Real.log 4 + cellGammaWeight a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hna' : (n : ℝ) + 1 ≤ 4 * (a : ℝ) := by exact_mod_cast (show n + 1 ≤ 4 * a by omega)
  have hw : logCellWidth a ≤ 4 * logCellWidth n := by
    calc
      _ ≤ 1 / (a : ℝ) := logCellWidth_le_inv ha
      _ ≤ 4 * (1 / ((n : ℝ) + 1)) := by
        rw [mul_one_div, div_le_div_iff₀ ha0 hn0]
        simpa only [one_mul] using hna'
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_add_one_le_logCellWidth hn) (by norm_num)
  have hlog : Real.log (1 / logCellWidth n) ≤ Real.log (4 / logCellWidth a) := by
    apply Real.log_le_log (div_pos zero_lt_one (logCellWidth_pos hn))
    rw [div_le_div_iff₀ (logCellWidth_pos hn) (logCellWidth_pos ha)]
    simpa only [one_mul] using hw
  have he : Real.log (4 / logCellWidth a) = Real.log 4 + cellGammaWeight a := by
    rw [cellGammaWeight, Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (logCellWidth_pos ha).ne',
      Real.log_div one_ne_zero (logCellWidth_pos ha).ne', Real.log_one]
    ring
  exact hlog.trans_eq he

private theorem raw_half_gamma_le {a n : ℕ} (ha : 1 ≤ a) (hn : 1 ≤ n) (hna : n ≤ 2 * a + 1) :
    levyEnergy (rawCell n) ≤ haarGammaUpperConstant * cellGammaWeight a * logCellWidth n := by
  have hκ := cellGammaWeight_pos (le_refl 1)
  have hκa := cellGammaWeight_mono (le_refl 1) ha
  have hT := gammaTailMass_nonneg (show (0 : ℝ) < 1 by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hnum : 0 ≤ Real.exp (1 / 2) * Real.log 4 + 2 * gammaTailMass 1 + Real.exp (1 / 2) :=
    by positivity
  have hpay : Real.exp (1 / 2) * Real.log 4 + 2 * gammaTailMass 1 + Real.exp (1 / 2) ≤
      ((Real.exp (1 / 2) * Real.log 4 + 2 * gammaTailMass 1 + Real.exp (1 / 2)) /
        cellGammaWeight 1) * cellGammaWeight a := by
    calc
      _ = ((Real.exp (1 / 2) * Real.log 4 + 2 * gammaTailMass 1 + Real.exp (1 / 2)) /
          cellGammaWeight 1) * cellGammaWeight 1 := (div_mul_cancel₀ _ hκ.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hκa (div_nonneg hnum hκ.le)
  have hlog := mul_le_mul_of_nonneg_left (half_cell_log_le ha hn hna) (Real.exp_pos (1 / 2)).le
  have hcost : Real.exp (1 / 2) * Real.log (1 / logCellWidth n) +
      2 * gammaTailMass 1 + Real.exp (1 / 2) ≤ haarGammaUpperConstant * cellGammaWeight a := by
    unfold haarGammaUpperConstant
    nlinarith only [hlog, hpay]
  calc
    _ ≤ logCellWidth n * (Real.exp (1 / 2) * Real.log (1 / logCellWidth n) +
        2 * gammaTailMass 1 + Real.exp (1 / 2)) := rawCell_levyEnergy_le_log hn
    _ ≤ logCellWidth n * (haarGammaUpperConstant * cellGammaWeight a) :=
      mul_le_mul_of_nonneg_left hcost (logCellWidth_pos hn).le
    _ = _ := by ring

/-- The upper Gamma cost of one balanced atom has its exact logarithmic mass scale. -/
theorem haarProfile_gamma_le_weight {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (haarProfile a) ≤ 2 * haarGammaUpperConstant * cellGammaWeight a * haarMass a := by
  have h := levyEnergy_sub_le_two_bv
    (bv_const_mul (haarLeftCoeff a) (rawCell_bv (2 * a)))
    (bv_const_mul (haarRightCoeff a) (rawCell_bv (2 * a + 1)))
    ((rawCell_compact (2 * a)).mul_left) ((rawCell_compact (2 * a + 1)).mul_left)
  change levyEnergy (haarProfile a) ≤ _ at h
  rw [levyEnergy_const_mul, levyEnergy_const_mul] at h
  have hl := mul_le_mul_of_nonneg_left
    (raw_half_gamma_le ha (show 1 ≤ 2 * a by omega) (by omega)) (sq_nonneg (haarLeftCoeff a))
  have hr := mul_le_mul_of_nonneg_left
    (raw_half_gamma_le ha (show 1 ≤ 2 * a + 1 by omega) le_rfl) (sq_nonneg (haarRightCoeff a))
  have hm : haarLeftCoeff a ^ 2 * logCellWidth (2 * a) +
      haarRightCoeff a ^ 2 * logCellWidth (2 * a + 1) = haarMass a := by
    have hl := (haarCoeff_mass a).1
    have hr := (haarCoeff_mass a).2
    have hs := haarCoeff_sum ha
    linear_combination haarLeftCoeff a * hl + haarRightCoeff a * hr + haarMass a * hs
  calc
    _ ≤ 2 * (haarLeftCoeff a ^ 2 * levyEnergy (rawCell (2 * a))) +
        2 * (haarRightCoeff a ^ 2 * levyEnergy (rawCell (2 * a + 1))) := h
    _ ≤ 2 * (haarLeftCoeff a ^ 2 *
        (haarGammaUpperConstant * cellGammaWeight a * logCellWidth (2 * a))) +
        2 * (haarRightCoeff a ^ 2 *
        (haarGammaUpperConstant * cellGammaWeight a * logCellWidth (2 * a + 1))) := by
      linarith only [hl, hr]
    _ = 2 * haarGammaUpperConstant * cellGammaWeight a *
        (haarLeftCoeff a ^ 2 * logCellWidth (2 * a) +
          haarRightCoeff a ^ 2 * logCellWidth (2 * a + 1)) := by ring
    _ = _ := by rw [hm]

private theorem haarProfile_disjoint {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b)
    (x : ℝ) : haarProfile a x = 0 ∨ haarProfile b x = 0 := by
  by_cases hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · right
    apply haarProfile_zero_outside_pair hb
    intro hy
    rcases lt_or_gt_of_ne hab with hab | hba
    · have hsep : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
      linarith only [hx.2, hy.1, hsep]
    · have hsep : Real.log ((2 * b + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b + 2 ≤ 2 * a by omega))
      linarith only [hy.2, hx.1, hsep]
  · exact Or.inl (haarProfile_zero_outside_pair ha hx)

/-- Balanced details have Gamma energy at most a fixed multiple of their weighted square mass. -/
theorem haarSectionProfile_gamma_le_weighted_mass (d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (haarSectionProfile d X) ≤
      (4 * haarGammaUpperConstant) *
        ∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2 := by
  have h := levyEnergy_disjoint_sum_le (Finset.Icc 1 X)
    (fun a x => d a * haarProfile a x)
    (fun a _ => bv_const_mul _ (haarProfile_bv a))
    (fun a _ => (haarProfile_compact a).mul_left)
    (haarSectionProfile_bv d X) (haarSectionProfile_compact d X)
    (fun a ha b hb hab x => (haarProfile_disjoint (Finset.mem_Icc.mp ha).1
      (Finset.mem_Icc.mp hb).1 hab x).elim
        (fun hz => Or.inl (by rw [hz, mul_zero])) (fun hz => Or.inr (by rw [hz, mul_zero])))
  change levyEnergy (haarSectionProfile d X) ≤ _ at h
  simp_rw [levyEnergy_const_mul] at h
  calc
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 X, d a ^ 2 * levyEnergy (haarProfile a) := h
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 X,
        d a ^ 2 * (2 * haarGammaUpperConstant * cellGammaWeight a * haarMass a) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
        (haarProfile_gamma_le_weight (Finset.mem_Icc.mp ha).1) (sq_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Exact reciprocal-width detail mass is paid even in the presence of arbitrary averages. -/
theorem completePairProfile_gamma_ge_weighted_detail (q d : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
  apply le_trans ?_ (sum_cellGammaWeight_variance_le_gamma
    (completePairProfile_bv q d X) (completePairProfile_compact q d X) X)
  apply Finset.sum_le_sum
  intro a ha
  rw [intervalVariance_completePairProfile q d (Finset.mem_Icc.mp ha).1
    (Finset.mem_Icc.mp ha).2, mul_assoc]

/-- The full source pays the Gamma energy of its actual detail projection. -/
theorem completePairProfile_gamma_pays_detail (q d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (haarSectionProfile d X) ≤
      (4 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X) := by
  exact (haarSectionProfile_gamma_le_weighted_mass d X).trans
    (mul_le_mul_of_nonneg_left (completePairProfile_gamma_ge_weighted_detail q d X)
      (mul_nonneg (by norm_num) haarGammaUpperConstant_pos.le))

/-- Pair averages and balanced details are simultaneously bounded in homogeneous Gamma energy. -/
theorem completePairProfile_gamma_pays_coarse_and_detail (q d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile q X) + levyEnergy (haarSectionProfile d X) ≤
      (2 + 12 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X) := by
  have hd := completePairProfile_gamma_pays_detail q d X
  have hg := levyEnergy_sub_le_two_bv (completePairProfile_bv q d X)
    (haarSectionProfile_bv d X) (completePairProfile_compact q d X) (haarSectionProfile_compact d X)
  have he : (fun x => completePairProfile q d X x - haarSectionProfile d X x) =
      averageSectionProfile q X := by
    funext x
    exact add_sub_cancel_right _ _
  rw [he] at hg
  nlinarith only [hd, hg]

/-- A single horizon-independent constant controls both source projections with no mass correction. -/
theorem exists_uniform_homogeneous_gamma_coarse_detail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      levyEnergy (averageSectionProfile q X) + levyEnergy (haarSectionProfile d X) ≤
        C * levyEnergy (completePairProfile q d X) := by
  refine ⟨2 + 12 * haarGammaUpperConstant, ?_, completePairProfile_gamma_pays_coarse_and_detail⟩
  have h := haarGammaUpperConstant_pos
  positivity

/-- Coarse Gamma energy plus weighted detail mass is an equivalent homogeneous energy. -/
theorem completePairProfile_gamma_equivalent_coarse_weighted_detail (q d : ℕ → ℝ) (X : ℕ) :
    (levyEnergy (averageSectionProfile q X) +
      (∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2) ≤
        (3 + 12 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X)) ∧
    (levyEnergy (completePairProfile q d X) ≤ 2 * levyEnergy (averageSectionProfile q X) +
      (8 * haarGammaUpperConstant) *
        ∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2) := by
  constructor
  · have hp := completePairProfile_gamma_pays_coarse_and_detail q d X
    have hm := completePairProfile_gamma_ge_weighted_detail q d X
    have hd := levyEnergy_nonneg_bv (haarSectionProfile_bv d X) (haarSectionProfile_compact d X)
    nlinarith only [hp, hm, hd]
  · have ht := levyEnergy_sub_le_two_bv (averageSectionProfile_bv q X)
      (bv_const_mul (-1) (haarSectionProfile_bv d X))
      (averageSectionProfile_compact q X) ((haarSectionProfile_compact d X).mul_left)
    have he : (fun x => averageSectionProfile q X x - (-1) * haarSectionProfile d X x) =
        completePairProfile q d X := by
      funext x
      simp only [completePairProfile, neg_one_mul, sub_neg_eq_add]
    rw [he, levyEnergy_const_mul] at ht
    norm_num only [neg_one_sq, one_mul] at ht
    have hd := haarSectionProfile_gamma_le_weighted_mass d X
    nlinarith only [ht, hd]

/-- After a fixed detail head, the paid higher-power source retains coarse Gamma and detail mass. -/
theorem exists_squareOddHigherRefinement_coarse_detail_reserve :
    ∃ η : ℝ, 0 < η ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      η * (levyEnergy (averageSectionProfile q X) +
          ∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2) +
        (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, completePairProfile q d X x ^ 2) ≤
          squareOddHigherRefinementSourceForm q d X +
            (1 / 2 : ℝ) * (∫ x : ℝ, completePairProfile q d X x) ^ 2 := by
  obtain ⟨δ, hδ, hsquare⟩ := exists_squarePrime_retained_gamma_complete
  obtain ⟨A, hA, hodd⟩ := exists_oddHigherPrimePower_joint_gamma_small_tail
    (show 0 < δ / 2 by positivity)
  have hK : 0 < 3 + 12 * haarGammaUpperConstant := by
    have h := haarGammaUpperConstant_pos
    positivity
  refine ⟨(δ / 2) / (3 + 12 * haarGammaUpperConstant), div_pos (by positivity) hK, A, hA, ?_⟩
  intro q d X hd
  have htail : (fun a => if A ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : A ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd a (by omega)]
  have ho := hodd q d X
  rw [htail] at ho
  have hp := hsquare q d X
  have hs := le_abs_self
    (oddHigherPrimePowerPairing (haarSection d X) (coarseSection q X + haarSection d X))
  have hg := mul_le_mul_of_nonneg_left
    (completePairProfile_gamma_equivalent_coarse_weighted_detail q d X).1
    (div_nonneg (by positivity : 0 ≤ δ / 2) hK.le)
  rw [← mul_assoc, div_mul_cancel₀ _ hK.ne'] at hg
  unfold squareOddHigherRefinementSourceForm
  rw [oddHigherPrimePowerSource_sub_coarse]
  linarith only [ho, hp, hs, hg]

end GaloisForLFunctions.ArithmeticIndexDescent
