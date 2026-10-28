import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms
import GaloisForLFunctions.HTGeometry.DyadicLatticeCover

/-!
# Uniform Gamma payment for translated detail probes

A balanced cell reads only the variance of the profile paired with it.
Integral Young payment and the logarithmic Gamma charge on disjoint pairs
bound the whole high-detail probe. Translation preserves the original
Gamma energy, so the same bound holds at every real lag. The exact
reciprocal-width weight is positive even on the first pair.
-/

noncomputable section

open MeasureTheory Set Filter
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells ArithmeticCastelnuovoSeveri.IntervalVariance
open BiarithmeticGaugeGeometry HTGeometry

private theorem two_abs_integral_mul_le_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    2 * |∫ x, u x * v x ∂μ| ≤ (∫ x, u x ^ 2 ∂μ) + ∫ x, v x ^ 2 ∂μ := by
  have huv : Integrable (fun x => u x * v x) μ := hu.integrable_mul hv
  have hm : (∫ x, (u x - v x) ^ 2 ∂μ) =
      ((∫ x, u x ^ 2 ∂μ) - 2 * ∫ x, u x * v x ∂μ) + ∫ x, v x ^ 2 ∂μ := by
    have he : (fun x => (u x - v x) ^ 2) = fun x => (u x ^ 2 - 2 * (u x * v x)) + v x ^ 2 := by
      funext x; ring
    have hi : Integrable (fun x => u x ^ 2 - 2 * (u x * v x)) μ :=
      hu.integrable_sq.sub (huv.const_mul 2)
    rw [he, integral_add hi hv.integrable_sq,
      integral_sub hu.integrable_sq (huv.const_mul 2), integral_const_mul]
  have hp : (∫ x, (u x + v x) ^ 2 ∂μ) =
      ((∫ x, u x ^ 2 ∂μ) + 2 * ∫ x, u x * v x ∂μ) + ∫ x, v x ^ 2 ∂μ := by
    have he : (fun x => (u x + v x) ^ 2) = fun x => (u x ^ 2 + 2 * (u x * v x)) + v x ^ 2 := by
      funext x; ring
    have hi : Integrable (fun x => u x ^ 2 + 2 * (u x * v x)) μ :=
      hu.integrable_sq.add (huv.const_mul 2)
    rw [he, integral_add hi hv.integrable_sq,
      integral_add hu.integrable_sq (huv.const_mul 2), integral_const_mul]
  have hm0 : 0 ≤ ∫ x, (u x - v x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hp0 : 0 ≤ ∫ x, (u x + v x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [hm] at hm0
  rw [hp] at hp0
  by_cases hi : 0 ≤ ∫ x, u x * v x ∂μ
  · rw [abs_of_nonneg hi]
    linarith only [hm0]
  · rw [abs_of_neg (lt_of_not_ge hi)]
    linarith only [hp0]

private theorem integral_haar_mul_eq_pair {a : ℕ} (ha : 1 ≤ a) (g : ℝ → ℝ) :
    (∫ x, haarProfile a x * g x) =
      ∫ x in Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
        haarProfile a x * g x := by
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (Real.log ((2 * a : ℕ) : ℝ))] with x hx
  by_cases hm : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
  · exact (indicator_of_mem hm (fun x => haarProfile a x * g x)).symm
  · rw [indicator_of_notMem hm]
    have hz : haarProfile a x = 0 := by
      apply haarProfile_zero_outside_pair ha
      intro hi
      apply hm
      refine ⟨?_, hi.2⟩
      rcases lt_or_eq_of_le hi.1 with hl | he
      · exact hl
      · exact False.elim (hx he.symm)
    rw [hz, zero_mul]

/-- A literal balanced cell reads only the actual local variance of its second profile. -/
theorem two_abs_haarProbe_le_variance {a : ℕ} (ha : 1 ≤ a) (d : ℝ)
    {g : ℝ → ℝ} (hg : MemLp g 2 volume) :
    2 * |d * ∫ x, haarProfile a x * g x| ≤ haarMass a * d ^ 2 +
      intervalVariance (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) g := by
  let L := Real.log ((2 * a : ℕ) : ℝ)
  let U := Real.log ((2 * a + 2 : ℕ) : ℝ)
  let t := intervalMean L U g
  have hh : MemLp (haarProfile a) 2 (volume.restrict (Ioo L U)) :=
    (memLp_compact_bv (haarProfile_bv a) (haarProfile_compact a)).mono_measure Measure.restrict_le_self
  have hgi : MemLp g 2 (volume.restrict (Ioo L U)) := hg.mono_measure Measure.restrict_le_self
  have hu : MemLp (fun x => d * haarProfile a x) 2 (volume.restrict (Ioo L U)) := hh.const_mul d
  have hv : MemLp (fun x => g x - t) 2 (volume.restrict (Ioo L U)) := hgi.sub (memLp_const t)
  have hprod : IntegrableOn (fun x => haarProfile a x * g x) (Ioo L U) := hh.integrable_mul hgi
  have hhi : IntegrableOn (haarProfile a) (Ioo L U) := hh.integrable one_le_two
  have hcenter : (∫ x in Ioo L U, haarProfile a x * (g x - t)) =
      ∫ x, haarProfile a x * g x := by
    simp_rw [mul_sub]
    rw [integral_sub hprod (hhi.mul_const t), integral_mul_const,
      setIntegral_haarProfile_pair ha, zero_mul, sub_zero, integral_haar_mul_eq_pair ha g]
  have hsquare : (∫ x in Ioo L U, (d * haarProfile a x) ^ 2) = haarMass a * d ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, setIntegral_haarProfile_pair_sq ha, mul_comm]
  have h := two_abs_integral_mul_le_sq hu hv
  rw [show (fun x => (d * haarProfile a x) * (g x - t)) =
      fun x => d * (haarProfile a x * (g x - t)) by funext x; ring,
    integral_const_mul, hcenter, hsquare] at h
  exact h

/-- The exact logarithmic variance weight of a complete cell pair. -/
def cellGammaWeight (a : ℕ) : ℝ := Real.log (1 / logCellWidth a)

theorem logCellWidth_le_of_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logCellWidth b ≤ logCellWidth a := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  unfold logCellWidth
  rw [← Real.log_div (by positivity : (b : ℝ) + 1 ≠ 0) hb0.ne',
    ← Real.log_div (by positivity : (a : ℝ) + 1 ≠ 0) ha0.ne']
  apply Real.log_le_log (by positivity)
  rw [add_div, add_div, div_self hb0.ne', div_self ha0.ne']
  exact add_le_add (le_refl _) (one_div_le_one_div_of_le ha0 (by exact_mod_cast hab))

theorem cellGammaWeight_pos {a : ℕ} (ha : 1 ≤ a) : 0 < cellGammaWeight a := by
  have hw : logCellWidth a < 1 := by
    calc
      _ ≤ logCellWidth 1 := logCellWidth_le_of_le (le_refl 1) ha
      _ = Real.log 2 := by norm_num only [logCellWidth, Nat.cast_one, Real.log_one, sub_zero]
      _ < 1 := HTGeometry.log_two_lt_one
  apply Real.log_pos
  apply (lt_div_iff₀ (logCellWidth_pos ha)).mpr
  simpa only [one_mul] using hw

theorem cellGammaWeight_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    cellGammaWeight a ≤ cellGammaWeight b := by
  have hb : 1 ≤ b := ha.trans hab
  apply Real.log_le_log (div_pos zero_lt_one (logCellWidth_pos ha))
  exact one_div_le_one_div_of_le (logCellWidth_pos hb) (logCellWidth_le_of_le ha hab)

theorem log_le_cellGammaWeight {a : ℕ} (ha : 1 ≤ a) :
    Real.log (a : ℝ) ≤ cellGammaWeight a := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  apply Real.log_le_log ha0
  apply (le_div_iff₀ (logCellWidth_pos ha)).mpr
  have h := mul_le_mul_of_nonneg_left (logCellWidth_le_inv ha) ha0.le
  simpa only [mul_one_div_cancel ha0.ne'] using h

/-- Gamma pays the exact reciprocal-width variance weight on every original pair. -/
theorem sum_cellGammaWeight_variance_le_gamma {g : ℝ → ℝ}
    (hg : BoundedVariationOn g univ) (hgc : HasCompactSupport g) (Y : ℕ) :
    (∑ a ∈ Finset.Icc 1 Y, cellGammaWeight a *
      intervalVariance (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) g) ≤
        levyEnergy g := by
  let S := Finset.Icc 1 Y
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hw0 (i : S) : 0 < U i - L i := by rw [hwidth]; exact logCellWidth_pos (hpos i)
  have hwidth1 (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))).mpr
        (by exact_mod_cast hpos i))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      apply Real.log_le_log (by have := hpos i; positivity)
      exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)
    · right
      apply Real.log_le_log (by have := hpos j; positivity)
      exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)
  have h := levyEnergy_ge_sum_log_variance L U (fun i => sub_pos.mp (hw0 i)) hwidth1 hsep hg hgc
  apply le_trans ?_ h
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro i _hi
  rw [cellGammaWeight, hwidth]

theorem sum_log_pair_variance_le_gamma {g : ℝ → ℝ}
    (hg : BoundedVariationOn g univ) (hgc : HasCompactSupport g) (Y : ℕ) :
    (∑ a ∈ Finset.Icc 1 Y, Real.log (a : ℝ) *
      intervalVariance (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) g) ≤
        levyEnergy g := by
  apply le_trans ?_ (sum_cellGammaWeight_variance_le_gamma hg hgc Y)
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_right (log_le_cellGammaWeight (Finset.mem_Icc.mp ha).1)
    (intervalVariance_nonneg _ _ _)

/-- The actual high-detail probe is paid by its logarithmic mass and the other profile's Gamma energy. -/
theorem two_cellGammaWeight_mul_abs_haar_tail_le (d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (Y : ℕ)
    {g : ℝ → ℝ} (hg : BoundedVariationOn g univ) (hgc : HasCompactSupport g) :
    2 * cellGammaWeight A *
        |∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) Y x * g x| ≤
      (∑ a ∈ Finset.Icc 1 Y, cellGammaWeight a * haarMass a * d a ^ 2) + levyEnergy g := by
  let c : ℕ → ℝ := fun a => if A ≤ a then d a else 0
  let V : ℕ → ℝ := fun a =>
    intervalVariance (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) g
  have hgm := memLp_compact_bv hg hgc
  have hweightA := (cellGammaWeight_pos hA).le
  have hlocal (a : ℕ) (ha : 1 ≤ a) :
      2 * cellGammaWeight A * |c a * ∫ x, haarProfile a x * g x| ≤
        cellGammaWeight a * haarMass a * d a ^ 2 + cellGammaWeight a * V a := by
    have hwa := (cellGammaWeight_pos ha).le
    by_cases hAa : A ≤ a
    · have hl := cellGammaWeight_mono hA hAa
      have hp := mul_le_mul_of_nonneg_left (two_abs_haarProbe_le_variance ha (d a) hgm) hwa
      simp only [c, if_pos hAa]
      have hcomp := mul_le_mul_of_nonneg_right hl
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (d a * ∫ x, haarProfile a x * g x)))
      dsimp only [V] at *
      linarith only [hp, hcomp]
    · simp only [c, if_neg hAa, zero_mul, abs_zero, mul_zero]
      exact add_nonneg (mul_nonneg (mul_nonneg hwa (haarMass_pos ha).le) (sq_nonneg _))
        (mul_nonneg hwa (intervalVariance_nonneg _ _ _))
  have hcorr : (∫ x, haarSectionProfile c Y x * g x) =
      ∑ a ∈ Finset.Icc 1 Y, c a * ∫ x, haarProfile a x * g x := by
    have hi (a : ℕ) : Integrable (fun x => c a * (haarProfile a x * g x)) := by
      have hprod : Integrable (fun x => haarProfile a x * g x) :=
        (memLp_compact_bv (haarProfile_bv a) (haarProfile_compact a)).integrable_mul hgm
      exact hprod.const_mul (c a)
    simp only [haarSectionProfile, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun a _ => hi a)]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [integral_const_mul]
  change 2 * cellGammaWeight A * |∫ x, haarSectionProfile c Y x * g x| ≤ _
  rw [hcorr]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hweightA)).trans
  calc
    _ = ∑ a ∈ Finset.Icc 1 Y, 2 * cellGammaWeight A * |c a * ∫ x, haarProfile a x * g x| :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 Y,
        (cellGammaWeight a * haarMass a * d a ^ 2 + cellGammaWeight a * V a) :=
      Finset.sum_le_sum fun a ha => hlocal a (Finset.mem_Icc.mp ha).1
    _ = (∑ a ∈ Finset.Icc 1 Y, cellGammaWeight a * haarMass a * d a ^ 2) +
        ∑ a ∈ Finset.Icc 1 Y, cellGammaWeight a * V a := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_refl _) (sum_cellGammaWeight_variance_le_gamma hg hgc Y)

private theorem bv_translate {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (t : ℝ) :
    BoundedVariationOn (fun x => f (x - t)) univ :=
  ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f (fun x => x - t)
    (fun _ _ _ _ h => sub_le_sub_right h t) (fun _ _ => mem_univ _))

/-- Every real translation obeys the same exact cell-capacity bound, including the first detail. -/
theorem cellGammaWeight_mul_abs_translated_detail_le_gamma (q d : ℕ → ℝ) {A Y X : ℕ}
    (hA : 1 ≤ A) (hYX : Y ≤ X) (t : ℝ) :
    cellGammaWeight A *
        |∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) Y u *
          completePairProfile q d X (u - t)| ≤ levyEnergy (completePairProfile q d X) := by
  have hv := bv_translate (completePairProfile_bv q d X) t
  have hc : HasCompactSupport (fun u => completePairProfile q d X (u - t)) :=
    (completePairProfile_compact q d X).comp_homeomorph (Homeomorph.subRight t)
  have h := two_cellGammaWeight_mul_abs_haar_tail_le d hA Y hv hc
  rw [SpacingScaleHarmonicAnalysis.levyEnergy_translate t] at h
  have hd : (∑ a ∈ Finset.Icc 1 Y, cellGammaWeight a * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
    apply le_trans ?_ (sum_cellGammaWeight_variance_le_gamma
      (completePairProfile_bv q d X) (completePairProfile_compact q d X) Y)
    apply Finset.sum_le_sum
    intro a ha
    rw [intervalVariance_completePairProfile q d (Finset.mem_Icc.mp ha).1
      ((Finset.mem_Icc.mp ha).2.trans hYX)]
    exact le_of_eq (mul_assoc _ _ _)
  linarith only [h, hd]

/-- The exact capacity bound implies inverse-logarithmic decay uniformly over all real lags. -/
theorem log_mul_abs_translated_detail_le_gamma (q d : ℕ → ℝ) {A Y X : ℕ}
    (hA : 1 ≤ A) (hYX : Y ≤ X) (t : ℝ) :
    Real.log (A : ℝ) *
        |∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) Y u *
          completePairProfile q d X (u - t)| ≤ levyEnergy (completePairProfile q d X) :=
  (mul_le_mul_of_nonneg_right (log_le_cellGammaWeight hA) (abs_nonneg _)).trans
    (cellGammaWeight_mul_abs_translated_detail_le_gamma q d hA hYX t)

/-- Positive capacity gives a Gamma form bound even when the cutoff retains every detail. -/
theorem abs_translated_detail_le_gamma_div_weight (q d : ℕ → ℝ) {A Y X : ℕ}
    (hA : 1 ≤ A) (hYX : Y ≤ X) (t : ℝ) :
    |∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) Y u *
        completePairProfile q d X (u - t)| ≤ levyEnergy (completePairProfile q d X) / cellGammaWeight A := by
  apply (le_div_iff₀ (cellGammaWeight_pos hA)).mpr
  simpa only [mul_comm] using cellGammaWeight_mul_abs_translated_detail_le_gamma q d hA hYX t

/-- The entire detail pairing is Gamma-bounded, uniformly in the real translation and horizon. -/
theorem abs_translated_full_detail_le_gamma (q d : ℕ → ℝ) {Y X : ℕ}
    (hYX : Y ≤ X) (t : ℝ) :
    |∫ u, haarSectionProfile d Y u * completePairProfile q d X (u - t)| ≤
      levyEnergy (completePairProfile q d X) / cellGammaWeight 1 := by
  have h := abs_translated_detail_le_gamma_div_weight q d (le_refl 1) hYX t
  have hc : haarSectionProfile (fun a => if 1 ≤ a then d a else 0) Y = haarSectionProfile d Y := by
    funext u
    apply Finset.sum_congr rfl
    intro a ha
    simp only [if_pos (Finset.mem_Icc.mp ha).1]
  rw [hc] at h
  exact h

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.two_abs_haarProbe_le_variance
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sum_log_pair_variance_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_pos
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.two_cellGammaWeight_mul_abs_haar_tail_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_abs_translated_detail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.log_mul_abs_translated_detail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_translated_detail_le_gamma_div_weight
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_translated_full_detail_le_gamma
