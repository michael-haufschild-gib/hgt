import GaloisForLFunctions.ArithmeticIndexDescent.EveryEvenPrimeLagHasGammaSmallMixedTails
import GaloisForLFunctions.ArithmeticIndexDescent.GammaBoundedCompleteProfilesHaveCompactDetails
import GaloisForLFunctions.HTGeometry.PaperHalfLineCalkin

/-!
# Gamma-small mixed tails at every integer prime lag

Odd-boundary incidence sends detail indices only upward. A translated high
detail therefore pairs with the high target detail alone. Shift contractivity
and original pair variance pay this correction to the full-profile pairing.
The resulting estimate keeps every coarse coefficient and every cell horizon.
-/

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Restriction after full-line translation cannot increase the actual half-line norm. -/
theorem norm_halfLineRightShift_le (t : ℝ) (f : Lp ℂ 2 halfLineMeasure) :
    ‖halfLineRightShift t f‖ ≤ ‖f‖ := by
  unfold halfLineRightShift
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  calc
    _ ≤ ‖halfLineRestrict‖ * ‖(Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - t)
        (measurePreserving_sub_right volume t)) (halfLineExtend f)‖ :=
      halfLineRestrict.le_opNorm _
    _ ≤ 1 * ‖(Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - t)
        (measurePreserving_sub_right volume t)) (halfLineExtend f)‖ :=
      mul_le_mul_of_nonneg_right norm_halfLineRestrict_le_one (norm_nonneg _)
    _ = ‖f‖ := by
      rw [one_mul, LinearIsometry.norm_map]
      exact norm_halfLineExtendLM f

/-- A high-detail input cannot read a low target detail under integer translation. -/
theorem inner_shift_haar_tail_eq_tail (d : ℕ → ℝ) (A X : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m)
        (haarSection (fun a => if A ≤ a then d a else 0) X)) (haarSection d X)).re =
      (inner ℂ (halfLineRightShift (Real.log m)
        (haarSection (fun a => if A ≤ a then d a else 0) X))
          (haarSection (fun a => if A ≤ a then d a else 0) X)).re := by
  rw [inner_shift_haarSection _ d X hm, inner_shift_haarSection _ _ X hm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hAa : A ≤ a
  · simp only [if_pos hAa]
    by_cases he : (2 * a + 1) * m = 2 * b + 1
    · have hab : a ≤ b := by
        have h := Nat.mul_le_mul_left (2 * a + 1) (show 1 ≤ m by omega)
        rw [Nat.mul_one, he] at h
        omega
      rw [if_pos (hAa.trans hab)]
    · simp only [if_neg he, mul_zero]
  · simp only [if_neg hAa, zero_mul]

/-- Odd-lag detail corrections are paid in the same untruncated Gamma profile. -/
theorem cellGammaWeight_mul_abs_haar_tail_pair_le_gamma (q d : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (X : ℕ) :
    cellGammaWeight A * |(inner ℂ (halfLineRightShift (Real.log m)
      (haarSection (fun a => if A ≤ a then d a else 0) X)) (haarSection d X)).re| ≤
        levyEnergy (completePairProfile q d X) := by
  rw [inner_shift_haar_tail_eq_tail d A X hm]
  let v := haarSection (fun a => if A ≤ a then d a else 0) X
  have hnorm : |(inner ℂ (halfLineRightShift (Real.log m) v) v).re| ≤ ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖inner ℂ (halfLineRightShift (Real.log m) v) v‖ := Complex.abs_re_le_norm _
      _ ≤ ‖halfLineRightShift (Real.log m) v‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right (norm_halfLineRightShift_le _ v) (norm_nonneg _)
      _ = _ := (pow_two _).symm
  have hmass : ‖v‖ ^ 2 = ∑ a ∈ Icc 1 X, haarMass a * (if A ≤ a then d a else 0) ^ 2 := by
    have hn : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq _
    exact hn.symm.trans (re_inner_haarSection_self (fun a => if A ≤ a then d a else 0) X)
  exact (mul_le_mul_of_nonneg_left (hnorm.trans_eq hmass) (cellGammaWeight_pos hA).le).trans
    (cellGammaWeight_mul_haar_tail_mass_le_gamma q d hA X)

/-- At every integer lag the mixed term is a full-profile probe minus its exact detail correction. -/
theorem integerMixedSource_eq_fullProfile_sub_detail (c q d : ℕ → ℝ) (X : ℕ)
    {m : ℕ} (hm : 2 ≤ m) :
    integerMixedSource m c q X X = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
      ((∫ u, haarSectionProfile c X u * completePairProfile q d X (u + Real.log m)) -
        (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection d X)).re) := by
  have hzero := inner_shift_coarseSection_haarSection q c X X hm
  have hfull := inner_shift_haar_completePair_profiles c q d X X (Real.log m)
  rw [inner_add_right, Complex.add_re] at hfull
  rw [integerMixedSource, hzero, add_zero, ← hfull]
  ring

/-- Every integer prime lag has an inverse-capacity mixed tail bound in the original Gamma energy. -/
theorem cellGammaWeight_mul_abs_integerMixed_tail_le (d q : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (X : ℕ) :
    cellGammaWeight A * |integerMixedSource m (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m)) *
        levyEnergy (completePairProfile q d X) := by
  have hw : 0 ≤ 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m :=
    div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  have hprobe := cellGammaWeight_mul_abs_translated_detail_le_gamma q d hA (le_refl X) (-Real.log m)
  simp only [sub_neg_eq_add] at hprobe
  have hdetail := cellGammaWeight_mul_abs_haar_tail_pair_le_gamma q d hA hm X
  rw [integerMixedSource_eq_fullProfile_sub_detail _ q d X hm, abs_mul, abs_of_nonneg hw]
  have htri := mul_le_mul_of_nonneg_left
    (abs_sub (∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) X u *
      completePairProfile q d X (u + Real.log m))
      (inner ℂ (halfLineRightShift (Real.log m)
        (haarSection (fun a => if A ≤ a then d a else 0) X)) (haarSection d X)).re)
    (cellGammaWeight_pos hA).le
  have hsum : cellGammaWeight A *
      |(∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) X u *
        completePairProfile q d X (u + Real.log m)) -
        (inner ℂ (halfLineRightShift (Real.log m)
          (haarSection (fun a => if A ≤ a then d a else 0) X)) (haarSection d X)).re| ≤
      2 * levyEnergy (completePairProfile q d X) := by
    linarith only [htri, hprobe, hdetail]
  calc
    _ = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
      (cellGammaWeight A * |(∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) X u *
        completePairProfile q d X (u + Real.log m)) -
        (inner ℂ (halfLineRightShift (Real.log m)
          (haarSection (fun a => if A ≤ a then d a else 0) X)) (haarSection d X)).re|) := by ring
    _ ≤ (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        (2 * levyEnergy (completePairProfile q d X)) := mul_le_mul_of_nonneg_left hsum hw
    _ = _ := by ring

/-- Quantitative payment ready for summing a complete fixed Euler factor. -/
theorem abs_integerMixed_tail_le_gamma_div_weight (d q : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (X : ℕ) :
    |integerMixedSource m (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m)) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (cellGammaWeight_pos hA)).mpr
  simpa only [mul_comm] using cellGammaWeight_mul_abs_integerMixed_tail_le d q hA hm X

/-- The positive first-cell weight pays the entire mixed term at every integer prime lag. -/
theorem abs_integerMixed_le_gamma (d q : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) (X : ℕ) :
    |integerMixedSource m d q X X| ≤ (2 * (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m)) *
      (levyEnergy (completePairProfile q d X) / cellGammaWeight 1) := by
  have h := abs_integerMixed_tail_le_gamma_div_weight d q (le_refl 1) hm X
  have hc : haarSection (fun a => if 1 ≤ a then d a else 0) X = haarSection d X := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos (mem_Icc.mp ha).1]
  simpa only [integerMixedSource, hc] using h

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.inner_shift_haar_tail_eq_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_abs_haar_tail_pair_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integerMixedSource_eq_fullProfile_sub_detail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_integerMixed_tail_le_gamma_div_weight
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_integerMixed_le_gamma
