import GaloisForLFunctions.ArithmeticIndexDescent.TheCoarseDetailPrimePairIsTheLiteralSource
import GaloisForLFunctions.ArithmeticIndexDescent.TranslatedDetailsAreUniformlySmallInGammaEnergy

/-!
# The original mixed source at every even integer lag

Even integer translation sends each balanced detail into the pair-average
space. Its pairing with every target detail vanishes by parity of the cell
boundaries. The surviving mixed source therefore pairs the translated detail
with the full original profile, whose Gamma energy pays it uniformly.
-/

noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Both original mixed prime orientations, with their literal arithmetic coefficient. -/
def integerMixedSource (m : ℕ) (d q : ℕ → ℝ) (Y X : ℕ) : ℝ :=
  (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    ((inner ℂ (halfLineRightShift (Real.log m) (haarSection d Y)) (coarseSection q X)).re +
      (inner ℂ (halfLineRightShift (Real.log m) (coarseSection q X)) (haarSection d Y)).re)

theorem integerMixedSource_two (d q : ℕ → ℝ) (Y X : ℕ) :
    integerMixedSource 2 d q Y X = primeTwoMixedSource d q Y X := by
  simp only [integerMixedSource, primeTwoMixedSource, Nat.cast_ofNat]

/-- The mixed integer-lag source is exactly the two original physical correlations. -/
theorem integerMixedSource_eq_integrals (m : ℕ) (d q : ℕ → ℝ) (Y X : ℕ) :
    integerMixedSource m d q Y X = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
      ((∫ u, haarSectionProfile d Y u * averageSectionProfile q X (u + Real.log m)) +
        ∫ u, averageSectionProfile q X u * haarSectionProfile d Y (u + Real.log m)) := by
  rw [integerMixedSource, inner_shift_haar_coarse_profiles, inner_shift_coarse_haar_profiles]

/-- The literal mixed source is additive in its detail coefficients at every horizon. -/
theorem integerMixedSource_add_details (m : ℕ) (d e q : ℕ → ℝ) (Y X : ℕ) :
    integerMixedSource m (fun a => d a + e a) q Y X =
      integerMixedSource m d q Y X + integerMixedSource m e q Y X := by
  have hc : haarSection (fun a => d a + e a) Y = haarSection d Y + haarSection e Y := by
    simp only [haarSection, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  rw [integerMixedSource, hc, map_add, inner_add_left, inner_add_right]
  simp only [Complex.add_re, integerMixedSource]
  ring

/-- Removing the finite detail head leaves exactly the actual high-detail mixed source. -/
theorem integerMixedSource_sub_head (m : ℕ) (d q : ℕ → ℝ) (A Y X : ℕ) :
    integerMixedSource m d q Y X -
      integerMixedSource m (fun a => if a < A then d a else 0) q Y X =
        integerMixedSource m (fun a => if A ≤ a then d a else 0) q Y X := by
  have hd : (fun a => (if a < A then d a else 0) + (if A ≤ a then d a else 0)) = d := by
    funext a
    by_cases h : a < A
    · simp only [if_pos h, if_neg (by omega : ¬A ≤ a), add_zero]
    · simp only [if_neg h, if_pos (by omega : A ≤ a), zero_add]
  have h := integerMixedSource_add_details m
    (fun a => if a < A then d a else 0) (fun a => if A ≤ a then d a else 0) q Y X
  rw [hd] at h
  linarith only [h]

/-- An even translated middle boundary cannot coincide with an odd target detail boundary. -/
theorem inner_shift_haarSection_even (c d : ℕ → ℝ) (X : ℕ) {m : ℕ}
    (hm : 2 ≤ m) (heven : Even m) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection d X)).re = 0 := by
  rw [inner_shift_haarSection c d X hm]
  apply Finset.sum_eq_zero
  intro a _ha
  apply Finset.sum_eq_zero
  intro b _hb
  have hne : (2 * a + 1) * m ≠ 2 * b + 1 := by
    rcases heven with ⟨k, hk⟩
    rw [hk, Nat.mul_add]
    omega
  rw [if_neg hne, mul_zero]

/-- At every even lag the surviving coarse pairing equals pairing with the full original profile. -/
theorem integerMixedSource_even_eq_fullProfile (c q d : ℕ → ℝ) (X : ℕ) {m : ℕ}
    (hm : 2 ≤ m) (heven : Even m) :
    integerMixedSource m c q X X = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
      ∫ u, haarSectionProfile c X u * completePairProfile q d X (u + Real.log m) := by
  have hzero := inner_shift_coarseSection_haarSection q c X X hm
  have hdetail := inner_shift_haarSection_even c d X hm heven
  have hfull := inner_shift_haar_completePair_profiles c q d X X (Real.log m)
  rw [inner_add_right, Complex.add_re, hdetail, add_zero] at hfull
  rw [integerMixedSource, hzero, add_zero, hfull]

private theorem integerMixedSource_weight_nonneg (m : ℕ) :
    0 ≤ 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m :=
  div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

/-- Original Gamma energy pays the actual even-lag mixed tail at every complete horizon. -/
theorem cellGammaWeight_mul_abs_evenMixed_tail_le (d q : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (heven : Even m) (X : ℕ) :
    cellGammaWeight A * |integerMixedSource m (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        levyEnergy (completePairProfile q d X) := by
  have hw := integerMixedSource_weight_nonneg m
  have h := mul_le_mul_of_nonneg_left
    (cellGammaWeight_mul_abs_translated_detail_le_gamma q d hA (le_refl X) (-Real.log m)) hw
  simp only [sub_neg_eq_add] at h
  rw [integerMixedSource_even_eq_fullProfile _ q d X hm heven, abs_mul, abs_of_nonneg hw]
  calc
    _ = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        (cellGammaWeight A * |∫ u, haarSectionProfile (fun a => if A ≤ a then d a else 0) X u *
          completePairProfile q d X (u + Real.log m)|) := by ring
    _ ≤ _ := h

/-- The positive first-cell weight bounds the entire mixed even-lag source in Gamma energy. -/
theorem abs_evenMixed_le_gamma (d q : ℕ → ℝ) {m : ℕ}
    (hm : 2 ≤ m) (heven : Even m) (X : ℕ) :
    |integerMixedSource m d q X X| ≤
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight 1) := by
  have hw := integerMixedSource_weight_nonneg m
  have h := mul_le_mul_of_nonneg_left (abs_translated_full_detail_le_gamma q d (le_refl X)
    (-Real.log m)) hw
  simp only [sub_neg_eq_add] at h
  rw [integerMixedSource_even_eq_fullProfile d q d X hm heven, abs_mul, abs_of_nonneg hw]
  exact h

/-- A quantitative tail bound with a factor ready for absolute Euler-factor summation. -/
theorem abs_evenMixed_tail_le_gamma_div_weight (d q : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (heven : Even m) (X : ℕ) :
    |integerMixedSource m (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (cellGammaWeight_pos hA)).mpr
  simpa only [mul_comm] using cellGammaWeight_mul_abs_evenMixed_tail_le d q hA hm heven X

/-- Every even integer lag has inverse-logarithmic mixed tail decay at its literal prime weight. -/
theorem log_mul_abs_evenMixed_tail_le (d q : ℕ → ℝ) {A m : ℕ}
    (hA : 1 ≤ A) (hm : 2 ≤ m) (heven : Even m) (X : ℕ) :
    Real.log (A : ℝ) * |integerMixedSource m (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        levyEnergy (completePairProfile q d X) :=
  (mul_le_mul_of_nonneg_right (log_le_cellGammaWeight hA) (abs_nonneg _)).trans
    (cellGammaWeight_mul_abs_evenMixed_tail_le d q hA hm heven X)

/-- The original prime-two mixed block is paid at every horizon, including terminal half-pairs. -/
theorem cellGammaWeight_mul_abs_primeTwo_tail_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    cellGammaWeight A * |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q X X| ≤
      (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        levyEnergy (completePairProfile q d X) := by
  have h := cellGammaWeight_mul_abs_evenMixed_tail_le d q hA (le_refl 2)
    (show Even 2 from ⟨1, by norm_num⟩) X
  simpa only [integerMixedSource_two, Nat.cast_ofNat] using h

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integerMixedSource_eq_integrals
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integerMixedSource_even_eq_fullProfile
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_abs_evenMixed_tail_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_evenMixed_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.cellGammaWeight_mul_abs_primeTwo_tail_le_gamma
