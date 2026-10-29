import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaCouplingUsesOnlyDetailMass
import GaloisForLFunctions.ArithmeticIndexDescent.CompleteCellAveragesAreBoundedInGammaEnergy
import GaloisForLFunctions.ArithmeticIndexDescent.GammaBoundedCompleteProfilesHaveCompactDetails

/-!
# Uniform finite heads for the actual mixed Gamma form

The mixed coarse/detail block factors through ordinary detail square mass.
The original complete-source Gamma energy controls that mass with a divergent
reciprocal-width weight. A fixed finite detail head therefore approximates the
whole mixed block uniformly over all coefficients and support horizons.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- One fixed constant pays the mixed Gamma tail in the original source energy. -/
def gammaMixedTailConstant : ℝ :=
  128 * Real.exp (1 / 2) * (2 + 12 * haarGammaUpperConstant)

theorem gammaMixedTailConstant_pos : 0 < gammaMixedTailConstant := by
  have h := haarGammaUpperConstant_pos
  unfold gammaMixedTailConstant
  positivity

/-- Every high-detail mixed block is small in the original complete-profile Gamma norm. -/
theorem completeGammaMixed_tail_sq_le (q d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A) (X : ℕ) :
    cellGammaWeight A * completeGammaMixed q (fun a => if A ≤ a then d a else 0) X ^ 2 ≤
      gammaMixedTailConstant * levyEnergy (completePairProfile q d X) ^ 2 := by
  let E := levyEnergy (completePairProfile q d X)
  let G := levyEnergy (averageSectionProfile q X)
  have hE : 0 ≤ E := by
    change 0 ≤ levyEnergy (completePairProfile q d X)
    rw [← norm_levyVector_sq _ (completePairProfile_bv q d X) (completePairProfile_compact q d X)]
    exact sq_nonneg _
  have hG : 0 ≤ G := by
    change 0 ≤ levyEnergy (averageSectionProfile q X)
    rw [← norm_levyVector_sq _ (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)]
    exact sq_nonneg _
  have hh : 0 ≤ levyEnergy (haarSectionProfile d X) := by
    rw [← norm_levyVector_sq _ (haarSectionProfile_bv d X) (haarSectionProfile_compact d X)]
    exact sq_nonneg _
  have hcoarse : G ≤ (2 + 12 * haarGammaUpperConstant) * E := by
    change levyEnergy (averageSectionProfile q X) ≤
      (2 + 12 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X)
    have h := completePairProfile_gamma_pays_coarse_and_detail q d X
    linarith only [h, hh]
  have hmass : cellGammaWeight A *
      (∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) ≤ E := by
    rw [integral_haarSectionProfile_sq]
    exact cellGammaWeight_mul_haar_tail_mass_le_gamma q d hA X
  have hB := completeGammaMixed_sq_le q (fun a => if A ≤ a then d a else 0) X
  calc
    _ ≤ cellGammaWeight A * (128 * Real.exp (1 / 2) * G *
        ∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) :=
      mul_le_mul_of_nonneg_left hB (cellGammaWeight_pos hA).le
    _ = (128 * Real.exp (1 / 2) * G) *
        (cellGammaWeight A * ∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) := by
      ring
    _ ≤ (128 * Real.exp (1 / 2) * G) * E :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (128 * Real.exp (1 / 2) * ((2 + 12 * haarGammaUpperConstant) * E)) * E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoarse (by positivity)) hE
    _ = _ := by unfold gammaMixedTailConstant; ring

/-- One finite head approximates the mixed Gamma form uniformly across all complete sources. -/
theorem exists_uniform_finite_head_for_gamma_mixed (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |completeGammaMixed q d X -
        completeGammaMixed q (fun a => if a < A then d a else 0) X| ≤
          ε * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (gammaMixedTailConstant / ε ^ 2))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : gammaMixedTailConstant / ε ^ 2 < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcap : gammaMixedTailConstant ≤ cellGammaWeight A * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp (hlog.le.trans (log_le_cellGammaWeight hA1))
  refine ⟨A, hA1, ?_⟩
  intro q d X
  have hE : 0 ≤ levyEnergy (completePairProfile q d X) := by
    rw [← norm_levyVector_sq _ (completePairProfile_bv q d X) (completePairProfile_compact q d X)]
    exact sq_nonneg _
  have ht := completeGammaMixed_tail_sq_le q d hA1 X
  have hs : completeGammaMixed q (fun a => if A ≤ a then d a else 0) X ^ 2 ≤
      (ε * levyEnergy (completePairProfile q d X)) ^ 2 := by
    refine le_of_mul_le_mul_left (a := cellGammaWeight A) ?_ (cellGammaWeight_pos hA1)
    refine ht.trans ((mul_le_mul_of_nonneg_right hcap (sq_nonneg _)).trans_eq ?_)
    ring
  have hb : |completeGammaMixed q (fun a => if A ≤ a then d a else 0) X| ≤
      ε * levyEnergy (completePairProfile q d X) := by
    have hnonneg := mul_nonneg hε.le hE
    have habs := abs_nonneg (completeGammaMixed q (fun a => if A ≤ a then d a else 0) X)
    have habssq := sq_abs (completeGammaMixed q (fun a => if A ≤ a then d a else 0) X)
    nlinarith only [hs, hnonneg, habs, habssq]
  have hc : (fun a => d a - (if a < A then d a else 0)) =
      (fun a => if A ≤ a then d a else 0) := by
    funext a
    by_cases ha : a < A
    · simp only [if_pos ha, if_neg (by omega : ¬A ≤ a), sub_self]
    · simp only [if_neg ha, if_pos (by omega : A ≤ a), sub_zero]
  have he := completeGammaMixed_sub q d (fun a => if a < A then d a else 0) X
  rw [hc] at he
  rw [← he]
  exact hb

end GaloisForLFunctions.ArithmeticIndexDescent
