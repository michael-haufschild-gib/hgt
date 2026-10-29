import GaloisForLFunctions.ArithmeticIndexDescent.TheFullHaarPrimeSourceHasUniformFiniteHeads
import GaloisForLFunctions.ArithmeticIndexDescent.TheFullPolarNonfirstSourceHasUniformFiniteIndex

/-!
# Almost all complete Gamma energy survives the nonfirst mixed source

The entire Haar prime diagonal, the disjoint mixed exponents above one,
and the constant detail mass are arbitrarily small after one finite detail
head. Their payments use the same complete-profile Gamma energy. The full
original pole is retained exactly, including both coarse and mixed terms.
-/

noncomputable section
open MeasureTheory
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

private theorem tail_eq_of_head_zero {A B : ℕ} (hBA : B ≤ A)
    (d : ℕ → ℝ) (hd : ∀ a : ℕ, a < A → d a = 0) :
    (fun a => if B ≤ a then d a else 0) = d := by
  funext a
  by_cases ha : B ≤ a
  · exact if_pos ha
  · rw [if_neg ha, hd a ((lt_of_not_ge ha).trans_le hBA)]

/-- The full Haar prime diagonal and every mixed exponent above one leave an arbitrarily small
error relative to the original Gamma source plus its complete pole. -/
theorem exists_fullPolarNonfirst_gamma_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      |fullPolarNonfirstSourceForm q d X -
        (levyEnergy (completePairProfile q d X) +
          (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
            2 * sinhHalfMoment (completePairProfile q d X) ^ 2))| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨A₀, hA₀, hp⟩ := exists_haarPrime_tail_small_originalGamma (ε / 4) hε4
  obtain ⟨A₁, _, hs⟩ := exists_uniform_small_squarePrimeMixed_tail hε4
  obtain ⟨A₂, _, ho⟩ := exists_oddHigherPrimePower_gamma_small_tail hε4
  let C := 2 * |gammaHardyPhaseRate 0|
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (4 * C / ε))
  have hB1 : 1 ≤ B := by
    have hb : (0 : ℝ) < B := (Real.exp_pos _).trans hB
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hb.ne')
  have hcap : C ≤ (ε / 4) * cellGammaWeight B := by
    have hl := Real.log_lt_log (Real.exp_pos _) hB
    rw [Real.log_exp] at hl
    have h := (div_le_iff₀ hε).mp (hl.le.trans (log_le_cellGammaWeight hB1))
    linarith only [h]
  let A := max (max A₀ A₁) (max A₂ B)
  have h₀ : A₀ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have h₁ : A₁ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have h₂ : A₂ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : B ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA₀.trans h₀, ?_⟩
  intro q d X hd
  have hprime : |haarPrimeEnergy d X| ≤ (ε / 4) * levyEnergy (completePairProfile q d X) := by
    simpa only [tail_eq_of_head_zero h₀ d hd] using hp q d X
  have hsquare : |squarePrimeMixedSource q d X| ≤
      (ε / 4) * levyEnergy (completePairProfile q d X) := by
    simpa only [tail_eq_of_head_zero h₁ d hd] using hs q d X
  have hodd : |oddHigherPrimePowerMixedSource d q X| ≤
      (ε / 4) * levyEnergy (completePairProfile q d X) := by
    simpa only [tail_eq_of_head_zero h₂ d hd] using ho d q X
  have hmass0 : 0 ≤ ∫ x, haarSectionProfile d X x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hmass : cellGammaWeight B * (∫ x, haarSectionProfile d X x ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
    rw [integral_haarSectionProfile_sq, ← norm_haarSection_sq]
    have h := cellGammaWeight_mul_norm_haar_tail_sq_le_logMass d hB1 X
    rw [tail_eq_of_head_zero h₃ d hd] at h
    exact h.trans (haarLogarithmicMass_le_completeGamma q d X)
  have hconstant : |2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2)| ≤
      (ε / 4) * levyEnergy (completePairProfile q d X) := by
    calc
      _ = C * (∫ x, haarSectionProfile d X x ^ 2) := by
        simp only [C, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hmass0]
      _ ≤ ((ε / 4) * cellGammaWeight B) * (∫ x, haarSectionProfile d X x ^ 2) :=
        mul_le_mul_of_nonneg_right hcap hmass0
      _ = (ε / 4) * (cellGammaWeight B * ∫ x, haarSectionProfile d X x ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hε4.le
  have he : fullPolarNonfirstSourceForm q d X -
      (levyEnergy (completePairProfile q d X) +
        (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2)) =
      2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2) -
        haarPrimeEnergy d X - squarePrimeMixedSource q d X -
          oddHigherPrimePowerMixedSource d q X := by
    unfold fullPolarNonfirstSourceForm
    ring
  rw [he]
  calc
    _ ≤ |2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2)| +
        |haarPrimeEnergy d X| + |squarePrimeMixedSource q d X| +
          |oddHigherPrimePowerMixedSource d q X| :=
      (abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))) (le_refl _))
    _ ≤ (ε / 4) * levyEnergy (completePairProfile q d X) +
        (ε / 4) * levyEnergy (completePairProfile q d X) +
        (ε / 4) * levyEnergy (completePairProfile q d X) +
        (ε / 4) * levyEnergy (completePairProfile q d X) :=
      add_le_add (add_le_add (add_le_add hconstant hprime) hsquare) hodd
    _ = _ := by ring

/-- Any fraction below one of the complete Gamma energy survives, with the exact positive
cosh square and the single original adverse sinh square. -/
theorem exists_fullPolarNonfirst_completeGamma_reserve (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (1 - ε) * levyEnergy (completePairProfile q d X) +
          2 * coshHalfMoment (completePairProfile q d X) ^ 2 ≤
        fullPolarNonfirstSourceForm q d X +
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2 := by
  obtain ⟨A, hA, hclose⟩ := exists_fullPolarNonfirst_gamma_approximation ε hε
  refine ⟨A, hA, ?_⟩
  intro q d X hd
  have h := (abs_le.mp (hclose q d X hd)).1
  linarith only [h]

end GaloisForLFunctions.ArithmeticIndexDescent
