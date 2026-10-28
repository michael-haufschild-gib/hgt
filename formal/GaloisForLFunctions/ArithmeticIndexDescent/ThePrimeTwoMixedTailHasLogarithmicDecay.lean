import GaloisForLFunctions.ArithmeticIndexDescent.MergedCellVariancePaysCoarseDifferences
import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimeTwoMixedTailIsGammaSmall

/-!
# Inverse-logarithmic decay of the prime-two mixed tail

Gamma controls logarithmically weighted detail mass and, separately, the
same weighted coarse variation. Pointwise Young payment combines these
two bounds without treating them as disjoint shares of the energy.
The mixed tail therefore decays as the reciprocal of its cutoff logarithm.
-/

noncomputable section

open MeasureTheory Finset
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

private theorem signed_unit_young (x y ell : ℝ) :
    |2 * ell * x * y| ≤ x ^ 2 + ell ^ 2 * y ^ 2 := by
  apply abs_le.mpr
  constructor
  · nlinarith only [sq_nonneg (x + ell * y)]
  · nlinarith only [sq_nonneg (x - ell * y)]

/-- The mixed high-detail charge has an explicit logarithmic decay in the original Gamma form. -/
theorem log_mul_abs_primeTwo_tail_le_gamma (d q : ℕ → ℝ) {A Y X : ℕ}
    (hA : 1 ≤ A) (hYX : 2 * Y + 1 ≤ X) :
    Real.log (A : ℝ) *
        |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q Y X| ≤
      (1 + (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2) *
        levyEnergy (completePairProfile q d X) := by
  let ell : ℝ := ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2
  let c : ℕ → ℝ := fun a => if A ≤ a then d a else 0
  have hA0 : 0 < (A : ℝ) := by exact_mod_cast (show 0 < A by omega)
  have hlogA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have hlocal (a : ℕ) (ha : 1 ≤ a) :
      Real.log (A : ℝ) * |2 * ell * (haarMass a * c a * (q (2 * a) - q (2 * a + 1)))| ≤
        Real.log (a : ℝ) * haarMass a * d a ^ 2 +
          ell ^ 2 * (Real.log (a : ℝ) * haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2) := by
    have hm := (haarMass_pos ha).le
    have hla : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
    by_cases hAa : A ≤ a
    · have hl : Real.log (A : ℝ) ≤ Real.log (a : ℝ) :=
        Real.log_le_log hA0 (by exact_mod_cast hAa)
      simp only [c, if_pos hAa]
      rw [show 2 * ell * (haarMass a * d a * (q (2 * a) - q (2 * a + 1))) =
        haarMass a * (2 * ell * d a * (q (2 * a) - q (2 * a + 1))) by ring,
        abs_mul, abs_of_nonneg hm]
      calc
        _ ≤ Real.log (a : ℝ) * (haarMass a *
            |2 * ell * d a * (q (2 * a) - q (2 * a + 1))|) :=
          mul_le_mul_of_nonneg_right hl (mul_nonneg hm (abs_nonneg _))
        _ ≤ Real.log (a : ℝ) * (haarMass a *
            (d a ^ 2 + ell ^ 2 * (q (2 * a) - q (2 * a + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (signed_unit_young _ _ ell) hm) hla
        _ = _ := by ring
    · simp only [c, if_neg hAa, mul_zero, zero_mul, abs_zero]
      exact add_nonneg (mul_nonneg (mul_nonneg hla hm) (sq_nonneg _))
        (mul_nonneg (sq_nonneg ell) (mul_nonneg (mul_nonneg hla hm) (sq_nonneg _)))
  have hsource : primeTwoMixedSource c q Y X =
      ∑ a ∈ Finset.Icc 1 Y, 2 * ell * (haarMass a * c a * (q (2 * a) - q (2 * a + 1))) := by
    rw [primeTwoMixedSource_eq c q hYX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    dsimp only [ell]
    ring
  have hp : Real.log (A : ℝ) * |primeTwoMixedSource c q Y X| ≤
      (∑ a ∈ Finset.Icc 1 Y, Real.log (a : ℝ) * haarMass a * d a ^ 2) +
        ell ^ 2 * ∑ a ∈ Finset.Icc 1 Y,
          Real.log (a : ℝ) * haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2 := by
    rw [hsource]
    apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hlogA).trans
    calc
      _ = ∑ a ∈ Finset.Icc 1 Y, Real.log (A : ℝ) *
          |2 * ell * (haarMass a * c a * (q (2 * a) - q (2 * a + 1)))| :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 Y,
          (Real.log (a : ℝ) * haarMass a * d a ^ 2 +
            ell ^ 2 * (Real.log (a : ℝ) * haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2)) :=
        Finset.sum_le_sum fun a ha => hlocal a (Finset.mem_Icc.mp ha).1
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdetail : (∑ a ∈ Finset.Icc 1 Y, Real.log (a : ℝ) * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) := by
    apply le_trans ?_ (completePairProfile_levyEnergy_ge q d X)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by have := (Finset.mem_Icc.mp ha).2; omega⟩
    · intro a ha _
      have ha1 := (Finset.mem_Icc.mp ha).1
      exact mul_nonneg (mul_nonneg (Real.log_nonneg (by exact_mod_cast ha1))
        (haarMass_pos ha1).le) (sq_nonneg _)
  have hcoarse := mul_le_mul_of_nonneg_left
    (completePair_gamma_ge_log_coarseVariation q d hYX) (sq_nonneg ell)
  change Real.log (A : ℝ) * |primeTwoMixedSource c q Y X| ≤
    (1 + ell ^ 2) * levyEnergy (completePairProfile q d X)
  calc
    _ ≤ _ := hp
    _ ≤ levyEnergy (completePairProfile q d X) + ell ^ 2 * levyEnergy (completePairProfile q d X) :=
      add_le_add hdetail hcoarse
    _ = _ := by ring

/-- At a full odd horizon the same decay accounts for all details, including the terminal region. -/
theorem log_mul_abs_primeTwo_full_tail_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (Y : ℕ) :
    Real.log (A : ℝ) *
        |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
      (1 + (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2) *
        levyEnergy (completePairProfile q d (2 * Y + 1)) := by
  rw [primeTwoMixedSource_odd_horizon]
  exact log_mul_abs_primeTwo_tail_le_gamma d q hA (le_refl _)

/-- The finite detail approximation has an explicit inverse-logarithmic error bound. -/
theorem log_mul_abs_primeTwo_head_error_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (Y : ℕ) :
    Real.log (A : ℝ) *
        |primeTwoMixedSource d q (2 * Y + 1) (2 * Y + 1) -
          primeTwoMixedSource (fun a => if a < A then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
      (1 + (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2) *
        levyEnergy (completePairProfile q d (2 * Y + 1)) := by
  rw [primeTwoMixedSource_sub_head]
  exact log_mul_abs_primeTwo_full_tail_le_gamma d q hA Y

/-- The cutoff logarithm gives a quantitative relative form bound for every full odd horizon. -/
theorem abs_primeTwo_full_tail_le_gamma_div_log (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 < A) (Y : ℕ) :
    |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
      ((1 + (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2) *
        levyEnergy (completePairProfile q d (2 * Y + 1))) / Real.log (A : ℝ) := by
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hA))).mpr
  simpa only [mul_comm] using log_mul_abs_primeTwo_full_tail_le_gamma d q hA.le Y

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.log_mul_abs_primeTwo_tail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.log_mul_abs_primeTwo_full_tail_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.log_mul_abs_primeTwo_head_error_le_gamma
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeTwo_full_tail_le_gamma_div_log
