import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaMeanGraphPaysThePrimeTwoMixedBlock

/-!
# The prime-two mixed tail is small in Gamma energy

An adjustable share of the mean graph pays the actual prime-two mixed block.
The remaining detail charge is constant in the horizon. The logarithmic
detail reserve therefore makes every sufficiently high detail tail arbitrarily
small relative to the original Gamma energy, with all coarse coefficients free.
That energy is evaluated on the complete untruncated source.
-/

noncomputable section

open MeasureTheory Finset
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- A prescribed positive share of the graph gives an explicit reciprocal detail charge. -/
theorem abs_primeTwoMixedSource_le_graph_fraction (d q : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) {δ : ℝ} (hδ : 0 < δ) :
    |primeTwoMixedSource d q Y X| ≤
      (primeTwoDetailCharge / δ) * primeTwoDetailMass d Y +
        δ * ((1 / 2) * completePairMeanGraph q X) := by
  have he : 0 < primeTwoDetailCharge / δ := div_pos primeTwoDetailCharge_pos hδ
  have hcoef : (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2 /
      (primeTwoDetailCharge / δ) ≤ δ * (Real.exp (-(1 / 2 : ℝ)) / 4) := by
    rw [div_div_eq_mul_div]
    simpa only [mul_div_assoc, mul_comm] using
      mul_le_mul_of_nonneg_left primeTwoDetailCharge_payment hδ.le
  apply (abs_primeTwoMixedSource_le_variation d q hYX he).trans
  apply add_le_add_left
  calc
    _ ≤ (δ * (Real.exp (-(1 / 2 : ℝ)) / 4)) * primeTwoCoarseVariation q Y :=
      mul_le_mul_of_nonneg_right hcoef (primeTwoCoarseVariation_nonneg q Y)
    _ = δ * ((Real.exp (-(1 / 2 : ℝ)) / 4) * primeTwoCoarseVariation q Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeTwoCoarseVariation_le_meanGraph q hYX) hδ.le

/-- The complete mixed tail has arbitrarily small Gamma form bound, uniformly in the horizon. -/
theorem exists_primeTwo_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (Y : ℕ),
      |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
        δ * levyEnergy (completePairProfile q d (2 * Y + 1)) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp ((primeTwoDetailCharge / δ) / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog {a : ℕ} (hAa : A ≤ a) : primeTwoDetailCharge / δ ≤ δ * Real.log (a : ℝ) := by
    have hbound : Real.exp ((primeTwoDetailCharge / δ) / δ) < (a : ℝ) :=
      hA.trans_le (by exact_mod_cast hAa)
    have hl := Real.log_lt_log (Real.exp_pos _) hbound
    rw [Real.log_exp] at hl
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hl.le
  refine ⟨A, hA1, ?_⟩
  intro d q Y
  let c : ℕ → ℝ := fun a => if A ≤ a then d a else 0
  have hcoef (a : ℕ) (ha : 1 ≤ a) :
      (primeTwoDetailCharge / δ) * (haarMass a * c a ^ 2) ≤
        δ * (Real.log (a : ℝ) * haarMass a * d a ^ 2) := by
    by_cases hAa : A ≤ a
    · simpa only [c, if_pos hAa, mul_assoc] using mul_le_mul_of_nonneg_right (hlog hAa)
        (mul_nonneg (haarMass_pos ha).le (sq_nonneg (d a)))
    · simp only [c, if_neg hAa, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      exact mul_nonneg hδ.le (mul_nonneg
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast ha)) (haarMass_pos ha).le) (sq_nonneg _))
  have htotal : (primeTwoDetailCharge / δ) * primeTwoDetailMass c (2 * Y + 1) ≤
      δ * ∑ a ∈ Finset.Icc 1 (2 * Y + 1), Real.log (a : ℝ) * haarMass a * d a ^ 2 := by
    rw [primeTwoDetailMass, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hcoef a (Finset.mem_Icc.mp ha).1
  have hsub : primeTwoDetailMass c Y ≤ primeTwoDetailMass c (2 * Y + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by have := (Finset.mem_Icc.mp ha).2; omega⟩
    · intro a ha _
      exact mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
  have hbudget := (mul_le_mul_of_nonneg_left hsub
    (div_pos primeTwoDetailCharge_pos hδ).le).trans htotal
  have hpay := abs_primeTwoMixedSource_le_graph_fraction c q (le_refl (2 * Y + 1)) hδ
  have hgamma := mul_le_mul_of_nonneg_left
    (completePairProfile_levyEnergy_ge_detail_graph_exterior q d (2 * Y + 1)) hδ.le
  have hext := mul_nonneg hδ.le
    (ENNReal.toReal_nonneg (a := completePairExteriorCharge q (2 * Y + 1)))
  change |primeTwoMixedSource c q (2 * Y + 1) (2 * Y + 1)| ≤
    δ * levyEnergy (completePairProfile q d (2 * Y + 1))
  rw [primeTwoMixedSource_odd_horizon]
  linarith only [hbudget, hpay, hgamma, hext]

/-- Splitting detail coefficients splits the entire odd-horizon mixed source. -/
theorem primeTwoMixedSource_add_details (d e q : ℕ → ℝ) (Y : ℕ) :
    primeTwoMixedSource (fun a => d a + e a) q (2 * Y + 1) (2 * Y + 1) =
      primeTwoMixedSource d q (2 * Y + 1) (2 * Y + 1) +
        primeTwoMixedSource e q (2 * Y + 1) (2 * Y + 1) := by
  simp only [primeTwoMixedSource_odd_horizon,
    primeTwoMixedSource_eq _ _ (le_refl (2 * Y + 1))]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem primeTwoMixedSource_sub_head (d q : ℕ → ℝ) (A Y : ℕ) :
    primeTwoMixedSource d q (2 * Y + 1) (2 * Y + 1) -
      primeTwoMixedSource (fun a => if a < A then d a else 0) q (2 * Y + 1) (2 * Y + 1) =
        primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q (2 * Y + 1) (2 * Y + 1) := by
  have hd : (fun a => (if a < A then d a else 0) + (if A ≤ a then d a else 0)) = d := by
    funext a
    by_cases h : a < A
    · simp only [if_pos h, if_neg (by omega : ¬A ≤ a), add_zero]
    · simp only [if_neg h, if_pos (by omega : A ≤ a), zero_add]
  have hs := primeTwoMixedSource_add_details
    (fun a => if a < A then d a else 0) (fun a => if A ≤ a then d a else 0) q Y
  rw [hd] at hs
  linarith only [hs]

/-- Finitely many detail coordinates approximate the mixed source in the original Gamma form. -/
theorem exists_primeTwo_finite_detail_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (Y : ℕ),
      |primeTwoMixedSource d q (2 * Y + 1) (2 * Y + 1) -
        primeTwoMixedSource (fun a => if a < A then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
          δ * levyEnergy (completePairProfile q d (2 * Y + 1)) := by
  obtain ⟨A, hA, hpay⟩ := exists_primeTwo_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro d q Y
  rw [primeTwoMixedSource_sub_head]
  exact hpay d q Y

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeTwoMixedSource_le_graph_fraction
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_primeTwo_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_primeTwo_finite_detail_approximation
