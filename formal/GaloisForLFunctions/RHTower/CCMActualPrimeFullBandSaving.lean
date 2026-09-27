import GaloisForLFunctions.RHTower.CCMActualPrimeBandInterference

/-!
# A collective saving for the complete actual finite-prime operator

The two separated bands are retained together. Every other atom remains
in the remainder, and its interactions with the bands are bounded before
the complete squared norm is estimated. No coefficient or degree cutoff
is imposed on the physical vector.
-/

open Complex MeasureTheory Set
open scoped BigOperators InnerProduct
noncomputable section
namespace RHTower

private theorem atom_norm_le (a : SuzukiPositiveAperture) (n : ℕ) (hn : 2 ≤ n)
    (f : suzukiApertureHilbert a) :
    ‖((ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a n) f‖ ≤
      (if a.1 < Real.log n then 1 else 2) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * ‖f‖ := by
  have hv := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  by_cases hl : a.1 < Real.log n
  · rw [if_pos hl]
    have hop := (ContinuousLinearMap.le_opNorm (ccmPrimeTransportOperator a n) f).trans
      (mul_le_mul_of_nonneg_right (norm_ccmPrimeTransportOperator_le_outerShell a n hl)
        (norm_nonneg f))
    have h := mul_le_mul_of_nonneg_left hop hv
    nlinarith only [h]
  · rw [if_neg hl]
    have hop := (ContinuousLinearMap.le_opNorm (ccmPrimeTransportOperator a n) f).trans
      (mul_le_mul_of_nonneg_right (norm_ccmPrimeTransportOperator_le a (by omega : 1 ≤ n))
        (norm_nonneg f))
    have h := mul_le_mul_of_nonneg_left hop hv
    nlinarith only [h]

private theorem band_subset (a : SuzukiPositiveAperture) (lo hi : ℝ) :
    ccmActualPrimeBand a lo hi ⊆ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ :=
  Finset.filter_subset _ _

private theorem bands_disjoint (a : SuzukiPositiveAperture) :
    Disjoint (ccmActualPrimeBand a 4 3) (ccmActualPrimeBand a 1 0) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have hnl := (Finset.mem_filter.mp hn).2
  have hml := (Finset.mem_filter.mp hm).2
  linarith [hnl.2, hml.1]

private theorem band_vector_sum (a : SuzukiPositiveAperture) (lo hi : ℝ)
    (f : suzukiApertureHilbert a) :
    (∑ n ∈ ccmActualPrimeBand a lo hi,
      ((ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a n) f) =
        ccmActualPrimeBandOperator a lo hi f := by
  unfold ccmActualPrimeBandOperator
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [ccmWeightedPrimeTransport_eq, criticalMellinAtomWeight_eq_div_sqrt]

private theorem band_budget_sum (a : SuzukiPositiveAperture) (lo hi : ℝ)
    (houter : ∀ n ∈ ccmActualPrimeBand a lo hi, a.1 < Real.log n) :
    (∑ n ∈ ccmActualPrimeBand a lo hi,
      (if a.1 < Real.log n then 1 else 2) *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n)) = ccmActualPrimeBandMass a lo hi := by
  unfold ccmActualPrimeBandMass
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos (houter n hn), one_mul, criticalMellinAtomWeight_eq_div_sqrt]

/-- The complete head gains the product of two complete band masses. All
remaining atoms and mixed terms are included in this inequality. -/
theorem ccmFinitePrimeOperator_sq_le_collectiveBandBudget
    (a : {a : SuzukiPositiveAperture // 4 < a.1}) (f : suzukiApertureHilbert a.1) :
    4 * ‖ccmFinitePrimeOperator a.1 f‖ ^ 2 ≤
      (4 * ccmPrimeOuterShellBudget a.1 ^ 2 -
        ccmActualPrimeBandMass a.1 4 3 * ccmActualPrimeBandMass a.1 1 0) * ‖f‖ ^ 2 := by
  classical
  let S := Finset.Icc 2 ⌊Real.exp (2 * a.1.1)⌋₊
  let L := ccmActualPrimeBand a.1 4 3
  let H := ccmActualPrimeBand a.1 1 0
  let R := S \ (L ∪ H)
  let V := fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) • ccmPrimeTransportOperator a.1 n) f
  let b := fun n => (if a.1.1 < Real.log n then (1 : ℝ) else 2) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
  let r := ∑ n ∈ R, b n
  let m := ccmActualPrimeBandMass a.1 4 3
  let n := ccmActualPrimeBandMass a.1 1 0
  let X := ccmActualPrimeBandOperator a.1 4 3 f + ccmActualPrimeBandOperator a.1 1 0 f
  have hsub : L ∪ H ⊆ S := Finset.union_subset (band_subset a.1 4 3) (band_subset a.1 1 0)
  have hdis : Disjoint L H := bands_disjoint a.1
  have hsplit : (∑ k ∈ R, V k) + X = ccmFinitePrimeOperator a.1 f := by
    have hs := Finset.sum_sdiff (f := V) hsub
    rw [Finset.sum_union hdis, band_vector_sum, band_vector_sum] at hs
    simpa only [ccmFinitePrimeOperator, sum_apply, S, R, X] using hs
  have hlo (k : ℕ) (hk : k ∈ L) : a.1.1 < Real.log k := by
    have h := (Finset.mem_filter.mp hk).2
    linarith [h.1, a.2]
  have hhi (k : ℕ) (hk : k ∈ H) : a.1.1 < Real.log k := by
    have h := (Finset.mem_filter.mp hk).2
    linarith [h.1, a.2]
  have hbudget : r + (m + n) = ccmPrimeOuterShellBudget a.1 := by
    have hs := Finset.sum_sdiff (f := b) hsub
    rw [Finset.sum_union hdis, band_budget_sum a.1 4 3 hlo,
      band_budget_sum a.1 1 0 hhi] at hs
    exact hs
  have hb (k : ℕ) : 0 ≤ b k := by
    dsimp only [b]
    split_ifs <;> exact mul_nonneg (by norm_num)
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  have hr : 0 ≤ r := Finset.sum_nonneg fun k _ => hb k
  have hm : 0 ≤ m := ccmActualPrimeBandMass_nonneg a.1 4 3
  have hn : 0 ≤ n := ccmActualPrimeBandMass_nonneg a.1 1 0
  have hrem : ‖∑ k ∈ R, V k‖ ≤ r * ‖f‖ := by
    unfold r
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro k hk
    exact atom_norm_le a.1 k (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hk).1).1 f
  have hfull : ‖ccmFinitePrimeOperator a.1 f‖ ≤ ‖X‖ + r * ‖f‖ := by
    rw [← hsplit]
    exact (norm_add_le _ _).trans (by linarith only [hrem])
  have hpair := ccmActualPrimeBands_sq_bound a f
  change 4 * ‖X‖ ^ 2 ≤ (4 * (m + n) ^ 2 - m * n) * ‖f‖ ^ 2 at hpair
  have hX : ‖X‖ ≤ (m + n) * ‖f‖ := by
    have hmn : 0 ≤ m * n * ‖f‖ ^ 2 := by positivity
    have hright : 0 ≤ (m + n) * ‖f‖ := by positivity
    nlinarith [norm_nonneg X]
  have hfullsq := pow_le_pow_left₀ (norm_nonneg _) hfull 2
  have hcross := mul_le_mul_of_nonneg_right hX
    (by positivity : 0 ≤ 2 * r * ‖f‖)
  rw [← hbudget]
  change 4 * ‖ccmFinitePrimeOperator a.1 f‖ ^ 2 ≤
    (4 * (r + (m + n)) ^ 2 - m * n) * ‖f‖ ^ 2
  nlinarith only [hpair, hfullsq, hcross]

end RHTower
