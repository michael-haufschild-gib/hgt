import GaloisForLFunctions.SignedArithmeticHodgeTheory.BinaryVarianceFlowCountsEveryAncestor
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection

/-!
# Small high-generator tails with every translation level retained

The logarithmic square-function bound controls the high-label tail summed over
all dyadic levels. The cutoff acts only on generator labels. Its complement
retains each selected generator's entire translation orbit.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells

private theorem log_label_weight_pos {A : ℕ} (hA : 1 ≤ A) :
    0 < 1 + Real.log (A : ℝ) := by
  have h := Real.log_nonneg (by exact_mod_cast hA : (1 : ℝ) ≤ A)
  linarith only [h]

private theorem finite_high_orbit_mass_le (t : ℝ) (T : Finset ℕ+) {A : ℕ}
    (hA : 1 ≤ A) {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ a ∈ T, if A ≤ (a : ℕ) then logCellHaarOrbitEnergy t a f else 0) ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  apply (le_div_iff₀ (log_label_weight_pos hA)).mpr
  rw [Finset.sum_mul]
  apply le_trans ?_ (sum_log_weight_haar_orbit_le t T hv hc)
  apply Finset.sum_le_sum
  intro a _
  have hE : 0 ≤ logCellHaarOrbitEnergy t a f := tsum_nonneg (fun _ => sq_nonneg _)
  by_cases hAa : A ≤ (a : ℕ)
  · rw [if_pos hAa, mul_comm]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl
      (Real.log_le_log (by exact_mod_cast (show 0 < A by omega)) (by exact_mod_cast hAa))) hE
  · rw [if_neg hAa, zero_mul]
    exact mul_nonneg (log_label_weight_pos a.pos).le hE

/-- Uniform smallness of high generator labels, with the sum over every level inside each orbit. -/
theorem logCellHaar_high_orbit_tail_le (t : ℝ) {A : ℕ} (hA : 1 ≤ A)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑' a : ℕ+, if A ≤ (a : ℕ) then logCellHaarOrbitEnergy t a f else 0) ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) :=
  Real.tsum_le_of_sum_le
    (f := fun a : ℕ+ => if A ≤ (a : ℕ) then logCellHaarOrbitEnergy t a f else 0)
    (fun a => by
    split_ifs
    · exact tsum_nonneg (fun _ => sq_nonneg _)
    · rfl)
    (fun T => finite_high_orbit_mass_le t T hA hv hc)

/-- The same tail bound on the literal level-by-generator Haar coordinates. -/
theorem logCellHaar_high_detail_tail_le (t : ℝ) {A : ℕ} (hA : 1 ≤ A)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑' i : ℕ × ℕ+, if A ≤ (i.2 : ℕ) then logCellHaarReadout t i f ^ 2 else 0) ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  have hs : Summable (fun i : ℕ × ℕ+ =>
      if A ≤ (i.2 : ℕ) then logCellHaarReadout t i f ^ 2 else 0) := by
    refine ((summable_readout_squares t hv hc).indicator {i | A ≤ (i.2 : ℕ)}).congr fun i => ?_
    by_cases hi : A ≤ (i.2 : ℕ)
    · rw [if_pos hi]
      exact _root_.Set.indicator_of_mem (s := {i : ℕ × ℕ+ | A ≤ (i.2 : ℕ)}) hi
        (fun i => logCellHaarReadout t i f ^ 2)
    · rw [if_neg hi]
      exact _root_.Set.indicator_of_notMem (s := {i : ℕ × ℕ+ | A ≤ (i.2 : ℕ)}) hi
        (fun i => logCellHaarReadout t i f ^ 2)
  have hswap : Summable (fun i : ℕ+ × ℕ =>
      if A ≤ (i.1 : ℕ) then logCellHaarReadout t (i.2, i.1) f ^ 2 else 0) :=
    hs.comp_injective (i := fun p : ℕ+ × ℕ => (p.2, p.1))
      (fun p q h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  have he : (∑' i : ℕ × ℕ+, if A ≤ (i.2 : ℕ) then logCellHaarReadout t i f ^ 2 else 0) =
      ∑' a : ℕ+, if A ≤ (a : ℕ) then logCellHaarOrbitEnergy t a f else 0 := by
    rw [← (Equiv.prodComm ℕ+ ℕ).tsum_eq
      (fun i : ℕ × ℕ+ => if A ≤ (i.2 : ℕ) then logCellHaarReadout t i f ^ 2 else 0)]
    change (∑' i : ℕ+ × ℕ, if A ≤ (i.1 : ℕ) then logCellHaarReadout t (i.2, i.1) f ^ 2 else 0) = _
    rw [hswap.tsum_prod]
    apply tsum_congr
    intro a
    by_cases ha : A ≤ (a : ℕ)
    · simp only [ha, if_true, logCellHaarOrbitEnergy]
    · simp only [ha, if_false, tsum_zero]
  rw [he]
  exact logCellHaar_high_orbit_tail_le t hA hv hc

/-- Square-summable coordinates of the original source against the literal normalized Haar profiles. -/
def logCellHaarAnalysis (t : ℝ) (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    lp (fun _ : ℕ × ℕ+ => ℂ) 2 :=
  ⟨fun i => (logCellHaarReadout t i f : ℂ), memℓp_gen (by
    simpa [Real.rpow_two] using
      summable_readout_squares t hv hc)⟩

/-- A generator cutoff keeps every level of each label below the cutoff. -/
def logCellHaarOrbitHead (A : ℕ) :
    lp (fun _ : ℕ × ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ × ℕ+ => ℂ) 2 :=
  lpCoordinateProjection {i | (i.2 : ℕ) < A}

theorem logCellHaarOrbitHead_apply (A : ℕ) (x : lp (fun _ : ℕ × ℕ+ => ℂ) 2)
    (j : ℕ) (a : ℕ+) :
    logCellHaarOrbitHead A x (j, a) = if (a : ℕ) < A then x (j, a) else 0 := by
  simp only [logCellHaarOrbitHead, lpCoordinateProjection_apply, indicator_apply, mem_setOf_eq]

/-- The actual analysis error is small with no cutoff on translation levels. -/
theorem norm_logCellHaarAnalysis_sub_orbitHead_sq_le (t : ℝ) {A : ℕ} (hA : 1 ≤ A)
    (f : ℝ → ℝ) (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    ‖logCellHaarAnalysis t f hv hc - logCellHaarOrbitHead A (logCellHaarAnalysis t f hv hc)‖ ^ 2 ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  have he : logCellHaarAnalysis t f hv hc -
      logCellHaarOrbitHead A (logCellHaarAnalysis t f hv hc) =
      lpCoordinateProjection {i | A ≤ (i.2 : ℕ)} (logCellHaarAnalysis t f hv hc) := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_sub, Pi.sub_apply, logCellHaarOrbitHead,
      lpCoordinateProjection_apply, indicator_apply, mem_setOf_eq]
    change (logCellHaarReadout t i f : ℂ) -
        (if (i.2 : ℕ) < A then (logCellHaarReadout t i f : ℂ) else 0) =
      if A ≤ (i.2 : ℕ) then (logCellHaarReadout t i f : ℂ) else 0
    split_ifs <;> simp_all <;> omega
  rw [he, norm_lpCoordinateProjection_sq]
  have hterms (i : ℕ × ℕ+) :
      ({i : ℕ × ℕ+ | A ≤ (i.2 : ℕ)}.indicator
        (fun j => ‖logCellHaarAnalysis t f hv hc j‖ ^ 2)) i =
      if A ≤ (i.2 : ℕ) then logCellHaarReadout t i f ^ 2 else 0 := by
    simp only [indicator_apply, mem_setOf_eq]
    change (if A ≤ (i.2 : ℕ) then ‖(logCellHaarReadout t i f : ℂ)‖ ^ 2 else 0) = _
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterms]
  exact logCellHaar_high_detail_tail_le t hA hv hc

/-- Complete arithmetic profiles inherit the all-level cutoff estimate with every coarse coefficient free. -/
theorem completePair_high_detail_tail_le (q d : ℕ → ℝ) (X : ℕ) (t : ℝ)
    {A : ℕ} (hA : 1 ≤ A) :
    (∑' i : ℕ × ℕ+, if A ≤ (i.2 : ℕ) then
      logCellHaarReadout t i (completePairProfile q d X) ^ 2 else 0) ≤
      32 * levyEnergy (completePairProfile q d X) / (1 + Real.log (A : ℝ)) :=
  logCellHaar_high_detail_tail_le t hA
    (completePairProfile_bv q d X) (completePairProfile_compact q d X)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellHaar_high_detail_tail_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.norm_logCellHaarAnalysis_sub_orbitHead_sq_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.completePair_high_detail_tail_le
