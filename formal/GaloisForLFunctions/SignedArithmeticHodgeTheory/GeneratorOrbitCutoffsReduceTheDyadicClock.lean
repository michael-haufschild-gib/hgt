import GaloisForLFunctions.SignedArithmeticHodgeTheory.FiniteGeneratorOrbitsApproximateThePhysicalCellSource
import GaloisForLFunctions.SignedArithmeticHodgeTheory.ArithmeticTranslationsHaveAnExactDyadicLevelMatrix

/-!
# Exact dyadic correlation splitting by whole generator orbits

The actual generator cutoff commutes with the dyadic clock because it retains
every level of each selected generator. Its orthogonal head and tail therefore
have no mixed dyadic correlations. One original-source Gamma reserve bounds
the correlation error uniformly in the translation power and source horizon.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2

open Classical in
/-- The actual whole-orbit cutoff acts only on the generator coordinate. -/
theorem logCellDyadicCoordinates_head_apply (A : ℕ) (x : CellH)
    (j : ℕ) (o : Option ℕ+) :
    logCellDyadicCoordinates (logCellGeneratorHead A x) (j, o) =
      if retainedLogCellGenerator A o then logCellDyadicCoordinates x (j, o) else 0 := by
  classical
  rw [logCellDyadicCoordinates_generatorHead, lpCoordinateProjection_apply]
  rfl

/-- Keeping entire generator orbits makes the cutoff commute with the actual cell clock. -/
theorem logCellGeneratorHead_shift (A : ℕ) (x : CellH) :
    logCellGeneratorHead A (W x) = W (logCellGeneratorHead A x) := by
  classical
  apply logCellDyadicCoordinates.injective
  apply lp.ext
  funext i
  rcases i with ⟨j, o⟩
  cases j with
  | zero =>
    simp only [logCellDyadicCoordinates_head_apply,
      logCellDyadicCoordinates_shift_zero, ite_self]
  | succ j =>
    simp only [logCellDyadicCoordinates_head_apply, logCellDyadicCoordinates_shift_succ]

/-- The same exact commutation holds with no cutoff on the dyadic translation power. -/
theorem logCellGeneratorHead_dyadic_pow (A k : ℕ) (x : CellH) :
    logCellGeneratorHead A ((W ^ k) x) = (W ^ k) (logCellGeneratorHead A x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, logCellGeneratorHead_shift, ih,
      mul_apply_eq_comp]

/-- Selected and omitted generator families are orthogonal for every pair of source vectors. -/
theorem inner_logCellGeneratorHead_tail (A : ℕ) (x y : CellH) :
    inner ℂ (logCellGeneratorHead A x) (y - logCellGeneratorHead A y) = 0 := by
  classical
  rw [← LinearIsometry.inner_map_map logCellDyadicCoordinates.toLinearIsometry]
  change inner ℂ (logCellDyadicCoordinates (logCellGeneratorHead A x))
    (logCellDyadicCoordinates (y - logCellGeneratorHead A y)) = 0
  rw [map_sub, logCellDyadicCoordinates_generatorHead,
    logCellDyadicCoordinates_generatorHead, lp.inner_eq_tsum]
  calc
    _ = ∑' _i : ℕ × Option ℕ+, (0 : ℂ) := by
      apply tsum_congr
      intro i
      change inner ℂ
          (lpCoordinateProjection {i | retainedLogCellGenerator A i.2} (logCellDyadicCoordinates x) i)
          ((logCellDyadicCoordinates y -
            lpCoordinateProjection {i | retainedLogCellGenerator A i.2} (logCellDyadicCoordinates y)) i) = 0
      simp only [lp.coeFn_sub, Pi.sub_apply, lpCoordinateProjection_apply,
        indicator_apply, mem_setOf_eq]
      by_cases hi : retainedLogCellGenerator A i.2
      · simp only [if_pos hi, sub_self, inner_zero_right]
      · simp only [if_neg hi, inner_zero_left]
    _ = 0 := tsum_zero

/-- Exact decomposition of every actual dyadic correlation into its head and tail. -/
theorem dyadic_correlation_sub_head (A k : ℕ) (x : CellH) :
    inner ℂ ((W ^ k) x) x -
      inner ℂ ((W ^ k) (logCellGeneratorHead A x)) (logCellGeneratorHead A x) =
        inner ℂ ((W ^ k) (x - logCellGeneratorHead A x)) (x - logCellGeneratorHead A x) := by
  have hht : inner ℂ ((W ^ k) (logCellGeneratorHead A x))
      (x - logCellGeneratorHead A x) = 0 := by
    rw [← logCellGeneratorHead_dyadic_pow]
    exact inner_logCellGeneratorHead_tail A _ _
  have hth : inner ℂ ((W ^ k) (x - logCellGeneratorHead A x))
      (logCellGeneratorHead A x) = 0 := by
    rw [map_sub, ← logCellGeneratorHead_dyadic_pow]
    exact inner_eq_zero_symm.mp (inner_logCellGeneratorHead_tail A x ((W ^ k) x))
  have hx : logCellGeneratorHead A x + (x - logCellGeneratorHead A x) = x := by abel
  calc
    _ = inner ℂ ((W ^ k) (logCellGeneratorHead A x + (x - logCellGeneratorHead A x)))
        (logCellGeneratorHead A x + (x - logCellGeneratorHead A x)) -
      inner ℂ ((W ^ k) (logCellGeneratorHead A x)) (logCellGeneratorHead A x) := by
        rw [hx]
    _ = _ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hht, hth]
      ring

/-- Dyadic powers retain the original cell-space norm. -/
theorem norm_logCellDyadic_pow (k : ℕ) (x : CellH) : ‖(W ^ k) x‖ = ‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, norm_logCellShift_apply (by norm_num), ih]

/-- Every dyadic correlation has the same quadratic tail cost, independently of its lag. -/
theorem abs_re_dyadic_correlation_sub_head_le (A k : ℕ) (x : CellH) :
    |(inner ℂ ((W ^ k) x) x).re -
      (inner ℂ ((W ^ k) (logCellGeneratorHead A x)) (logCellGeneratorHead A x)).re| ≤
        ‖x - logCellGeneratorHead A x‖ ^ 2 := by
  rw [← Complex.sub_re, dyadic_correlation_sub_head]
  calc
    _ ≤ ‖inner ℂ ((W ^ k) (x - logCellGeneratorHead A x))
      (x - logCellGeneratorHead A x)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(W ^ k) (x - logCellGeneratorHead A x)‖ *
      ‖x - logCellGeneratorHead A x‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_logCellDyadic_pow, pow_two]

/-- The original source pays the cell-coordinate tail before any Gamma projection is made. -/
theorem norm_original_cell_coordinates_sub_head_sq_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    let x := wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc)
    ‖x - logCellGeneratorHead A x‖ ^ 2 ≤ 32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  have h := norm_physical_cell_component_sub_head_sq_le f hv hc hA
  dsimp only at h ⊢
  rwa [← map_sub, norm_wholeLineLogCellEmbedding] at h

/-- One Gamma reserve pays every dyadic lag on the actual finite cell source. -/
theorem abs_re_wholeCell_dyadic_head_error_le (c : ℕ → ℝ) (X k : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    let x := logCellEmbedding.adjoint (cellSection c 1 X)
    |(inner ℂ ((W ^ k) x) x).re -
      (inner ℂ ((W ^ k) (logCellGeneratorHead A x)) (logCellGeneratorHead A x)).re| ≤
        32 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ)) := by
  have h := norm_original_cell_coordinates_sub_head_sq_le (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  dsimp only at h ⊢
  rw [realSourceLp_wholeCellProfile, wholeLineLogCellEmbedding_adjoint_self] at h
  exact (abs_re_dyadic_correlation_sub_head_le A k _).trans h

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_dyadic_pow
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.dyadic_correlation_sub_head
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_re_wholeCell_dyadic_head_error_le
