import GaloisForLFunctions.SignedArithmeticHodgeTheory.GeneratorOrbitCutoffsReduceTheDyadicClock
import GaloisForLFunctions.ArithmeticIndexDescent.TheEntirePrimeTwoEulerMixedSourceIsGammaSmall

/-!
# The full dyadic Euler correlation has one all-level Gamma tail budget

Whole generator orbits reduce every power of the actual dyadic clock. The
head error in the complete prime-two correlation is therefore its tail
correlation alone. The literal critical Euler weights are summable, so one
original-source Gamma estimate pays all dyadic lags and all source levels.
The physical identification retains the original finite cell profile.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open ArithmeticIndexDescent

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "HalfH" => Lp ℂ 2 halfLineMeasure
local notation "W" => logCellShift 2

/-- The full critical correlation contribution of prime two on the actual cell space. -/
def dyadicEulerCorrelation (x : CellH) : ℝ :=
  ∑' k : ℕ, primeTwoPowerWeight k * (inner ℂ ((W ^ (k + 1)) x) x).re

private theorem abs_re_dyadic_correlation_le (k : ℕ) (x : CellH) :
    |(inner ℂ ((W ^ k) x) x).re| ≤ ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖inner ℂ ((W ^ k) x) x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(W ^ k) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = _ := by rw [norm_logCellDyadic_pow, pow_two]

private theorem abs_dyadicEulerTerm_le (k : ℕ) (x : CellH) :
    |primeTwoPowerWeight k * (inner ℂ ((W ^ (k + 1)) x) x).re| ≤
      primeTwoPowerWeight k * ‖x‖ ^ 2 := by
  rw [abs_mul, abs_of_nonneg (primeTwoPowerWeight_nonneg k)]
  exact mul_le_mul_of_nonneg_left (abs_re_dyadic_correlation_le (k + 1) x)
    (primeTwoPowerWeight_nonneg k)

/-- Absolute convergence is proved before performing any Euler-series subtraction. -/
theorem summable_norm_dyadicEulerCorrelation (x : CellH) :
    Summable (fun k : ℕ => ‖primeTwoPowerWeight k * (inner ℂ ((W ^ (k + 1)) x) x).re‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => ?_) (hasSum_primeTwoPowerWeight.summable.mul_right (‖x‖ ^ 2))
  simpa only [Real.norm_eq_abs] using abs_dyadicEulerTerm_le k x

theorem summable_dyadicEulerCorrelation (x : CellH) :
    Summable (fun k : ℕ => primeTwoPowerWeight k * (inner ℂ ((W ^ (k + 1)) x) x).re) :=
  (summable_norm_dyadicEulerCorrelation x).of_norm

/-- The complete Euler series has the literal geometric coefficient cost. -/
theorem abs_dyadicEulerCorrelation_le (x : CellH) :
    |dyadicEulerCorrelation x| ≤ primeTwoEulerWeightTotal * ‖x‖ ^ 2 := by
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (hasSum_primeTwoPowerWeight.summable.mul_right (‖x‖ ^ 2))
    (fun k => abs_dyadicEulerTerm_le k x)
  rw [tsum_mul_right, hasSum_primeTwoPowerWeight.tsum_eq] at h
  exact h

/-- Orthogonal whole generator orbits split the complete dyadic Euler contribution exactly. -/
theorem dyadicEulerCorrelation_sub_head (A : ℕ) (x : CellH) :
    dyadicEulerCorrelation x - dyadicEulerCorrelation (logCellGeneratorHead A x) =
      dyadicEulerCorrelation (x - logCellGeneratorHead A x) := by
  unfold dyadicEulerCorrelation
  rw [← (summable_dyadicEulerCorrelation x).tsum_sub
    (summable_dyadicEulerCorrelation (logCellGeneratorHead A x))]
  apply tsum_congr
  intro k
  rw [← mul_sub, ← Complex.sub_re, dyadic_correlation_sub_head]

/-- No dyadic level or Euler power is charged a second copy of the source norm. -/
theorem abs_dyadicEulerCorrelation_head_error_le (A : ℕ) (x : CellH) :
    |dyadicEulerCorrelation x - dyadicEulerCorrelation (logCellGeneratorHead A x)| ≤
      primeTwoEulerWeightTotal * ‖x - logCellGeneratorHead A x‖ ^ 2 := by
  rw [dyadicEulerCorrelation_sub_head]
  exact abs_dyadicEulerCorrelation_le _

/-- One original Gamma reserve pays the full Euler error on a source's cell component. -/
theorem abs_original_cell_dyadicEuler_head_error_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    let x := wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc)
    |dyadicEulerCorrelation x - dyadicEulerCorrelation (logCellGeneratorHead A x)| ≤
      primeTwoEulerWeightTotal * (32 * levyEnergy f / (1 + Real.log (A : ℝ))) := by
  dsimp only
  exact (abs_dyadicEulerCorrelation_head_error_le A _).trans
    (mul_le_mul_of_nonneg_left (norm_original_cell_coordinates_sub_head_sq_le f hv hc hA)
      primeTwoEulerWeightTotal_nonneg)

/-- The actual arithmetic map at a power of two equals that power of the cell clock. -/
theorem logCellShift_two_pow_succ (k : ℕ) :
    logCellShift (2 ^ (k + 1)) = W ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 ≤ 2 ^ (k + 1) := by
      have h := one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega : k + 1 ≠ 0)
      omega
    calc
      _ = W ∘L logCellShift (2 ^ (k + 1)) := by
        rw [logCellShift_comp (by norm_num) hk, pow_succ']
      _ = W * W ^ (k + 1) := by rw [ih]; rfl
      _ = _ := (pow_succ' W (k + 1)).symm

/-- The dyadic Euler contribution written directly in the original physical half-line space. -/
def physicalDyadicEulerCorrelation (u : HalfH) : ℝ :=
  ∑' k : ℕ, primeTwoPowerWeight k *
    (inner ℂ (halfLineRightShift (Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) u) u).re

/-- Every clock power reads the original physical correlation at the corresponding prime power. -/
theorem dyadic_power_correlation_eq_physical (k : ℕ) (x : CellH) :
    inner ℂ ((W ^ (k + 1)) x) x =
      inner ℂ (halfLineRightShift (Real.log ((2 ^ (k + 1) : ℕ) : ℝ))
        (logCellEmbedding x)) (logCellEmbedding x) := by
  have hk : 2 ≤ 2 ^ (k + 1) := by
    have h := one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega : k + 1 ≠ 0)
    omega
  have ht := congrArg (fun T => T x) (halfLineRightShift_comp_logCellEmbedding hk)
  change halfLineRightShift (Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) (logCellEmbedding x) =
    logCellEmbedding (logCellShift (2 ^ (k + 1)) x) at ht
  have hU : inner ℂ (logCellEmbedding ((W ^ (k + 1)) x)) (logCellEmbedding x) =
      inner ℂ ((W ^ (k + 1)) x) x :=
    LinearIsometry.inner_map_map logCellIsometry _ _
  rw [ht, logCellShift_two_pow_succ, hU]

/-- The literal physical Euler series is absolutely convergent on every complete-cell vector. -/
theorem summable_norm_physicalDyadicEuler_on_cells (x : CellH) :
    Summable (fun k : ℕ => ‖primeTwoPowerWeight k *
      (inner ℂ (halfLineRightShift (Real.log ((2 ^ (k + 1) : ℕ) : ℝ))
        (logCellEmbedding x)) (logCellEmbedding x)).re‖) := by
  refine (summable_norm_dyadicEulerCorrelation x).congr fun k => ?_
  rw [dyadic_power_correlation_eq_physical]

/-- Each arithmetic coefficient reads the literal physical translation, with no substituted source. -/
theorem dyadicEulerCorrelation_eq_physical (x : CellH) :
    dyadicEulerCorrelation x = physicalDyadicEulerCorrelation (logCellEmbedding x) := by
  unfold dyadicEulerCorrelation physicalDyadicEulerCorrelation
  apply tsum_congr
  intro k
  rw [dyadic_power_correlation_eq_physical]

/-- The finite original cell section is exactly recovered from its cell coordinates. -/
theorem logCellEmbedding_cellSection_coordinates (c : ℕ → ℝ) (X : ℕ) :
    logCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X)) = cellSection c 1 X := by
  have he : halfLineExtend (logCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X))) =
      halfLineExtend (cellSection c 1 X) := by
    change wholeLineLogCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X)) = _
    rw [← realSourceLp_wholeCellProfile]
    apply Lp.ext
    exact (realSourceLp_coeFn _ _ _).trans (halfLineExtend_wholeCellProfile c X).symm
  have hr := congrArg halfLineRestrict he
  change (halfLineRestrict ∘L halfLineExtend)
      (logCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X))) =
    (halfLineRestrict ∘L halfLineExtend) (cellSection c 1 X) at hr
  rw [halfLineRestrict_comp_halfLineExtend] at hr
  exact hr

/-- On every finite cell source the full Euler series is the original whole-line correlation integral. -/
theorem physicalDyadicEulerCorrelation_wholeCell (c : ℕ → ℝ) (X : ℕ) :
    physicalDyadicEulerCorrelation (cellSection c 1 X) =
      ∑' k : ℕ, primeTwoPowerWeight k *
        ∫ u, wholeCellProfile c X u *
          wholeCellProfile c X (u + Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) := by
  unfold physicalDyadicEulerCorrelation
  apply tsum_congr
  intro k
  rw [inner_shift_wholeCellProfile]

/-- The original whole-cell Euler integral series is absolutely convergent at every horizon. -/
theorem summable_norm_wholeCell_dyadicEuler_integrals (c : ℕ → ℝ) (X : ℕ) :
    Summable (fun k : ℕ => ‖primeTwoPowerWeight k *
      ∫ u, wholeCellProfile c X u *
        wholeCellProfile c X (u + Real.log ((2 ^ (k + 1) : ℕ) : ℝ))‖) := by
  simpa only [logCellEmbedding_cellSection_coordinates, inner_shift_wholeCellProfile] using
    summable_norm_physicalDyadicEuler_on_cells (logCellEmbedding.adjoint (cellSection c 1 X))

/-- The complete physical prime-two contribution admits a finite-generator approximation across all levels. -/
theorem abs_physicalDyadicEuler_wholeCell_head_error_le (c : ℕ → ℝ) (X : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    |physicalDyadicEulerCorrelation (cellSection c 1 X) -
      physicalDyadicEulerCorrelation (logCellEmbedding (logCellGeneratorHead A
        (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
      primeTwoEulerWeightTotal *
        (32 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ))) := by
  have h := abs_original_cell_dyadicEuler_head_error_le (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  dsimp only at h
  rw [realSourceLp_wholeCellProfile, wholeLineLogCellEmbedding_adjoint_self,
    dyadicEulerCorrelation_eq_physical, dyadicEulerCorrelation_eq_physical,
    logCellEmbedding_cellSection_coordinates] at h
  exact h

/-- A single finite generator family makes the entire physical dyadic Euler error Gamma-small. -/
theorem exists_physicalDyadicEuler_finite_generator_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (c : ℕ → ℝ) (X : ℕ),
      |physicalDyadicEulerCorrelation (cellSection c 1 X) -
        physicalDyadicEulerCorrelation (logCellEmbedding (logCellGeneratorHead A
          (logCellEmbedding.adjoint (cellSection c 1 X))))| ≤
        δ * levyEnergy (wholeCellProfile c X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (primeTwoEulerWeightTotal * 32 / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : primeTwoEulerWeightTotal * 32 / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hden : 0 < 1 + Real.log (A : ℝ) := by
    have h := Real.log_nonneg (by exact_mod_cast hA1 : (1 : ℝ) ≤ A)
    linarith only [h]
  have hcoef : primeTwoEulerWeightTotal * 32 / (1 + Real.log (A : ℝ)) ≤ δ := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_le_iff₀ hδ).mp hlog.le
    nlinarith only [h, hδ]
  refine ⟨A, hA1, fun c X => ?_⟩
  have hE := levyEnergy_nonneg_bv (wholeCellProfile_regular c X).1
    (wholeCellProfile_regular c X).2
  calc
    _ ≤ _ := abs_physicalDyadicEuler_wholeCell_head_error_le c X hA1
    _ = (primeTwoEulerWeightTotal * 32 / (1 + Real.log (A : ℝ))) *
        levyEnergy (wholeCellProfile c X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_dyadicEulerCorrelation
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.dyadicEulerCorrelation_sub_head
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.physicalDyadicEulerCorrelation_wholeCell
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_norm_wholeCell_dyadicEuler_integrals
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.abs_physicalDyadicEuler_wholeCell_head_error_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_physicalDyadicEuler_finite_generator_approximation
