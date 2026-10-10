import GaloisForLFunctions.RHTower.PaperCriticalFeatureEntropy
import GaloisForLFunctions.RHTower.PaperCriticalFeaturePhaseQuantization
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureOffLineAliasBalance

/-!
# Entropy accounting for the literal critical-line Xi packet

The histogram uses actual Xi multiplicities and the native compact cutoff weights.
Zero total mass is handled by the uniform law, with exact zero weighted contribution.
No equidistribution or nonuniformity assumption is introduced.
-/

open GaloisForLFunctions.HTGeometry FourierLLogL
open scoped BigOperators Classical

namespace RHTower

noncomputable section

def paperCriticalFeatureXiLinePacket (n : ℕ) : Finset XiDivisorSupport :=
  (hcfXiSupportPacket n).filter (fun rho : XiDivisorSupport => (rho : ℂ).re = 1 / 2)

def paperCriticalFeatureXiWeight (n : ℕ) (rho : XiDivisorSupport) : ℝ :=
  (xiSupportMultiplicity rho : ℝ) *
    SchwartzMap.realCompactIntervalCutoff (n : ℝ) (rho : ℂ).im

theorem paperCriticalFeatureXiWeight_nonneg (n : ℕ) (rho : XiDivisorSupport) :
    0 ≤ paperCriticalFeatureXiWeight n rho :=
  mul_nonneg (Nat.cast_nonneg _) (SchwartzMap.realCompactIntervalCutoff_nonnegative _ _)

def paperCriticalFeatureXiLineMass (n : ℕ) : ℝ :=
  ∑ rho ∈ paperCriticalFeatureXiLinePacket n, paperCriticalFeatureXiWeight n rho

theorem paperCriticalFeatureXiLineMass_nonneg (n : ℕ) :
    0 ≤ paperCriticalFeatureXiLineMass n :=
  Finset.sum_nonneg fun rho _ => paperCriticalFeatureXiWeight_nonneg n rho

def paperCriticalFeatureXiBinWeight (n N : ℕ) (theta : ℝ) (j : Fin (N + 1)) : ℝ :=
  ∑ rho ∈ paperCriticalFeatureXiLinePacket n,
    if paperCriticalFeaturePhaseBin N ((rho : ℂ).im + theta) = j
      then paperCriticalFeatureXiWeight n rho else 0

theorem paperCriticalFeatureXiBinWeight_nonneg (n N : ℕ) (theta : ℝ) (j : Fin (N + 1)) :
    0 ≤ paperCriticalFeatureXiBinWeight n N theta j := by
  apply Finset.sum_nonneg
  intro rho _
  split_ifs
  · exact paperCriticalFeatureXiWeight_nonneg n rho
  · exact le_rfl

/-- The histogram retains every unit of the literal cutoff-weighted Xi mass. -/
theorem paperCriticalFeatureXiBinWeight_sum (n N : ℕ) (theta : ℝ) :
    ∑ j, paperCriticalFeatureXiBinWeight n N theta j = paperCriticalFeatureXiLineMass n := by
  classical
  unfold paperCriticalFeatureXiBinWeight
  rw [Finset.sum_comm]
  simp [paperCriticalFeatureXiLineMass]

/-- Normalize the actual Xi histogram; the zero-mass convention contributes no source mass. -/
def paperCriticalFeatureXiHistogram (n N : ℕ) (theta : ℝ) : Law (Fin (N + 1)) :=
  if h : 0 < paperCriticalFeatureXiLineMass n then
    Law.proportional (paperCriticalFeatureXiBinWeight n N theta)
      (paperCriticalFeatureXiBinWeight_nonneg n N theta)
      (by rw [paperCriticalFeatureXiBinWeight_sum]; exact h)
  else Law.uniform (Fin (N + 1))

theorem paperCriticalFeatureXiHistogram_mass (n N : ℕ) (theta : ℝ) (j : Fin (N + 1)) :
    paperCriticalFeatureXiLineMass n * paperCriticalFeatureXiHistogram n N theta j =
      paperCriticalFeatureXiBinWeight n N theta j := by
  classical
  by_cases h : 0 < paperCriticalFeatureXiLineMass n
  · rw [paperCriticalFeatureXiHistogram, dif_pos h, Law.proportional_apply,
      paperCriticalFeatureXiBinWeight_sum]
    rw [mul_comm, div_mul_cancel₀ _ h.ne']
  · have hz : paperCriticalFeatureXiLineMass n = 0 :=
      le_antisymm (le_of_not_gt h) (paperCriticalFeatureXiLineMass_nonneg n)
    have hb : paperCriticalFeatureXiBinWeight n N theta j ≤ paperCriticalFeatureXiLineMass n := by
      rw [← paperCriticalFeatureXiBinWeight_sum n N theta]
      exact Finset.single_le_sum
        (fun i _ => paperCriticalFeatureXiBinWeight_nonneg n N theta i) (Finset.mem_univ j)
    rw [hz] at hb ⊢
    rw [zero_mul]
    exact (le_antisymm hb (paperCriticalFeatureXiBinWeight_nonneg n N theta j)).symm

/-- Expected grid reporter is exactly the binned weighted source, including zero total mass. -/
theorem paperCriticalFeatureXiHistogram_alias (n N : ℕ) (theta : ℝ) :
    paperCriticalFeatureXiLineMass n *
        paperCriticalFeatureLawAlias (paperCriticalFeatureXiHistogram n N theta)
          (fun j => uniformNode 0 1 (N + 1) j) =
      ∑ rho ∈ paperCriticalFeatureXiLinePacket n, paperCriticalFeatureXiWeight n rho *
        (criticalFeatureRealBoundaryPeriodization
          (paperCriticalFeaturePhaseNode N ((rho : ℂ).im + theta)) - 2 * Real.pi) := by
  classical
  unfold paperCriticalFeatureLawAlias Law.Ex
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, paperCriticalFeatureXiHistogram_mass]
  unfold paperCriticalFeatureXiBinWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho _
  simp [paperCriticalFeaturePhaseNode]

def paperCriticalFeatureXiQuantizationResidual (n N : ℕ) (theta : ℝ) : ℝ :=
  ∑ rho ∈ paperCriticalFeatureXiLinePacket n, paperCriticalFeatureXiWeight n rho *
    (criticalFeatureRealBoundaryPeriodization ((rho : ℂ).im + theta) -
      criticalFeatureRealBoundaryPeriodization
        (paperCriticalFeaturePhaseNode N ((rho : ℂ).im + theta)))

/-- The physical boundary alias is the histogram reporter plus its exact quantization residual. -/
theorem paperCriticalFeatureXiHistogram_source_decomposition (n N : ℕ) (theta : ℝ) :
    criticalFeatureCompactSourceBoundaryAliasAtPhase n theta =
      paperCriticalFeatureXiLineMass n *
        paperCriticalFeatureLawAlias (paperCriticalFeatureXiHistogram n N theta)
          (fun j => uniformNode 0 1 (N + 1) j) +
        paperCriticalFeatureXiQuantizationResidual n N theta := by
  rw [← hcfXiLineAlias_eq_sourceAlias, paperCriticalFeatureXiHistogram_alias]
  unfold hcfXiLineAlias hcfXiAliasTerm paperCriticalFeatureXiQuantizationResidual
    paperCriticalFeatureXiLinePacket paperCriticalFeatureXiWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _
  ring

/-- Quantization costs at most the literal packet mass times the uniform reporter error. -/
theorem paperCriticalFeatureXiQuantizationResidual_bound (n N : ℕ) (theta : ℝ) :
    |paperCriticalFeatureXiQuantizationResidual n N theta| ≤
      paperCriticalFeatureXiLineMass n * paperCriticalFeatureQuantizationError N := by
  unfold paperCriticalFeatureXiQuantizationResidual
  calc
    _ ≤ ∑ rho ∈ paperCriticalFeatureXiLinePacket n,
        |paperCriticalFeatureXiWeight n rho *
          (criticalFeatureRealBoundaryPeriodization ((rho : ℂ).im + theta) -
            criticalFeatureRealBoundaryPeriodization
              (paperCriticalFeaturePhaseNode N ((rho : ℂ).im + theta)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ rho ∈ paperCriticalFeatureXiLinePacket n,
        paperCriticalFeatureXiWeight n rho * paperCriticalFeatureQuantizationError N := by
      apply Finset.sum_le_sum
      intro rho _
      rw [abs_mul, abs_of_nonneg (paperCriticalFeatureXiWeight_nonneg n rho)]
      exact mul_le_mul_of_nonneg_left
        (paperCriticalFeaturePhaseNode_error_le N ((rho : ℂ).im + theta))
        (paperCriticalFeatureXiWeight_nonneg n rho)
    _ = paperCriticalFeatureXiLineMass n * paperCriticalFeatureQuantizationError N := by
      rw [paperCriticalFeatureXiLineMass, Finset.sum_mul]

/-- Every excess over the uniform-grid source pays histogram entropy deficit and a vanishing
quantization error. All weights and phases come from the actual compact Xi packet. -/
theorem paperCriticalFeatureXiAlias_entropy (n N : ℕ) (theta : ℝ) :
    |criticalFeatureCompactSourceBoundaryAliasAtPhase n theta -
        paperCriticalFeatureXiLineMass n * (criticalFeatureUniformGridAlias (N + 1)).re| ≤
      paperCriticalFeatureXiLineMass n *
        (paperCriticalFeatureQuantizationError N + (37 : ℝ) / 100 *
          Real.sqrt (Real.log ((N + 1 : ℕ) : ℝ) -
            (paperCriticalFeatureXiHistogram n N theta).entropy)) := by
  rw [paperCriticalFeatureXiHistogram_source_decomposition]
  have he : paperCriticalFeatureXiLineMass n *
        paperCriticalFeatureLawAlias (paperCriticalFeatureXiHistogram n N theta)
          (fun j => uniformNode 0 1 (N + 1) j) +
        paperCriticalFeatureXiQuantizationResidual n N theta -
        paperCriticalFeatureXiLineMass n * (criticalFeatureUniformGridAlias (N + 1)).re =
      paperCriticalFeatureXiQuantizationResidual n N theta + paperCriticalFeatureXiLineMass n *
        (paperCriticalFeatureLawAlias (paperCriticalFeatureXiHistogram n N theta)
          (fun j => uniformNode 0 1 (N + 1) j) -
            (criticalFeatureUniformGridAlias (N + 1)).re) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (paperCriticalFeatureXiLineMass_nonneg n), mul_add]
  exact add_le_add (paperCriticalFeatureXiQuantizationResidual_bound n N theta)
    (mul_le_mul_of_nonneg_left
      (paperCriticalFeatureGridAlias_entropy N (paperCriticalFeatureXiHistogram n N theta))
      (paperCriticalFeatureXiLineMass_nonneg n))

end

end RHTower
