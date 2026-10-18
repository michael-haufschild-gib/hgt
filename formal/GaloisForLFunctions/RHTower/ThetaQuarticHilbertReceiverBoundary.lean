import GaloisForLFunctions.HTGeometry.SourcePairPositiveQuarticGradedRealification
import Mathlib.Analysis.InnerProductSpace.PiL2
import GaloisForLFunctions.RHTower.PaperThetaSchurModeCharge

/-!
# The exact Hilbert receiver and linear boundary for native quartic charge

The actual theta Schur-mode charge has a two-coordinate quadratic feature map.
Its squared Hilbert norm is exact, while degree-four scaling forbids any linear
norm-square realization on the original degree-one source coordinates.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The native quartic charge has degree four, so no linear norm-square realization exists. -/
theorem no_linear_norm_sq_sourcePairPositiveQuarticCharge
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :
    ¬ ∃ T : (ℝ × ℝ) →ₗ[ℝ] H,
      ∀ a b, ‖T (a, b)‖ ^ 2 = sourcePairPositiveQuarticCharge a b := by
  rintro ⟨T, hT⟩
  have h₁ := hT 0 1
  have h₂ := hT 0 2
  have hscale : T (0, 2) = (2 : ℝ) • T (0, 1) := by
    rw [← map_smul]
    congr 1
    ext <;> norm_num
  rw [hscale, norm_smul, Real.norm_of_nonneg (by norm_num)] at h₂
  norm_num [sourcePairPositiveQuarticCharge] at h₁ h₂
  nlinarith

/-- Exact nonlinear two-coordinate receiver of the actual quartic charge. -/
def sourcePairQuarticFeature (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![10 * Real.sqrt 6 * a * b, 10 * Real.sqrt 23 * b ^ 2]

theorem sourcePairQuarticFeature_norm_sq (a b : ℝ) :
    ‖sourcePairQuarticFeature a b‖ ^ 2 = sourcePairPositiveQuarticCharge a b := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change (10 * Real.sqrt 6 * a * b) ^ 2 + (10 * Real.sqrt 23 * b ^ 2) ^ 2 = _
  unfold sourcePairPositiveQuarticCharge
  simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
    Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)]
  ring

theorem sourcePairQuarticFeature_homogeneous (c a b : ℝ) :
    sourcePairQuarticFeature (c * a) (c * b) = c ^ 2 • sourcePairQuarticFeature a b := by
  ext k
  fin_cases k <;> simp [sourcePairQuarticFeature] <;> ring

theorem sourcePairQuarticFeature_eq_zero_iff (a b : ℝ) :
    sourcePairQuarticFeature a b = 0 ↔ b = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, sourcePairQuarticFeature_norm_sq,
    sourcePairPositiveQuarticCharge_eq_zero_iff]

theorem finite_sourcePairQuarticFeature_norm_sq {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, ‖sourcePairQuarticFeature (a i) (b i)‖ ^ 2) =
      ∑ i ∈ s, sourcePairPositiveQuarticCharge (a i) (b i) := by
  apply Finset.sum_congr rfl
  intro i _
  exact sourcePairQuarticFeature_norm_sq _ _

end GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource
open GaloisForLFunctions.HTGeometry

def paperThetaSchurModeFeature (S : PaperThetaSchurFamily) (p : PaperThetaSchurMode) :
    EuclideanSpace ℝ (Fin 2) :=
  sourcePairQuarticFeature ((S p.1).T p.2 p.2).re ((S p.1).T p.2 p.2).im

theorem paperThetaSchurModeFeature_norm_sq (S : PaperThetaSchurFamily) (p : PaperThetaSchurMode) :
    ‖paperThetaSchurModeFeature S p‖ ^ 2 = paperThetaSchurModeCharge S p :=
  sourcePairQuarticFeature_norm_sq _ _

theorem paperThetaSchurModeFeature_total (S : PaperThetaSchurFamily) (k : ℕ) :
    (∑ i, ‖paperThetaSchurModeFeature S ⟨k, i⟩‖ ^ 2) =
      thetaSourceStageSchurPositiveQuarticCharge (S k) := by
  simp_rw [paperThetaSchurModeFeature_norm_sq]
  exact sum_paperThetaSchurModeCharge S k

end RHTower.HedenmalmThetaSource

end
