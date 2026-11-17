import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClipping
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Composition of symmetric spectral cutoffs

Scalar clipping composes by taking the smaller cap. Continuous functional
calculus transfers this law to Hermitian matrices independently of the
eigenbases chosen for their separate spectral decompositions.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping

/-- Successive interval projections retain the smaller radius. -/
theorem clip_comp (c d : ℝ≥0) (x : ℝ) : clip d (clip c x) = clip (min c d) x := by
  by_cases hcd : c ≤ d
  · rw [min_eq_left hcd]
    apply clip_of_abs_le
    exact (abs_le.mpr (clip_bounds c x)).trans hcd
  · have hdcNN : d ≤ c := le_of_lt (lt_of_not_ge hcd)
    have hdc : (d : ℝ) ≤ c := hdcNN
    rw [min_eq_right hdcNN]
    rcases le_total x (-(d : ℝ)) with hx | hx
    · have hcx : clip c x ≤ -(d : ℝ) := by
        apply max_le
        · exact neg_le_neg hdc
        · exact (min_le_left _ _).trans hx
      rw [clip_of_le_neg d hx, clip_of_le_neg d hcx]
    · rcases le_total x (d : ℝ) with hx' | hx'
      · rw [clip_of_abs_le c ((abs_le.mpr ⟨hx, hx'⟩).trans hdc)]
      · have hcx : (d : ℝ) ≤ clip c x :=
          le_max_of_le_right (le_min hx' hdc)
        rw [clip_of_ge d hx', clip_of_ge d hcx]

/-- Clipping is continuous as a scalar spectral function. -/
theorem continuous_clip (c : ℝ≥0) : Continuous (clip c) :=
  continuous_const.max (continuous_id.min continuous_const)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matrix_eq_cfc {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    matrix hA c = cfc (clip c) A := by
  rw [hA.cfc_eq]
  rfl

/-- Repeated spectral clipping is exactly one clipping at the smaller cap, independently of eigenbasis choices. -/
theorem matrix_comp {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c d : ℝ≥0) :
    matrix (matrix_hermitian hA c) d = matrix hA (min c d) := by
  rw [matrix_eq_cfc, matrix_eq_cfc, matrix_eq_cfc,
    ← cfc_comp (clip d) (clip c) A hA.isSelfAdjoint
      (continuous_clip d).continuousOn (continuous_clip c).continuousOn]
  congr 1
  funext x
  exact clip_comp c d x

/-- The matrix projection is idempotent, including at zero cap. -/
theorem matrix_idempotent {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0) :
    matrix (matrix_hermitian hA c) c = matrix hA c := by
  simpa only [min_self] using matrix_comp hA c c

/-- Caps commute even though their separate spectral decompositions may differ. -/
theorem matrix_caps_commute {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (c d : ℝ≥0) :
    matrix (matrix_hermitian hA c) d = matrix (matrix_hermitian hA d) c := by
  rw [matrix_comp, matrix_comp, min_comm]

#print axioms matrix_comp
#print axioms matrix_idempotent
end GaloisForLFunctions.HilbertMetric.SymmetricClipping
