import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowMatrix
import Mathlib.Analysis.Matrix.Order

/-!
Exact support information retained by scalar and tensor spectral observations.
Following the invariant-menu viewpoint of Gomes, arXiv:2607.24901v1, positivity
makes a window's invisible states exactly its tensor kernel. All diagonal basis
observations, or their single trace sum, detect precisely the zero-window tensor.
-/
open scoped Matrix BigOperators ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- Finite spectral mass vanishes exactly when its real observation vanishes. -/
theorem gomesFockWindowMass_zero_iff_measure_zero {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S x = 0 ↔ gomesFockSpectralMeasure B x S = 0 := by
  unfold gomesFockWindowMass
  rw [ENNReal.toReal_eq_zero_iff]
  exact or_iff_left (measure_ne_top _ _)

/-- Invisible states of a spectral window are exactly the kernel of its reconstructed tensor. -/
theorem gomesFockWindowMass_zero_iff_kernel {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    gomesFockWindowMass B S x = 0 ↔ gomesFockWindowMatrix B S*ᵥx = 0 := by
  have h := (gomesFockWindowMatrix_posSemidef B S).dotProduct_mulVec_zero_iff x
  rw [gomesFockWindowMatrix_quadratic,Complex.ofReal_eq_zero] at h
  exact h

/-- Zero spectral measure of a window is equivalent to tensor annihilation of that state. -/
theorem gomesFockSpectralMeasure_window_zero_iff_kernel {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    gomesFockSpectralMeasure B x S = 0 ↔ gomesFockWindowMatrix B S*ᵥx = 0 := by
  rw [← gomesFockWindowMass_zero_iff_measure_zero,gomesFockWindowMass_zero_iff_kernel]

/-- A window tensor vanishes exactly when every internal-state spectral observation vanishes there. -/
theorem gomesFockWindowMatrix_zero_iff_all_states {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix B S = 0 ↔ ∀ x, gomesFockSpectralMeasure B x S = 0 := by
  constructor
  · intro h x
    apply (gomesFockSpectralMeasure_window_zero_iff_kernel B S x).mpr
    simp [h]
  · intro h
    apply matrix_eq_of_quadraticForm_eq
    intro x
    rw [gomesFockWindowMatrix_quadratic]
    have hz := (gomesFockWindowMass_zero_iff_measure_zero B S x).mpr (h x)
    simp [hz]

/-- Diagonal basis-state observations already detect whether the whole spectral window tensor is zero. -/
theorem gomesFockWindowMatrix_zero_iff_basis_states {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    gomesFockWindowMatrix B S = 0 ↔
      ∀ i : Fin (d+1), gomesFockSpectralMeasure B (freeFockInternalBasis i) S = 0 := by
  constructor
  · intro h i
    exact (gomesFockWindowMatrix_zero_iff_all_states B S).mp h _
  · intro h
    funext i j
    have hj := (gomesFockSpectralMeasure_window_zero_iff_kernel B S (freeFockInternalBasis j)).mp (h j)
    have hij := congrFun hj i
    simpa [freeFockInternalBasis,Matrix.mulVec_single_one] using hij

/-- The window trace is exactly the sum of its nonnegative diagonal basis-state masses. -/
theorem gomesFockWindowMatrix_trace {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockWindowMatrix B S).trace =
      ((∑ i : Fin (d+1), gomesFockWindowMass B S (freeFockInternalBasis i) : ℝ) : ℂ) := by
  change (∑ i, gomesFockWindowMatrix B S i i) = _
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := gomesFockWindowMatrix_quadratic B S (freeFockInternalBasis i)
  simpa [freeFockInternalBasis,Pi.star_single,Matrix.mulVec_single_one] using h

/-- A single trace observation detects exactly whether a positive spectral-window tensor vanishes. -/
theorem gomesFockWindowMatrix_trace_zero_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockWindowMatrix B S).trace = 0 ↔ gomesFockWindowMatrix B S = 0 := by
  rw [gomesFockWindowMatrix_trace,Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun i hi => gomesFockWindowMass_nonneg B S (freeFockInternalBasis i))]
  simpa only [Finset.mem_univ,true_implies,gomesFockWindowMass_zero_iff_measure_zero] using
    (gomesFockWindowMatrix_zero_iff_basis_states B S).symm

end GaloisForLFunctions.HTGeometry
