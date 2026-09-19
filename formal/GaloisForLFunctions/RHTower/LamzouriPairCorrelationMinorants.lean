import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.RHTower.AtlasBlindToUnfolded

/-!
# Affine minorants of finite pair correlation

The finite pair-correlation form is the squared Euclidean norm of its cosine
and sine Fourier coordinates.  Applying the tangent-line inequality for a
square from Lamzouri's Hilbert-space argument gives a lower bound for every
coordinate, and more generally for every rotated Fourier coordinate.

These inequalities are unconditional and retain arbitrary real weights.
-/

open Finset
open scoped BigOperators

namespace RHTower

/-- Pair correlation dominates every affine minorant of its cosine Fourier
coordinate. -/
theorem pair_correlation_cosine_affine_minorant {n : ℕ}
    (w gamma : Fin n → ℝ) (alpha t : ℝ) :
    2 * t * (∑ j, w j * Real.cos (alpha * gamma j)) - t ^ 2 ≤
      ∑ j, ∑ k, w j * w k *
        Real.cos (alpha * (gamma j - gamma k)) := by
  rw [pair_correlation_eq_squares]
  have h :=
    GaloisForLFunctions.HilbertMetric.lamzouriQuadratic_affineMinorant
      (∑ j, w j * Real.cos (alpha * gamma j)) t
  nlinarith [sq_nonneg (∑ j, w j * Real.sin (alpha * gamma j))]

/-- Pair correlation dominates every affine minorant of its sine Fourier
coordinate. -/
theorem pair_correlation_sine_affine_minorant {n : ℕ}
    (w gamma : Fin n → ℝ) (alpha t : ℝ) :
    2 * t * (∑ j, w j * Real.sin (alpha * gamma j)) - t ^ 2 ≤
      ∑ j, ∑ k, w j * w k *
        Real.cos (alpha * (gamma j - gamma k)) := by
  rw [pair_correlation_eq_squares]
  have h :=
    GaloisForLFunctions.HilbertMetric.lamzouriQuadratic_affineMinorant
      (∑ j, w j * Real.sin (alpha * gamma j)) t
  nlinarith [sq_nonneg (∑ j, w j * Real.cos (alpha * gamma j))]

/-- Pair correlation dominates every affine minorant of every rotated
Fourier coordinate.  This packages the cosine and sine estimates as a
direction-free two-dimensional Bessel bound. -/
theorem pair_correlation_rotated_affine_minorant {n : ℕ}
    (w gamma : Fin n → ℝ) (alpha theta t : ℝ) :
    2 * t *
        (Real.cos theta * (∑ j, w j * Real.cos (alpha * gamma j)) +
          Real.sin theta * (∑ j, w j * Real.sin (alpha * gamma j))) -
        t ^ 2 ≤
      ∑ j, ∑ k, w j * w k *
        Real.cos (alpha * (gamma j - gamma k)) := by
  rw [pair_correlation_eq_squares]
  let x := ∑ j, w j * Real.cos (alpha * gamma j)
  let y := ∑ j, w j * Real.sin (alpha * gamma j)
  let p := Real.cos theta * x + Real.sin theta * y
  have ha :=
    GaloisForLFunctions.HilbertMetric.lamzouriQuadratic_affineMinorant p t
  have hunit := Real.cos_sq_add_sin_sq theta
  have horth := sq_nonneg (Real.sin theta * x - Real.cos theta * y)
  dsimp only [p, x, y] at ha horth ⊢
  nlinarith

end RHTower
