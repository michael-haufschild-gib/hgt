import GaloisForLFunctions.RHTower.GaussCubicTripleCoefficient
import GaloisForLFunctions.RHTower.GaussMovingDefectParseval

/-!
# Literal triple-defect energy bound for cubic propagation

Weighted Cauchy--Schwarz collapses the square of the true two-index coefficient convolution without
duplicating its indices.  The resulting bound contains exactly the three squared sampled-ratio
defects controlled by the three-component conservation law.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussCubicTripleKernelMass (p : Nat.Primes) (j : ℤ) : ℝ≥0∞ :=
  ∑' lr : ℤ × ℤ, ENNReal.ofReal (gaussCubicTripleCoeffKernel p j lr.1 lr.2)

/-- Exact lattice majorant for the hard middle contribution of the cubic outer defect. -/
def gaussCubicTripleDefectBound (k : Fin 3) (p : Nat.Primes) (i : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
    gaussCubicTripleKernelMass p j *
      ∑' lr : ℤ × ℤ, ENNReal.ofReal
        (gaussCubicTripleCoeffKernel p j lr.1 lr.2 *
          ‖gaussSampleRatioDefect k p lr.1 i‖ ^ 2 *
            ‖gaussSampleRatioDefect k p lr.2 i‖ ^ 2)

/-- The literal hard cubic vector is dominated by the triple-defect lattice bound. -/
theorem ofReal_norm_gaussCubicOuterDefectPart_doubleDefect_sq_le
    (k : Fin 3) (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ENNReal.ofReal
        (‖gaussCubicOuterDefectPart (by omega : 1 ≤ 3) k p hp i
          (gaussDoubleDefectVector (by omega : 1 ≤ 3) k p hp i)‖ ^ (2 : ℝ)) ≤
      gaussCubicTripleDefectBound k p i := by
  let hm : 1 ≤ 3 := by omega
  change ENNReal.ofReal
      (‖gaussCubicOuterDefectPart hm k p hp i
        (gaussDoubleDefectVector hm k p hp i)‖ ^ (2 : ℝ)) ≤ _
  set DD : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussDoubleDefectVector hm k p hp i with hDD
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleSqBlock hp DD with hu
  have hvec : gaussCubicOuterDefectPart hm k p hp i DD =
      gaussMovingDefectVector hm k p i u := by
    rw [gaussCubicOuterDefectPart, gaussMovingDefectVector, hu]
  rw [hvec,
    ofReal_norm_gaussMovingDefectVector_sq_eq_energy]
  rw [gaussMovingDefectEnergy, gaussCubicTripleDefectBound]
  refine ENNReal.tsum_le_tsum fun j => ?_
  let a : ℤ × ℤ → ℝ := fun lr => gaussCubicTripleCoeffKernel p j lr.1 lr.2
  let x : ℤ × ℤ → ℝ := fun lr =>
    ‖gaussSampleRatioDefect k p lr.1 i‖ * ‖gaussSampleRatioDefect k p lr.2 i‖
  set S : ℝ≥0∞ := ∑' lr : ℤ × ℤ, ENNReal.ofReal (a lr * x lr) with hS
  set A : ℝ≥0∞ := ∑' lr : ℤ × ℤ, ENNReal.ofReal (a lr) with hA
  set B : ℝ≥0∞ := ∑' lr : ℤ × ℤ, ENNReal.ofReal (a lr * x lr ^ 2) with hB
  have hac : ∀ lr, 0 ≤ a lr := fun lr => gaussCubicTripleCoeffKernel_nonneg p j lr.1 lr.2
  have hxc : ∀ lr, 0 ≤ x lr := fun lr => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcoeff : ENNReal.ofReal
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ≤ S := by
    have h := ofReal_norm_fourierCoeff_gaussPrimeScaleSqBlock_doubleDefect_le hm k p hp i j
    rw [← hu] at h
    rw [hS]
    simpa only [a, x, mul_assoc] using h
  have hsq : ENNReal.ofReal
      (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2) ≤ S * S := by
    rw [show ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 =
      ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ *
        ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ by ring,
      ENNReal.ofReal_mul (norm_nonneg _)]
    exact mul_le_mul' hcoeff hcoeff
  have hcs : S * S ≤ A * B := by
    rw [hS, hA, hB]
    exact ennreal_tsum_ofReal_mul_sq_le a x hac hxc
  have hBform : B = ∑' lr : ℤ × ℤ, ENNReal.ofReal
      (gaussCubicTripleCoeffKernel p j lr.1 lr.2 *
        ‖gaussSampleRatioDefect k p lr.1 i‖ ^ 2 *
          ‖gaussSampleRatioDefect k p lr.2 i‖ ^ 2) := by
    rw [hB]
    exact tsum_congr fun lr => by
      congr 1
      simp only [a, x]
      ring
  have hAform : A = gaussCubicTripleKernelMass p j := by
    rw [hA, gaussCubicTripleKernelMass]
  rw [← hAform, ← hBform]
  calc
    ENNReal.ofReal
        (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2 *
          ‖gaussSampleRatioDefect k p j i‖ ^ 2)
        = ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
            ENNReal.ofReal (‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖ ^ 2) := by
          rw [mul_comm, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) * (S * S) :=
      mul_le_mul' le_rfl hsq
    _ ≤ ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) * (A * B) :=
      mul_le_mul' le_rfl hcs
    _ = ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) * A * B := by
      rw [mul_assoc]

end

end RHTower
