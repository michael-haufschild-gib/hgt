import GaloisForLFunctions.RHTower.GaussDoubleDefectCoefficient
import GaloisForLFunctions.RHTower.GaussCubicOuterDefectSplit

/-!
# Exact three-defect coefficient chain in cubic propagation

The hard cubic contribution is the outer moving-translation defect applied to `B² DD`.  Before the
outer defect is inserted, `B² DD` has one genuine two-index coefficient chain.  Its two ratio
defects become the three factors required by the cubic component law after the outer defect.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussPrimeScaleSqCoeffKernel (p : Nat.Primes) (j l : ℤ) : ℝ :=
  2 * (p : ℝ) ^ 2 / (1 + ((l - j).natAbs : ℝ))

theorem gaussPrimeScaleSqCoeffKernel_nonneg (p : Nat.Primes) (j l : ℤ) :
    0 ≤ gaussPrimeScaleSqCoeffKernel p j l := by
  rw [gaussPrimeScaleSqCoeffKernel]
  positivity

/-- True two-index harmonic kernel of the cubic triple-defect chain. -/
def gaussCubicTripleCoeffKernel (p : Nat.Primes) (j l r : ℤ) : ℝ :=
  gaussPrimeScaleSqCoeffKernel p j l * gaussDoubleDefectCoeffKernel p l r

theorem gaussCubicTripleCoeffKernel_nonneg (p : Nat.Primes) (j l r : ℤ) :
    0 ≤ gaussCubicTripleCoeffKernel p j l r :=
  mul_nonneg (gaussPrimeScaleSqCoeffKernel_nonneg p j l)
    (gaussDoubleDefectCoeffKernel_nonneg p l r)

/-- Coefficientwise ENNReal majorant for `B² DD`, retaining exactly two ratio defects and two
convolution indices. -/
theorem ofReal_norm_fourierCoeff_gaussPrimeScaleSqBlock_doubleDefect_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i j : ℤ) :
    ENNReal.ofReal
        ‖fourierCoeff ((gaussPrimeScaleSqBlock hp
          (gaussDoubleDefectVector hm k p hp i) : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
      ∑' lr : ℤ × ℤ, ENNReal.ofReal
        (gaussCubicTripleCoeffKernel p j lr.1 lr.2 *
          ‖gaussSampleRatioDefect k p lr.1 i‖ *
            ‖gaussSampleRatioDefect k p lr.2 i‖) := by
  set DD : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussDoubleDefectVector hm k p hp i with hDD
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleSqBlock hp DD with hu
  have hconv := norm_fourierCoeff_gaussPrimeScaleSqBlock_le hp DD j
  rw [← hu] at hconv
  have hleft : Summable (fun l : ℤ => gaussPrimeScaleSqCoeffKernel p j l *
      ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) l‖) := by
    exact summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 2 * (p : ℝ) ^ 2 / (1 + (x.natAbs : ℝ)))
      (A := 2 * (p : ℝ) ^ 2) (fun x => by positivity) (fun x => le_rfl) DD j
  have hleftnn : ∀ l : ℤ, 0 ≤ gaussPrimeScaleSqCoeffKernel p j l *
      ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) l‖ := by
    intro l
    exact mul_nonneg (gaussPrimeScaleSqCoeffKernel_nonneg p j l) (norm_nonneg _)
  rw [ENNReal.tsum_prod']
  calc
    ENNReal.ofReal ‖fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ ENNReal.ofReal (∑' l : ℤ, gaussPrimeScaleSqCoeffKernel p j l *
            ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) l‖) := by
          exact ENNReal.ofReal_le_ofReal hconv
    _ = ∑' l : ℤ, ENNReal.ofReal (gaussPrimeScaleSqCoeffKernel p j l *
          ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) l‖) := by
        exact ENNReal.ofReal_tsum_of_nonneg hleftnn hleft
    _ ≤ ∑' l : ℤ, ∑' r : ℤ, ENNReal.ofReal
          (gaussCubicTripleCoeffKernel p j l r *
            ‖gaussSampleRatioDefect k p l i‖ *
              ‖gaussSampleRatioDefect k p r i‖) := by
        refine ENNReal.tsum_le_tsum fun l => ?_
        have hDDcoeff := norm_fourierCoeff_gaussDoubleDefectVector_le hm k p hp i l
        have hreal := mul_le_mul_of_nonneg_left hDDcoeff
          (gaussPrimeScaleSqCoeffKernel_nonneg p j l)
        refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
        have hsum := summable_gaussDoubleDefectCoeffMajorant hm k p i l
        have hsum' : Summable (fun r : ℤ => gaussPrimeScaleSqCoeffKernel p j l *
            (gaussDoubleDefectCoeffKernel p l r *
              ‖gaussSampleRatioDefect k p l i‖ *
                ‖gaussSampleRatioDefect k p r i‖)) :=
          hsum.mul_left _
        have hnn : ∀ r : ℤ, 0 ≤ gaussPrimeScaleSqCoeffKernel p j l *
            (gaussDoubleDefectCoeffKernel p l r *
              ‖gaussSampleRatioDefect k p l i‖ *
                ‖gaussSampleRatioDefect k p r i‖) := by
          intro r
          exact mul_nonneg (gaussPrimeScaleSqCoeffKernel_nonneg p j l)
            (mul_nonneg
              (mul_nonneg (gaussDoubleDefectCoeffKernel_nonneg p l r) (norm_nonneg _))
              (norm_nonneg _))
        rw [← hsum.tsum_mul_left]
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum']
        exact le_of_eq (tsum_congr fun r => by
          congr 1
          rw [gaussCubicTripleCoeffKernel]
          ring)
    _ = ∑' l : ℤ, ∑' r : ℤ, ENNReal.ofReal
          (gaussCubicTripleCoeffKernel p j l r *
            ‖gaussSampleRatioDefect k p l i‖ *
              ‖gaussSampleRatioDefect k p r i‖) := rfl

end

end RHTower
