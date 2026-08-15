import GaloisForLFunctions.RHTower.GaussPrimeScaleSqConvolution

/-!
# Exact split of the cubic outer defect

The literal cubic outer defect is the moving-translation defect applied to `B²` times the exact
three-term relative-error source.  This file exposes those three contributions without estimates:
two contain two sampled-ratio defects, while the middle contribution contains three.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions

noncomputable section

/-- First (unconjugated smooth) source in the exact relative-error decomposition. -/
def gaussCubicFirstSource {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockDiag hm k p i
      (gaussPrimeScaleInvSqBlock hp
        (gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (fourierLp 2 0)))) -
    gaussRotationBlockInv ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleInvSqBlock hp
        (gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (fourierLp 2 0)))
      )

/-- Third (conjugated smooth) source in the exact relative-error decomposition. -/
def gaussCubicThirdSource {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussRotationBlockInv ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
    (gaussPrimeScaleInvSqBlock hp
      (gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
        gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (fourierLp 2 0))))

/-- Moving-translation defect applied after one exact `B²` multiplier. -/
def gaussCubicOuterDefectPart {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp u) -
    gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleSqBlock hp u)

theorem gaussCubicOuterDefectPart_add {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussCubicOuterDefectPart hm k p hp i (u + v) =
      gaussCubicOuterDefectPart hm k p hp i u +
        gaussCubicOuterDefectPart hm k p hp i v := by
  have hshift : gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp (u + v)) =
      gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp u) +
        gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp v) := by
    calc
      gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp (u + v)) =
          gaussShiftedBlockOf hm k p i
            (gaussPrimeScaleSqBlock hp u + gaussPrimeScaleSqBlock hp v) := by rw [map_add]
      _ = gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp u) +
          gaussShiftedBlockOf hm k p i (gaussPrimeScaleSqBlock hp v) := by
        exact map_add (gaussShiftedBlockOfCLM hm k p i) _ _
  simp only [gaussCubicOuterDefectPart]
  rw [hshift, map_add, map_add]
  abel

/-- Literal cubic outer defect split into its two double-defect contributions and its unique
triple-defect contribution. -/
theorem gaussCubicOuterDefectVector_eq_three_parts
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    gaussCubicOuterDefectVector hm k p hp i =
      gaussCubicOuterDefectPart hm k p hp i (gaussCubicFirstSource hm k p hp i) +
        (gaussCubicOuterDefectPart hm k p hp i (gaussDoubleDefectVector hm k p hp i) +
          gaussCubicOuterDefectPart hm k p hp i (gaussCubicThirdSource hm k p hp i)) := by
  rw [gaussCubicOuterDefectVector, gaussPrincipalRelativeErrorVector_eq_three_defects]
  rw [← gaussPrimeScaleSqBlock_apply]
  change gaussCubicOuterDefectPart hm k p hp i
      (gaussCubicFirstSource hm k p hp i +
        (gaussDoubleDefectVector hm k p hp i + gaussCubicThirdSource hm k p hp i)) = _
  rw [gaussCubicOuterDefectPart_add, gaussCubicOuterDefectPart_add]

end

end RHTower
