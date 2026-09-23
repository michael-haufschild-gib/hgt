import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import GaloisForLFunctions.RHTower.CCMRectangularFullObservableDivisorTomography

/-!
# Rectangular tomography is a Gamma/co-Poisson interval cell

The Laplace amplitude used by cutoff-free rectangular Xi-divisor tomography is
exactly one specialization of the signed Gamma/co-Poisson interval cell:

`A_L(w) = Θ_L(1 / 2, 1 / 2 - w)`.

Consequently the already-proved tomography residue is a
multiplicity-weighted square of that cell.  This supplies an exact bridge
between the two corpus constructions; it does not construct the signed
dagger-compatible boundary comparison needed for an RH implication.
-/

open Complex

namespace RHTower

noncomputable section

/-- The rectangular Laplace window is the Gamma/co-Poisson interval cell with
one endpoint fixed at the half-density character.  The equality includes the
removable value at `w = 0`. -/
theorem rectangularWindowAmplitude_eq_gammaCoPoissonIntervalCell
    (L : ℝ) (w : ℂ) :
    rectangularWindowAmplitude L w =
      gammaCoPoissonIntervalCell (L : ℂ) (1 / 2) (1 / 2 - w) := by
  by_cases hw : w = 0
  · subst w
    simp only [sub_zero]
    rw [rectangularWindowAmplitude_zero,
      gammaCoPoissonIntervalCell_self]
    simp
  · rw [rectangularWindowAmplitude_eq_div hw,
      gammaCoPoissonIntervalCell_eq_dividedDifference]
    · congr 1
      · rw [show ((1 / 2 : ℂ) - 1 / 2) * (L : ℂ) = 0 by ring,
          Complex.exp_zero]
        congr 1
        congr 1
        ring
      · ring
    · intro h
      apply hw
      linear_combination h

/-- Every fixed-width right-divisor coefficient is the square of the same
signed Gamma/co-Poisson interval cell. -/
theorem xiRectangularRightCoefficient_eq_gammaCoPoissonIntervalCell_sq
    (L : ℝ) (q : XiRightZeroCopy) :
    xiRectangularRightCoefficient L q =
      gammaCoPoissonIntervalCell (L : ℂ) (1 / 2)
        (1 / 2 - xiRightCenteredZero q) ^ (2 : ℕ) := by
  rw [xiRectangularRightCoefficient,
    rectangularWindowAmplitude_eq_gammaCoPoissonIntervalCell]

/-- The cutoff-free tomography pole carries exactly twice the analytic
multiplicity times the square of the corresponding Gamma/co-Poisson cell. -/
theorem
    meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation_eq_gammaCell
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
        (xiRightShiftedPole q) =
      2 * (xiRightMultiplicity q : ℂ) *
        gammaCoPoissonIntervalCell (L : ℂ) (1 / 2)
          (1 / 2 - xiRightCenteredZero q) ^ (2 : ℕ) := by
  rw [meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation hL,
    xiRectangularRightCoefficient_eq_gammaCoPoissonIntervalCell_sq]

end

end RHTower
