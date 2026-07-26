import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform
import GaloisForLFunctions.RHTower.MobiusCriticalFisherLowerBoundaryBudget

/-!
# Squarefree-Möbius finite-Fisher hard-coarea/soft-damping universality

For one finite Fisher pair-amplitude kernel on the squarefree-Möbius critical clock, the global
hard-cut coarea integral is the signed height holonomy and every soft Laplace entry is the exact
difference of the corresponding arithmetic damping coefficients.
-/

open Complex MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squarefree-Möbius critical clock pulled back to an arbitrary finite label family. -/
def squarefreeMobiusFiniteFisherClock
    {ι : Type*} (sigma : ℝ) (label : ι → ℕ) (i : ι) : ℝ :=
  squarefreeMobiusCriticalClock sigma (label i)

/-- Complexified exact lower-corner Fisher pair-amplitude kernel on the physical clock. -/
def squarefreeMobiusFiniteFisherPairKernel
    {ι : Type*} (sigma : ℝ) (label : ι → ℕ)
    (p : ι → ℝ) (center : ℝ) (i j : ι) : ℂ :=
  ((2 * finiteFisherPairAmplitudeSq p
    (squarefreeMobiusFiniteFisherClock sigma label) center i j : ℝ) : ℂ)

/-- At and above the Euler boundary, every natural squarefree-Möbius clock height is
nonnegative. -/
theorem squarefreeMobiusCriticalClock_nonneg_of_one_le
    {sigma : ℝ} (hsigma : 1 ≤ sigma) (n : ℕ) :
    0 ≤ squarefreeMobiusCriticalClock sigma n := by
  rw [squarefreeMobiusCriticalClock]
  apply mul_nonneg (sub_nonneg.mpr hsigma)
  by_cases hn : n = 0
  · simp [hn]
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn

/-- **Squarefree-Möbius finite-Fisher hard-coarea/soft-damping universality.**

The complete hard-cut energy identity and all ordered soft damping identities hold
simultaneously for the same finite non-diagonal Fisher kernel. -/
theorem squarefreeMobiusFiniteFisher_hardCoarea_softDampingUniversality
    {ι : Type*} [Fintype ι]
    (label : ι → ℕ) (p : ι → ℝ) (center : ℝ)
    {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    (∫ u : ℝ in Ioi 0,
        finiteFisherOneCornerCoareaDensity p
          (squarefreeMobiusFiniteFisherClock sigma label) center u) =
        finiteFisherSignedHolonomyEnergy p
          (squarefreeMobiusFiniteFisherClock sigma label) center ∧
      ∀ {u : ℝ}, u ≠ 0 → ∀ i j : ι,
        squarefreeMobiusFiniteFisherClock sigma label j ≤
            squarefreeMobiusFiniteFisherClock sigma label i →
          orientedCutoffLaplaceCoefficient
              (squarefreeMobiusFiniteFisherClock sigma label j)
              (squarefreeMobiusFiniteFisherClock sigma label i)
              (squarefreeMobiusFiniteFisherPairKernel
                sigma label p center i j) (u : ℂ) =
            squarefreeMobiusFiniteFisherPairKernel sigma label p center i j *
              ((Real.exp (-(u * (sigma - 1) * Real.log (label j))) : ℂ) -
                (Real.exp (-(u * (sigma - 1) * Real.log (label i))) : ℂ)) /
                  (u : ℂ) := by
  constructor
  · apply integral_finiteFisherOneCornerCoareaDensity
    intro i
    exact squarefreeMobiusCriticalClock_nonneg_of_one_le hsigma (label i)
  · intro u hu i j hji
    exact
      squarefreeMobiusCriticalClock_orientedCutoffLaplaceCoefficient_eq_dampingDividedDifference
        (sigma := sigma) (u := u) (m := label j) (n := label i)
        (k := squarefreeMobiusFiniteFisherPairKernel sigma label p center i j)
        hu hji

end

end RHTower
