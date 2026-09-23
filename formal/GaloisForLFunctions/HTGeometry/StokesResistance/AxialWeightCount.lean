import GaloisForLFunctions.HTGeometry.StokesResistance.JetDimension

/-!
# Axial Fourier multiplicities and continuous-axis response count

This module formalizes Moreau's Appendix A axial-weight multiplicities and continuous-axis raw
parameter count. With paper order shifted to `k = n + 3`, zero weight has multiplicity `3n+3`,
middle positive weights have multiplicities `3,6,...,3(n+1)` up to reordering, and top weight has
multiplicity one.

Counting zero weight once and every positive/negative pair twice recovers the full jet dimension.
In the symmetric response, continuous axial invariance keeps a symmetric form on zero weight plus
pairings of opposite nonzero weights, producing the cubic polynomial
`3n³ + 18n² + 30n + 16`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StokesResistance

/-- Multiplicity of axial weight zero at paper order `k = n + 3`. -/
def axialZeroWeightMultiplicity (n : ℕ) : ℕ := 3 * n + 3

/-- Middle positive-weight multiplicities, enumerated increasingly as `3,6,...`. -/
def axialMiddleMultiplicity (j : ℕ) : ℕ := 3 * (j + 1)

/-- Total carrier dimension reconstructed from axial Fourier multiplicities. -/
def axialWeightDimensionCount (n : ℕ) : ℕ :=
  axialZeroWeightMultiplicity n +
    2 * ((∑ j ∈ Finset.range (n + 1), axialMiddleMultiplicity j) + 1)

/-- Moreau's axial multiplicities sum exactly to the retained Stokes-jet dimension. -/
theorem axialWeightDimensionCount_eq_jetDimension (n : ℕ) :
    axialWeightDimensionCount n = jetDimension n := by
  rw [jetDimension_eq]
  induction n with
  | zero => norm_num [axialWeightDimensionCount, axialZeroWeightMultiplicity,
      axialMiddleMultiplicity, Finset.sum_range_succ]
  | succ n ih =>
      rw [axialWeightDimensionCount, Finset.sum_range_succ]
      rw [axialWeightDimensionCount] at ih
      simp only [axialZeroWeightMultiplicity, axialMiddleMultiplicity] at ih ⊢
      ring_nf at ih ⊢
      omega

/-- Raw continuous-axis invariant response count from zero and opposite-weight pairings. -/
def continuousAxialRawParameterCount (n : ℕ) : ℕ :=
  Nat.choose (axialZeroWeightMultiplicity n + 1) 2 +
    (∑ j ∈ Finset.range (n + 1), axialMiddleMultiplicity j ^ (2 : ℕ)) + 1

/-- Advancing zero-weight multiplicity by three adds three Pascal layers to `choose(-,2)`. -/
theorem choose_add_three_two (m : ℕ) :
    Nat.choose (m + 4) 2 = Nat.choose (m + 1) 2 + 3 * m + 6 := by
  have hstep (t : ℕ) : Nat.choose (t + 1) 2 = Nat.choose t 2 + t := by
    rw [Nat.choose_succ_succ']
    simp [Nat.choose_one_right, add_comm]
  rw [show m + 4 = (m + 3) + 1 by omega, hstep]
  rw [show m + 3 = (m + 2) + 1 by omega, hstep]
  rw [show m + 2 = (m + 1) + 1 by omega, hstep]
  omega

/-- Moreau Appendix A: `d_raw(C∞)=3k³-9k²+3k+7`, shifted to `k=n+3`. -/
theorem continuousAxialRawParameterCount_eq (n : ℕ) :
    continuousAxialRawParameterCount n = 3 * n ^ (3 : ℕ) + 18 * n ^ (2 : ℕ) + 30 * n + 16 := by
  induction n with
  | zero => norm_num [continuousAxialRawParameterCount, axialZeroWeightMultiplicity,
      axialMiddleMultiplicity, Finset.sum_range_succ, Nat.choose]
  | succ n ih =>
      rw [continuousAxialRawParameterCount, Finset.sum_range_succ]
      rw [continuousAxialRawParameterCount] at ih
      simp only [axialZeroWeightMultiplicity, axialMiddleMultiplicity] at ih
      change Nat.choose ((3 * n + 3) + 4) 2 +
          ((∑ j ∈ Finset.range (n + 1), (3 * (j + 1)) ^ (2 : ℕ)) +
            (3 * (n + 1 + 1)) ^ (2 : ℕ)) + 1 = _
      rw [choose_add_three_two (3 * n + 3)]
      ring_nf at ih ⊢
      omega

end GaloisForLFunctions.HTGeometry.StokesResistance
