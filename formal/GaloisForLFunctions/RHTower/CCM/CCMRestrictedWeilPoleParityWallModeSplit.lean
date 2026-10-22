import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleWallFieldWeld

/-!
# Exact common-age / relative-clock split of the literal CCM parity walls

The two literal restricted-Weil parity responses do not admit atomwise
positivity.  Their sum is precisely a common hyperbolic age mode, while their
difference is precisely a relative affine clock mode.  This keeps every
critical-Mellin coefficient, prime entry, polar term, and Gamma carrier: it
isolates the two genuinely coupled source channels that any sign producer must
control simultaneously.
-/

open Set MeasureTheory
open scoped BigOperators
noncomputable section

namespace RHTower

/-- Common hyperbolic age mode of one literal two-parity wall response. -/
def ccmWeilWallAgeMode (n : ℕ) (s : ℝ) : ℝ :=
  -16 * Real.sinh (s - Real.log n / 2)

/-- Relative affine clock mode of one literal two-parity wall response. -/
def ccmWeilWallClockMode (n : ℕ) (s : ℝ) : ℝ :=
  16 * (s - Real.log n / 2) * Real.cosh (Real.log n / 2)

/-- The parity sum of a literal wall response is exactly its common age mode. -/
theorem ccmWeilWallResponses_add_eq_ageMode (n : ℕ) (s : ℝ) :
    ccmWeilOddWallEnergyResponse n s + ccmWeilEvenWallEnergyResponse n s =
      ccmWeilWallAgeMode n s := by
  rw [ccmWeilOddWallEnergyResponse_eq_hyperbolic,
    ccmWeilEvenWallEnergyResponse_eq_hyperbolic]
  unfold ccmWeilWallAgeMode
  ring

/-- The parity difference of a literal wall response is exactly its affine clock mode. -/
theorem ccmWeilWallResponses_sub_eq_clockMode (n : ℕ) (s : ℝ) :
    ccmWeilOddWallEnergyResponse n s - ccmWeilEvenWallEnergyResponse n s =
      ccmWeilWallClockMode n s := by
  rw [ccmWeilOddWallEnergyResponse_eq_hyperbolic,
    ccmWeilEvenWallEnergyResponse_eq_hyperbolic]
  unfold ccmWeilWallClockMode
  ring

/-- The common age mode is twice the odd response's exact hyperbolic forcing. -/
theorem ccmWeilWallAgeMode_eq_two_odd_secondDerivative (n : ℕ) (s : ℝ) :
    ccmWeilWallAgeMode n s =
      2 * deriv (deriv (ccmWeilOddWallEnergyResponse n)) s := by
  rw [deriv_deriv_ccmWeilOddWallEnergyResponse]
  unfold ccmWeilWallAgeMode
  ring

/-- Exact source-level split: parity sum retains only the common age mode. -/
theorem ccmWeilParityPole_sum_eq_diagonal_ageModes (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) +
        ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) =
      4 * ccmWeilPoleDiagonalSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilWallAgeMode n a.1 := by
  rw [ccmWeilOddPole_eq_criticalMellinWallEnergySuperposition,
    ccmWeilEvenPole_eq_criticalMellinWallEnergySuperposition]
  calc
    (2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n a.1) +
        (2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) +
          ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
            criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1) =
      4 * ccmWeilPoleDiagonalSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n a.1 +
            criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = _ := by
      refine congrArg (fun z : ℝ => 4 * ccmWeilPoleDiagonalSmooth a.1 + z) ?_
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_add, ccmWeilWallResponses_add_eq_ageMode]

/-- Exact source-level split: parity difference retains only the relative clock mode. -/
theorem ccmWeilParityPole_sub_eq_cross_clockModes (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) -
        ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) =
      -4 * ccmWeilPoleCrossSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilWallClockMode n a.1 := by
  rw [ccmWeilOddPole_eq_criticalMellinWallEnergySuperposition,
    ccmWeilEvenPole_eq_criticalMellinWallEnergySuperposition]
  calc
    (2 * (ccmWeilPoleDiagonalSmooth a.1 - ccmWeilPoleCrossSmooth a.1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n a.1) -
        (2 * (ccmWeilPoleDiagonalSmooth a.1 + ccmWeilPoleCrossSmooth a.1) +
          ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
            criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1) =
      -4 * ccmWeilPoleCrossSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (criticalMellinAtomWeight n * ccmWeilOddWallEnergyResponse n a.1 -
            criticalMellinAtomWeight n * ccmWeilEvenWallEnergyResponse n a.1) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = _ := by
      refine congrArg (fun z : ℝ => -4 * ccmWeilPoleCrossSmooth a.1 + z) ?_
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_sub, ccmWeilWallResponses_sub_eq_clockMode]

/-- Exact real two-channel criterion: two energies are nonnegative precisely
when their relative channel is bounded by their common channel. -/
theorem ccmWeilParityPair_nonneg_iff_abs_sub_le_add (x y : ℝ) :
    (0 ≤ x ∧ 0 ≤ y) ↔ |x - y| ≤ x + y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro h
    obtain ⟨hlo, hhi⟩ := abs_le.mp h
    constructor <;> linarith

/-- The two literal parity tests are exactly one coupled common-age versus
relative-clock inequality, with all finite arithmetic coefficients retained. -/
theorem ccmWeilParityPole_nonneg_iff_wallModeBound (a : SuzukiPositiveAperture) :
    (0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1)) ↔
    |(-4 * ccmWeilPoleCrossSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilWallClockMode n a.1)| ≤
      4 * ccmWeilPoleDiagonalSmooth a.1 +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          criticalMellinAtomWeight n * ccmWeilWallAgeMode n a.1 := by
  rw [ccmWeilParityPair_nonneg_iff_abs_sub_le_add,
    ccmWeilParityPole_sub_eq_cross_clockModes,
    ccmWeilParityPole_sum_eq_diagonal_ageModes]

end RHTower
