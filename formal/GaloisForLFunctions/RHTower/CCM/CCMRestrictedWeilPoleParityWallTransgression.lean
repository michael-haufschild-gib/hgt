import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleParityWallModeSplit

/-!
# Coefficient-faithful parity-wall transgression

The common-age and relative-clock channels of the literal restricted-Weil
pole source are not independent.  One covariant first-order combination
cancels every finite critical-Mellin atom exactly.  The remainder is the
completed polar--Gamma smooth source, with no coefficient discarded.

This is an identity, not a positivity assertion: a sign or coercivity law for
the remaining common-age channel is still the RH-bearing problem.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

namespace RHTower

/-- Finite common-age channel, retaining the full completed smooth diagonal. -/
def ccmWeilParityAgeHead (S : Finset ℕ) (s : ℝ) : ℝ :=
  4 * ccmWeilPoleDiagonalSmooth s +
    ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s

/-- Finite relative-clock channel, retaining the full completed smooth cross term. -/
def ccmWeilParityClockHead (S : Finset ℕ) (s : ℝ) : ℝ :=
  -4 * ccmWeilPoleCrossSmooth s +
    ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallClockMode n s

/-- Literal local slope of the completed diagonal smooth source. -/
def ccmWeilPoleDiagonalSmoothSlope (s : ℝ) : ℝ :=
  2 * (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.cosh s -
    Real.exp s + (1 - 2 * s) * Real.exp (-s) +
    8 * Real.sinh s + 8 * s * Real.cosh s + ccmGammaPoleSelfBoundarySlope s

/-- Literal local slope of the completed cross smooth source. -/
def ccmWeilPoleCrossSmoothSlope (s : ℝ) : ℝ :=
  2 * (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) + 4 * s +
    8 * Real.sinh s * Real.cosh s + 2 * ccmGammaPoleBoundaryLog (2 * s)

/-- The common-age atom has its exact hyperbolic slope. -/
theorem hasDerivAt_ccmWeilWallAgeMode (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilWallAgeMode n)
      (-16 * Real.cosh (s - Real.log n / 2)) s := by
  have h := (((hasDerivAt_id s).sub_const (Real.log n / 2)).sinh).const_mul (-16)
  have hf : ccmWeilWallAgeMode n = fun y =>
      -16 * Real.sinh (y - Real.log n / 2) := by
    funext y
    unfold ccmWeilWallAgeMode
    ring
  rw [hf]
  simpa only [id_eq, mul_one] using h

/-- The relative-clock atom has its exact constant slope. -/
theorem hasDerivAt_ccmWeilWallClockMode (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilWallClockMode n)
      (16 * Real.cosh (Real.log n / 2)) s := by
  have h := ((hasDerivAt_id s).sub_const (Real.log n / 2)).mul_const
    (16 * Real.cosh (Real.log n / 2))
  have hf : ccmWeilWallClockMode n = fun y =>
      (y - Real.log n / 2) * (16 * Real.cosh (Real.log n / 2)) := by
    funext y
    unfold ccmWeilWallClockMode
    ring
  rw [hf]
  simpa only [id_eq, one_mul] using h

/-- **Atomic covariant cancellation.**  The literal clock atom is exactly
annihilated by the common-age transport connection. -/
theorem ccmWeilWallModeTransgression_atom (n : ℕ) (s : ℝ) :
    deriv (ccmWeilWallClockMode n) s +
      Real.cosh s * deriv (ccmWeilWallAgeMode n) s -
        Real.sinh s * ccmWeilWallAgeMode n s = 0 := by
  rw [(hasDerivAt_ccmWeilWallClockMode n s).deriv,
    (hasDerivAt_ccmWeilWallAgeMode n s).deriv]
  unfold ccmWeilWallAgeMode
  have hcosh : Real.cosh s * Real.cosh (s - Real.log n / 2) -
      Real.sinh s * Real.sinh (s - Real.log n / 2) =
      Real.cosh (Real.log n / 2) := by
    rw [← Real.cosh_sub]
    congr 1
    ring
  calc
    16 * Real.cosh (Real.log n / 2) +
        Real.cosh s * (-16 * Real.cosh (s - Real.log n / 2)) -
        Real.sinh s * (-16 * Real.sinh (s - Real.log n / 2)) =
      16 * (Real.cosh (Real.log n / 2) -
        (Real.cosh s * Real.cosh (s - Real.log n / 2) -
          Real.sinh s * Real.sinh (s - Real.log n / 2))) := by ring
    _ = 0 := by rw [hcosh]; ring

/-- The completed diagonal smooth source has its literal polar--Gamma slope. -/
theorem hasDerivAt_ccmWeilPoleDiagonalSmooth
    (a : SuzukiPositiveAperture) :
    HasDerivAt ccmWeilPoleDiagonalSmooth
      (ccmWeilPoleDiagonalSmoothSlope a.1) a.1 := by
  unfold ccmWeilPoleDiagonalSmooth ccmWeilPoleDiagonalSmoothSlope
  have hm : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-a.1)) a.1 := by
    simpa only [Pi.neg_apply, id_eq, mul_neg_one] using! (hasDerivAt_id a.1).neg.exp
  convert! (((((Real.hasDerivAt_sinh a.1).const_mul
      (2 * (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)))).sub
    (Real.hasDerivAt_exp a.1)).add
    ((((hasDerivAt_id a.1).const_mul 2).add_const 1).mul hm)).add
    (((hasDerivAt_id a.1).const_mul 8).mul (Real.hasDerivAt_sinh a.1))).add
    (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive a.2) using 1
  simp only [id_eq]
  ring

/-- The completed cross smooth source has its literal polar--Gamma slope. -/
theorem hasDerivAt_ccmWeilPoleCrossSmooth
    (a : SuzukiPositiveAperture) :
    HasDerivAt ccmWeilPoleCrossSmooth
      (ccmWeilPoleCrossSmoothSlope a.1) a.1 := by
  unfold ccmWeilPoleCrossSmooth ccmWeilPoleCrossSmoothSlope
  convert! (((((hasDerivAt_id a.1).const_mul
      (2 * (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)))).add
    ((hasDerivAt_id a.1).pow 2 |>.const_mul 2)).add
    ((Real.hasDerivAt_sinh a.1).const_mul 2 |>.pow 2)).add
    (hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive a.2)) using 1
  · ext s
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- The common-age finite head has its exact completed slope. -/
theorem hasDerivAt_ccmWeilParityAgeHead
    (S : Finset ℕ) (a : SuzukiPositiveAperture) :
    HasDerivAt (ccmWeilParityAgeHead S)
      (4 * ccmWeilPoleDiagonalSmoothSlope a.1 +
        ∑ n ∈ S, criticalMellinAtomWeight n *
          (-16 * Real.cosh (a.1 - Real.log n / 2))) a.1 := by
  have hD : HasDerivAt (fun s => 4 * ccmWeilPoleDiagonalSmooth s)
      (4 * ccmWeilPoleDiagonalSmoothSlope a.1) a.1 := by
    simpa only [mul_comm] using (hasDerivAt_ccmWeilPoleDiagonalSmooth a).const_mul 4
  have hsumRaw := HasDerivAt.fun_sum fun n (_ : n ∈ S) =>
    (hasDerivAt_ccmWeilWallAgeMode n a.1).const_mul (criticalMellinAtomWeight n)
  have hsum : HasDerivAt (fun s => ∑ n ∈ S, criticalMellinAtomWeight n *
      ccmWeilWallAgeMode n s) (∑ n ∈ S, criticalMellinAtomWeight n *
        (-16 * Real.cosh (a.1 - Real.log n / 2))) a.1 := by
    simpa only [mul_comm] using hsumRaw
  change HasDerivAt (fun s : ℝ => 4 * ccmWeilPoleDiagonalSmooth s +
      ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallAgeMode n s)
    (4 * ccmWeilPoleDiagonalSmoothSlope a.1 + ∑ n ∈ S,
      criticalMellinAtomWeight n * (-16 * Real.cosh (a.1 - Real.log n / 2))) a.1
  exact hD.add hsum

/-- The relative-clock finite head has its exact completed slope. -/
theorem hasDerivAt_ccmWeilParityClockHead
    (S : Finset ℕ) (a : SuzukiPositiveAperture) :
    HasDerivAt (ccmWeilParityClockHead S)
      (-4 * ccmWeilPoleCrossSmoothSlope a.1 +
        ∑ n ∈ S, criticalMellinAtomWeight n *
          (16 * Real.cosh (Real.log n / 2))) a.1 := by
  have hC : HasDerivAt (fun s => -4 * ccmWeilPoleCrossSmooth s)
      (-4 * ccmWeilPoleCrossSmoothSlope a.1) a.1 := by
    simpa only [mul_comm] using (hasDerivAt_ccmWeilPoleCrossSmooth a).const_mul (-4)
  have hsumRaw := HasDerivAt.fun_sum fun n (_ : n ∈ S) =>
    (hasDerivAt_ccmWeilWallClockMode n a.1).const_mul (criticalMellinAtomWeight n)
  have hsum : HasDerivAt (fun s => ∑ n ∈ S, criticalMellinAtomWeight n *
      ccmWeilWallClockMode n s) (∑ n ∈ S, criticalMellinAtomWeight n *
        (16 * Real.cosh (Real.log n / 2))) a.1 := by
    simpa only [mul_comm] using hsumRaw
  change HasDerivAt (fun s : ℝ => -4 * ccmWeilPoleCrossSmooth s +
      ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallClockMode n s)
    (-4 * ccmWeilPoleCrossSmoothSlope a.1 + ∑ n ∈ S,
      criticalMellinAtomWeight n * (16 * Real.cosh (Real.log n / 2))) a.1
  exact hC.add hsum

/-- **Completed finite-head transgression.**  Every arithmetic atom cancels from
the covariant clock derivative.  The right side is entirely the literal
polar--Gamma smooth forcing. -/
theorem ccmWeilParityHeadTransgression
    (S : Finset ℕ) (a : SuzukiPositiveAperture) :
    deriv (ccmWeilParityClockHead S) a.1 +
        Real.cosh a.1 * deriv (ccmWeilParityAgeHead S) a.1 -
          Real.sinh a.1 * ccmWeilParityAgeHead S a.1 =
      -4 * ccmWeilPoleCrossSmoothSlope a.1 +
        4 * Real.cosh a.1 * ccmWeilPoleDiagonalSmoothSlope a.1 -
          4 * Real.sinh a.1 * ccmWeilPoleDiagonalSmooth a.1 := by
  rw [(hasDerivAt_ccmWeilParityClockHead S a).deriv,
    (hasDerivAt_ccmWeilParityAgeHead S a).deriv]
  unfold ccmWeilParityAgeHead
  have hsum : ∑ n ∈ S, criticalMellinAtomWeight n *
      (16 * Real.cosh (Real.log n / 2) +
        Real.cosh a.1 * (-16 * Real.cosh (a.1 - Real.log n / 2)) -
          Real.sinh a.1 * ccmWeilWallAgeMode n a.1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [mul_eq_zero]
    right
    rw [show 16 * Real.cosh (Real.log n / 2) +
        Real.cosh a.1 * (-16 * Real.cosh (a.1 - Real.log n / 2)) -
          Real.sinh a.1 * ccmWeilWallAgeMode n a.1 =
        deriv (ccmWeilWallClockMode n) a.1 +
          Real.cosh a.1 * deriv (ccmWeilWallAgeMode n) a.1 -
            Real.sinh a.1 * ccmWeilWallAgeMode n a.1 by
      rw [(hasDerivAt_ccmWeilWallClockMode n a.1).deriv,
        (hasDerivAt_ccmWeilWallAgeMode n a.1).deriv]]
    exact ccmWeilWallModeTransgression_atom n a.1
  have hcombine :
      (∑ n ∈ S, criticalMellinAtomWeight n * (16 * Real.cosh (Real.log n / 2))) +
        Real.cosh a.1 * (∑ n ∈ S, criticalMellinAtomWeight n *
          (-16 * Real.cosh (a.1 - Real.log n / 2))) -
        Real.sinh a.1 * (∑ n ∈ S, criticalMellinAtomWeight n *
          ccmWeilWallAgeMode n a.1) =
      ∑ n ∈ S, criticalMellinAtomWeight n *
        (16 * Real.cosh (Real.log n / 2) +
          Real.cosh a.1 * (-16 * Real.cosh (a.1 - Real.log n / 2)) -
            Real.sinh a.1 * ccmWeilWallAgeMode n a.1) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  calc
    -4 * ccmWeilPoleCrossSmoothSlope a.1 +
        ∑ n ∈ S, criticalMellinAtomWeight n * (16 * Real.cosh (Real.log n / 2)) +
        Real.cosh a.1 * (4 * ccmWeilPoleDiagonalSmoothSlope a.1 +
          ∑ n ∈ S, criticalMellinAtomWeight n *
            (-16 * Real.cosh (a.1 - Real.log n / 2))) -
        Real.sinh a.1 * (4 * ccmWeilPoleDiagonalSmooth a.1 +
          ∑ n ∈ S, criticalMellinAtomWeight n * ccmWeilWallAgeMode n a.1) =
        (-4 * ccmWeilPoleCrossSmoothSlope a.1 +
          4 * Real.cosh a.1 * ccmWeilPoleDiagonalSmoothSlope a.1 -
            4 * Real.sinh a.1 * ccmWeilPoleDiagonalSmooth a.1) +
          ((∑ n ∈ S, criticalMellinAtomWeight n * (16 * Real.cosh (Real.log n / 2))) +
            Real.cosh a.1 * (∑ n ∈ S, criticalMellinAtomWeight n *
              (-16 * Real.cosh (a.1 - Real.log n / 2))) -
            Real.sinh a.1 * (∑ n ∈ S, criticalMellinAtomWeight n *
              ccmWeilWallAgeMode n a.1)) := by ring
    _ = (-4 * ccmWeilPoleCrossSmoothSlope a.1 +
          4 * Real.cosh a.1 * ccmWeilPoleDiagonalSmoothSlope a.1 -
            4 * Real.sinh a.1 * ccmWeilPoleDiagonalSmooth a.1) + 0 := by rw [hcombine, hsum]
    _ = _ := by ring

/-- At the literal cutoff, the common-age head is exactly the sum of both
source parity tests. -/
theorem ccmWeilParityAgeHead_cutoff_eq_sourceSum (a : SuzukiPositiveAperture) :
    ccmWeilParityAgeHead (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊) a.1 =
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) +
        ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) := by
  simpa only [ccmWeilParityAgeHead] using
    (ccmWeilParityPole_sum_eq_diagonal_ageModes a).symm

/-- At the literal cutoff, the relative-clock head is exactly the difference
of both source parity tests. -/
theorem ccmWeilParityClockHead_cutoff_eq_sourceSub (a : SuzukiPositiveAperture) :
    ccmWeilParityClockHead (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊) a.1 =
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) -
        ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) := by
  simpa only [ccmWeilParityClockHead] using
    (ccmWeilParityPole_sub_eq_cross_clockModes a).symm

end RHTower
