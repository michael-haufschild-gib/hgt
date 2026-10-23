import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedDampingWorkOfTheMobiusEnergy

/-!
# The first cell carries adverse work

The damping derivative of the critical receiver is twice the complete signed work,
`∂_ε E_T(ε) = 2 W_T(ε)`, `W_T(ε) = Σ_{n ≤ T} A_ε(n) E_ε(n)/(n(n + 1))`
(`ArithmeticContinuationAndCriticalEnergy.hasDerivAt_dampedMobiusEnergy`). A continuation estimate
that asked for nonnegative work everywhere would be asking for something false on the actual source,
already at the first horizon. There `A_ε(1) = 1 − 1/ζ(1+ε)` and `E_ε(1) = −m(ε)`, `m(ε) = Re(−ζ'/ζ²)`
at `1 + ε`, so

`W_1(ε) = −(1 − 1/ζ(1+ε)) m(ε)/2 → −1/2`  as `ε ↓ 0`  (`tendsto_signedDampingWork_one`),

because `1/ζ(1+ε) → 0` and `m(ε) → 1` from the simple pole. Hence the work is negative at the first
horizon for all small dampings (`eventually_signedDampingWork_one_neg`) and global nonnegative work
fails (`not_forall_signedDampingWork_nonneg`). A usable continuation theorem must accommodate
adverse work and let it be repaid elsewhere — the signed, averaged budget of
`ArithmeticContinuationAndCriticalEnergy.TheAveragedBudgetIsExactlyAdmission`.
-/

open Filter Topology Finset RHTower
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The first cell of the source: `A_ε(1) = 1 − Re(1/ζ(1+ε))`. -/
theorem centredPrefix_one (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 1 = 1 - (pmPowerDampedDivisorDensity ε).re := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  simp [pmPowerDampedDivisorCoeff]

/-- The first cell of the damped Chebyshev tangent: `E_ε(1) = −m(ε)`. -/
theorem dampedChebyshevError_one (ε : ℝ) : dampedChebyshevError ε 1 = -dampedReadout ε := by
  simp [dampedChebyshevError, dampedVonMangoldt]

/-- The work at the first horizon is a single pronic cell. -/
theorem signedDampingWork_one (ε : ℝ) :
    signedDampingWork ε 1 =
      -((1 - (pmPowerDampedDivisorDensity ε).re) * dampedReadout ε) / 2 := by
  rw [signedDampingWork, show Icc 1 1 = {1} by rfl, sum_singleton, centredPrefix_one,
    dampedChebyshevError_one]
  norm_num

/-- **The first-cell work tends to `−1/2` at zero damping.** -/
theorem tendsto_signedDampingWork_one :
    Tendsto (fun ε => signedDampingWork ε 1) (𝓝[>] 0) (𝓝 (-1 / 2)) := by
  have hA := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_pmPowerDampedDivisorDensity_re_zero
  have h := ((hA.mul tendsto_dampedReadout_zero).neg).div_const 2
  rw [sub_zero, one_mul] at h
  refine h.congr fun ε => ?_
  rw [signedDampingWork_one]

/-- The first-cell work is negative at every small positive damping. -/
theorem eventually_signedDampingWork_one_neg :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), signedDampingWork ε 1 < 0 :=
  tendsto_signedDampingWork_one.eventually (gt_mem_nhds (by norm_num))

/-- **No global nonnegative work.** The signed damping work of the actual source is negative
somewhere, at the first horizon and at arbitrarily small dampings. -/
theorem not_forall_signedDampingWork_nonneg :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, 0 ≤ signedDampingWork ε T := by
  intro h
  obtain ⟨ε, hε, hpos⟩ := (eventually_signedDampingWork_one_neg.and
    self_mem_nhdsWithin).exists
  exact absurd (h ε hpos 1) (not_le.mpr hε)

end GaloisForLFunctions.ArithmeticCompensationTheory
