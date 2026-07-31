import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.XiReflectionShiftInstance

/-!
# Xi antipodal-shift phase splitting

Schwarz equivariance and functional-equation reflection impose complementary phases on the
completed-Xi logarithmic derivative. Along the imaginary observation axis, every real antipodal
shift difference is real and even, while the unshifted critical-line channel is purely imaginary.
-/

open Complex

namespace RHTower

noncomputable section

/-- The completed-Xi logarithmic derivative is globally Schwarz-equivariant. -/
theorem logDeriv_xi_conj_global (s : ℂ) :
    logDeriv xi ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (logDeriv xi s) := by
  simpa [seamFluxCochain] using seamFluxCochain_conj s

/-- Conjugating a pairwise completed-Xi shift difference with real endpoints reverses its
imaginary observation coordinate. -/
theorem star_xiPairwiseShiftRawLogDerivDifference_ofReal
    (a b t : ℝ) :
    (starRingEnd ℂ)
        (xiPairwiseShiftRawLogDerivDifference (a : ℂ) (b : ℂ) (I * (t : ℂ))) =
      xiPairwiseShiftRawLogDerivDifference (a : ℂ) (b : ℂ) (-I * (t : ℂ)) := by
  rw [xiPairwiseShiftRawLogDerivDifference, map_sub,
    ← logDeriv_xi_conj_global, ← logDeriv_xi_conj_global]
  congr 2 <;> apply Complex.ext <;> simp

/-- Real antipodal shift differences are fixed by Schwarz conjugation on the imaginary
observation axis. -/
theorem xiPairwiseShiftRawLogDerivDifference_antipodal_star
    {a b : ℝ} (hab : a + b = 1) (t : ℝ) :
    (starRingEnd ℂ)
        (xiPairwiseShiftRawLogDerivDifference (a : ℂ) (b : ℂ) (I * (t : ℂ))) =
      xiPairwiseShiftRawLogDerivDifference (a : ℂ) (b : ℂ) (I * (t : ℂ)) := by
  rw [star_xiPairwiseShiftRawLogDerivDifference_ofReal]
  have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  convert xiPairwiseShiftRawLogDerivDifference_neg habc (I * (t : ℂ)) using 1 ; ring

/-- Every real antipodal shift-difference channel is real-valued on the imaginary observation
axis. -/
theorem xiPairwiseShiftRawLogDerivDifference_antipodal_im
    {a b : ℝ} (hab : a + b = 1) (t : ℝ) :
    (xiPairwiseShiftRawLogDerivDifference
      (a : ℂ) (b : ℂ) (I * (t : ℂ))).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (xiPairwiseShiftRawLogDerivDifference_antipodal_star hab t)

/-- **Xi antipodal-shift phase-splitting universality.** Every real shift pair symmetric about
`1/2` produces a real-even completed-Xi difference on the imaginary observation axis, whereas the
unshifted completed-Xi logarithmic derivative has zero real part on the critical line. -/
theorem xi_antipodalShift_phaseSplittingUniversality
    {a b : ℝ} (hab : a + b = 1) (t : ℝ) :
    xiPairwiseShiftRawLogDerivDifference
        (a : ℂ) (b : ℂ) (-I * (t : ℂ)) =
        xiPairwiseShiftRawLogDerivDifference
          (a : ℂ) (b : ℂ) (I * (t : ℂ)) ∧
      (xiPairwiseShiftRawLogDerivDifference
        (a : ℂ) (b : ℂ) (I * (t : ℂ))).im = 0 ∧
      (logDeriv xi ((1 / 2 : ℂ) + I * (t : ℂ))).re = 0 := by
  have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  refine ⟨?_, xiPairwiseShiftRawLogDerivDifference_antipodal_im hab t, ?_⟩
  · convert xiPairwiseShiftRawLogDerivDifference_neg habc (I * (t : ℂ)) using 1 ; ring
  · simpa [logDeriv_apply] using re_logDeriv_xi_criticalLine t

end

end RHTower
