import GaloisForLFunctions.RHTower.CCM.CCMCoherentSignedMomentArithmeticAction

/-!
# Continuous charge and discrete prime admission

For a fixed prime head, the charge has an exact derivative driven by its
terminal mass mismatch. Admission of the next atom changes the charge by a
quadratic profile that vanishes at that atom's physical time. Thus the charge
glues continuously while its time derivative records the literal prime impulse.
The derivative statement below freezes the head; it does not differentiate a
floor-valued moving cutoff at its jumps.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

theorem ccmActualHeadSignedMomentCharge_succ_sub (T : ℝ) (N : ℕ) :
    ccmActualHeadSignedMomentCharge T (N+1)-ccmActualHeadSignedMomentCharge T N =
      Real.pi*criticalMellinAtomWeight N*(T^2-(Real.log N)^2) := by
  rw [ccmActualHeadSignedMomentCharge_eq_quadraticProfile,
    ccmActualHeadSignedMomentCharge_eq_quadraticProfile, Finset.sum_range_succ]
  ring

/-- Prime admission preserves the signed charge exactly at the physical entry time. -/
theorem ccmActualHeadSignedMomentCharge_primeAdmission (N : ℕ) :
    ccmActualHeadSignedMomentCharge (Real.log N) (N+1) =
      ccmActualHeadSignedMomentCharge (Real.log N) N := by
  have h := ccmActualHeadSignedMomentCharge_succ_sub (Real.log N) N
  simpa only [sub_self, mul_zero, sub_eq_zero] using h

theorem hasDerivAt_ccmActualHeadSignedMomentCharge (T : ℝ) (N : ℕ) :
    HasDerivAt (fun t => ccmActualHeadSignedMomentCharge t N)
      (-2*Real.pi*T*(2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N))) T := by
  have hc : Continuous (fun h : ℝ => Real.exp (h/2)*h^2) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 T) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : HasDerivAt (fun t : ℝ => 2*Real.exp (t/2)) (Real.exp (T/2)) T := by
    convert! (((hasDerivAt_id T).div_const 2).exp.const_mul 2) using 1
    simp only [id_eq]
    ring
  have hd := (((he.sub_const (2+ccmOutgoingPrimeCumulative N)).mul
    ((hasDerivAt_id T).pow 2)).const_add
      (∑ n ∈ Finset.range N, criticalMellinAtomWeight n*(Real.log n)^2)).sub hi
  have h := hd.const_mul (-Real.pi)
  convert! h using 1
  · funext t
    exact ccmActualHeadSignedMomentCharge_eq_completedMoment t N
  · norm_num only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, pow_one,
      show (2 : ℕ)-1 = 1 by rfl]
    ring

theorem deriv_ccmActualHeadSignedMomentCharge (T : ℝ) (N : ℕ) :
    deriv (fun t => ccmActualHeadSignedMomentCharge t N) T =
      -2*Real.pi*T*(2*Real.exp (T/2)-(2+ccmOutgoingPrimeCumulative N)) :=
  (hasDerivAt_ccmActualHeadSignedMomentCharge T N).deriv

theorem continuous_ccmActualHeadSignedMomentCharge (N : ℕ) :
    Continuous (fun t => ccmActualHeadSignedMomentCharge t N) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_ccmActualHeadSignedMomentCharge t N).continuousAt

/-- Discrete admission and continuous time flow have an exact commutator. -/
theorem deriv_ccmActualHeadSignedMomentCharge_succ_sub (T : ℝ) (N : ℕ) :
    deriv (fun t => ccmActualHeadSignedMomentCharge t (N+1)) T -
      deriv (fun t => ccmActualHeadSignedMomentCharge t N) T =
        2*Real.pi*T*criticalMellinAtomWeight N := by
  rw [deriv_ccmActualHeadSignedMomentCharge, deriv_ccmActualHeadSignedMomentCharge,
    ccmOutgoingPrimeCumulative_succ]
  ring

/-- At a physical cutoff the frozen-head force is the actual centered completed error. -/
theorem deriv_ccmActualTimeSignedMomentCharge_eq_completedError (H : NNReal) :
    deriv (fun t => ccmActualHeadSignedMomentCharge t
      (Nat.floor (Real.exp (H : ℝ))+1)) (H : ℝ) =
        -2*Real.pi*(H : ℝ)*(criticalMellinCompletedError (H : ℝ)-
          2*(1-Real.exp (-(H : ℝ)/2))) := by
  rw [deriv_ccmActualHeadSignedMomentCharge,
    quantileTerminalMass_eq_completedError_sub_threshold]
  simp only [neg_div]

theorem deriv_ccmActualTimeSignedMomentCharge_eq_chebyshevVolterra (H : NNReal) :
    deriv (fun t => ccmActualHeadSignedMomentCharge t
      (Nat.floor (Real.exp (H : ℝ))+1)) (H : ℝ) =
        2*Real.pi*(H : ℝ)*(1+criticalMellinNormalizedChebyshevError (H : ℝ) +
          (1/2 : ℝ)*(∫ u in Set.Ioc (0 : ℝ) (H : ℝ), criticalMellinNormalizedChebyshevError u)) := by
  rw [deriv_ccmActualTimeSignedMomentCharge_eq_completedError,
    criticalMellinThresholdCenteredError_eq_chebyshevVolterra]
  ring

end RHTower
