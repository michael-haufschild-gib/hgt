import GaloisForLFunctions.RHTower.DeningerPrimeBlockHasse
import GaloisForLFunctions.RHTower.DeningerPrimePacketContinuousRestrictionGreen

/-!
# Hasse quotient for continuous prime-packet observations

Continuous data on every arithmetic prime packet give a concrete local profile.  Passing to the
canonical Haar-`L²` fibres preserves every local kernel, so global data modulo simultaneous
continuous-packet invisibility are exactly their realized Hilbert-sum profiles.  The all-prime
Green energy is faithful on this quotient.
-/

namespace RHTower

open Filter MeasureTheory Topology
open scoped ENNReal BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global data modulo simultaneous continuous-packet invisibility are exactly their realized
all-prime Haar-`L²` profiles. -/
noncomputable def deningerPrimePacketContinuousHasseQuotientEquivRealizedProfiles
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ)) :
    (E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap
      (deningerPrimePacketContinuousRestriction restriction)
      (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable))) ≃ₗ[ℝ]
      LinearMap.range (deningerPrimeRestrictionLinearMap
        (deningerPrimePacketContinuousRestriction restriction)
        (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)) :=
  deningerPrimeBlockHasseQuotientEquivRealizedProfiles _ _

/-- Two global data define the same quotient class exactly when all original continuous
prime-packet restrictions agree. -/
theorem deningerPrimePacketContinuous_congr_hasse_iff
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x y : E) :
    x - y ∈ LinearMap.ker (deningerPrimeRestrictionLinearMap
        (deningerPrimePacketContinuousRestriction restriction)
        (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)) ↔
      ∀ p, restriction p x = restriction p y := by
  rw [deningerPrimeBlock_congr_hasse_iff]
  apply forall_congr'
  intro p
  constructor
  · intro h
    apply deningerPrimePacketContinuousToHaarL2_injective p
    exact h
  · intro h
    exact congrArg (deningerPrimePacketContinuousToHaarL2 p) h

/-- The continuous-packet Hasse quotient class is zero exactly when its assembled all-prime Green
energy vanishes. -/
theorem deningerPrimePacketContinuousHasse_zeroClass_iff_energy_zero
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    Submodule.Quotient.mk x =
        (0 : E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap
          (deningerPrimePacketContinuousRestriction restriction)
          (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable))) ↔
      deningerPrimePacketContinuousRestrictionSummedGreenForm
        restriction hSupSummable hC hSupBessel x x = 0 := by
  rw [Submodule.Quotient.mk_eq_zero,
    deningerPrimeBlockHasse_mem_ker_iff,
    deningerPrimePacketContinuousRestrictionSummedGreenForm_self_eq_zero_iff]
  exact forall_congr' fun p =>
    deningerPrimePacketContinuousRestriction_eq_zero_iff restriction p x

/-- The continuous-packet all-prime Green energy is strictly positive exactly on nonzero Hasse
quotient classes. -/
theorem deningerPrimePacketContinuousHasse_energy_pos_iff_class_ne_zero
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    0 < deningerPrimePacketContinuousRestrictionSummedGreenForm
        restriction hSupSummable hC hSupBessel x x ↔
      Submodule.Quotient.mk x ≠
        (0 : E ⧸ LinearMap.ker (deningerPrimeRestrictionLinearMap
          (deningerPrimePacketContinuousRestriction restriction)
          (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable))) := by
  constructor
  · intro hpos hzero
    exact (ne_of_gt hpos) ((deningerPrimePacketContinuousHasse_zeroClass_iff_energy_zero
      restriction hSupSummable hC hSupBessel x).1 hzero)
  · intro hne
    have henergy :
        deningerPrimePacketContinuousRestrictionSummedGreenForm
          restriction hSupSummable hC hSupBessel x x ≠ 0 := by
      intro hzero
      exact hne ((deningerPrimePacketContinuousHasse_zeroClass_iff_energy_zero
        restriction hSupSummable hC hSupBessel x).2 hzero)
    exact lt_of_le_of_ne
      (deningerPrimePacketContinuousRestrictionSummedGreenForm_nonneg
        restriction hSupSummable hC hSupBessel x) (Ne.symm henergy)

end

end RHTower
