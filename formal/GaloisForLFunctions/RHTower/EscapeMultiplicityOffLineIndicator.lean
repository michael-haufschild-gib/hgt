import GaloisForLFunctions.RHTower.DirectSubunitEscapeCapacityFusion
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionCapacityTerminal
import GaloisForLFunctions.RHTower.FrobeniusTorsionLaw

/-!
# The escape multiplicity is the off-line indicator

The integer of the direct sub-unit anchor, `thetaKakutaniEscapeMultiplicity`, equals `0` at a zero
copy on the critical line and `1` off it.  Consequently the sub-unit gap inequality
`budget < (115/108) · multiplicity` holds at a copy exactly when the copy is off the line, and the
multiplicity vanishes at every copy exactly when RH holds.  The integer therefore encodes the
conclusion rather than constraining it: a bound below one unit is available only through a
statement equivalent to RH, as the trace-capacity law already shows.
-/

namespace RHTower

open HedenmalmThetaSource

/-- The escape multiplicity vanishes exactly on the critical line. -/
theorem thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half (q : XiZeroCopy) :
    thetaKakutaniEscapeMultiplicity q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaKakutaniEscapeMultiplicity_eq_zero_iff,
    thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- The escape multiplicity is one exactly off the critical line. -/
theorem thetaKakutaniEscapeMultiplicity_eq_one_iff_re_ne_half (q : XiZeroCopy) :
    thetaKakutaniEscapeMultiplicity q = 1 ↔ (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro h hre
    have h0 := (thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q).mpr hre
    omega
  · intro h
    have h0 : thetaKakutaniEscapeMultiplicity q ≠ 0 :=
      fun h0 => h ((thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q).mp h0)
    unfold thetaKakutaniEscapeMultiplicity at h0 ⊢
    split_ifs at h0 ⊢ with hflux
    · exact absurd rfl h0
    · rfl

/-- The escape multiplicity is the off-line indicator. -/
theorem thetaKakutaniEscapeMultiplicity_eq_ite (q : XiZeroCopy) :
    thetaKakutaniEscapeMultiplicity q = if (q.1 : ℂ).re = 1 / 2 then 0 else 1 := by
  split_ifs with h
  · exact (thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q).mpr h
  · exact (thetaKakutaniEscapeMultiplicity_eq_one_iff_re_ne_half q).mpr h

/-- **The sub-unit gap is the off-line condition.**  The inequality
`budget < (115/108) · multiplicity` holds at a copy exactly when the copy is off the line. -/
theorem budget_lt_quantum_mul_escapeMultiplicity_iff (q : XiZeroCopy) :
    routePPrimitiveCollisionCubicTraceBudget
      < (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q ↔ (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro h hre
    have h0 := (thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q).mpr hre
    rw [h0] at h
    simp only [Nat.cast_zero, mul_zero] at h
    exact absurd h (not_lt.mpr routePPrimitiveCollisionCubicTraceBudget_nonneg)
  · intro h
    rw [(thetaKakutaniEscapeMultiplicity_eq_one_iff_re_ne_half q).mpr h]
    simpa using routePPrimitiveCollisionCubicTraceBudget_lt_quantum

/-- **Vanishing of the escape multiplicity at every copy is RH.** -/
theorem forall_thetaKakutaniEscapeMultiplicity_eq_zero_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, thetaKakutaniEscapeMultiplicity q = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have hzero := (thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q.1).mp (h q.1)
    have hright := q.2
    rw [I_mul_xiSpectralPoint] at hright
    norm_num at hright
    linarith
  · intro hRH q
    exact (thetaKakutaniEscapeMultiplicity_eq_zero_iff_re_eq_half q).mpr
      (xi_zero_re_eq_half_of_riemannHypothesis hRH (xi_eq_zero_of_mem_divisor_support q.1))

end RHTower
