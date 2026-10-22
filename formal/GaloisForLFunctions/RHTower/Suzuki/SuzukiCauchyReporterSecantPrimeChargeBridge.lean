import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantTransitionCoreEscape
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardAtomicContinuousLightWeld

/-!
# Prime-charge bridge for the Suzuki Cauchy reporter packet

The lower-Hardy anchor of the literal natural Cauchy reporter packet is exactly Suzuki's coherent
prime outgoing charge.  Consequently the positive transition core dominates the square of the
same atomic mass which enters the exact atomic--continuous RH criterion.

This identifies the order-of-operations obstruction behind raw-wall escape.  Squaring the atomic
packet before inserting the regular-screw continuum forces a divergent positive core.  The
RH-bearing quantity instead compensates prime and continuum amplitudes first and only then asks
for uniform control.  The completed Cauchy anchor below is exactly Suzuki Green, so its uniform
boundedness is unconditionally equivalent to RH.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- The literal natural reporter packet and the coherent finite-prime wall have the same lower
Hardy anchor.  This is an equality of the corpus-native arithmetic sources, not a comparison. -/
theorem suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiNaturalApertureLowerHardyAmplitude N =
      unitRieszCoherentPrimeOutgoingCharge N := by
  rw [suzukiNaturalApertureLowerHardyAmplitude_eq_sum,
    ← unitRieszSuzuki_prime_sum hN]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hkIcc := Finset.mem_Icc.mp hk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hkIcc.1)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hlog : 0 ≤ Real.log N - Real.log k :=
    sub_nonneg.mpr (Real.log_le_log hkpos (by exact_mod_cast hkIcc.2))
  rw [suzukiNaturalApertureLag, Real.coe_toNNReal _ hlog]
  unfold unitRieszSuzukiReporter
  congr 1 <;> ring_nf

/-- The exact positive transition core dominates the square of the coherent prime outgoing
charge.  Thus the divergent core is precisely anchor-visible atomic mass. -/
theorem unitRieszCoherentPrimeOutgoingCharge_sq_le_transitionCore
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentPrimeOutgoingCharge N ^ 2 ≤
      suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
  rw [← suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge hN]
  exact (suzukiNaturalApertureLowerHardyAmplitude_sq_le_energy N).trans
    (suzukiNaturalApertureCauchyEnergy_le_transitionCore N)

/-- Amplitude-level completion of the natural Cauchy reporter anchor by the regular-screw
continuum. -/
def suzukiNaturalApertureCompletedLowerHardyAmplitude (N : ℕ) : ℝ :=
  suzukiNaturalApertureLowerHardyAmplitude N -
    suzukiUnitRieszRegularWardMass (Real.log N)

/-- The completed Cauchy anchor is exactly Suzuki Green on every nondegenerate natural aperture. -/
theorem suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green
    (N : ℕ) :
    suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 2) =
      unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) := by
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude,
    suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge
      (by omega : 2 ≤ N + 2)]
  exact (unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass N).symm

/-- The amplitude-completed reporter anchor is exactly the lower-Hardy value of the literal full
prime--polar--Gamma Ward wall. -/
theorem suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_gammaCompletedWall
    (N : ℕ) :
    (suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 2) : ℂ) =
      suzukiUnitRieszGammaCompletedWardWall (N + 2) (-Complex.I) := by
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green,
    suzukiUnitRieszGammaCompletedWardWall_add_two_neg_I_eq_green]
  norm_num

/-- Uniform boundedness of the amplitude-completed natural Cauchy reporter anchor. -/
def SuzukiNaturalCauchyCompletedAnchorBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
    |suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 2)| ≤ B

/-- **Amplitude-before-energy RH criterion.**  Uniform control becomes exactly RH only after the
positive atomic and continuous amplitudes are compensated, before forming a Gram energy. -/
theorem riemannHypothesis_iff_suzukiNaturalCauchyCompletedAnchorBounded :
    RiemannHypothesis ↔ SuzukiNaturalCauchyCompletedAnchorBounded := by
  rw [riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded]
  unfold SuzukiWardAtomicContinuousImbalanceBounded
    SuzukiNaturalCauchyCompletedAnchorBounded
  constructor
  · rintro ⟨B, hB, hbound⟩
    refine ⟨B, hB, fun N => ?_⟩
    rw [suzukiNaturalApertureCompletedLowerHardyAmplitude,
      suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge
        (by omega : 2 ≤ N + 2)]
    exact hbound N
  · rintro ⟨B, hB, hbound⟩
    refine ⟨B, hB, fun N => ?_⟩
    rw [← suzukiNaturalApertureLowerHardyAmplitude_eq_primeOutgoingCharge
      (by omega : 2 ≤ N + 2)]
    exact hbound N

end

end GaloisForLFunctions.RHTower
