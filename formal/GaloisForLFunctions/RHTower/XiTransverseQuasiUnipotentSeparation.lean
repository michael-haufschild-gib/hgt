import GaloisForLFunctions.RHTower.XiTransverseCompletionSourceSpinDescent
import GaloisForLFunctions.RHTower.XiThetaNodalConductorDegeneration
import GaloisForLFunctions.RHTower.LocalDivisorJetAdamsMonodromy

/-!
# Transverse quasi-unipotence, separated from longitudinal multiplicity

The Xi source has two monodromy channels that cannot be assigned the same geometric law.

* Its transverse rank-one character is the positive real Deninger gain
  `n^(2 Re(rho) - 1)`.  If this character is geometric/regular-singular, its monodromy must
  be quasi-unipotent.  Positivity then makes finite order equivalent to triviality, hence to
  the critical line and to vanishing of the transverse completion defect.
* Its longitudinal terminal multiplicity class already survives as a nonzero fixed vector in
  the universal nodal nearby-cycle lattice at every Xi divisor point.
* Imposing quasi-unipotence on the genuine Adams action on that whole longitudinal jet is too
  strong: it forces the jet to have length one.

Thus a viable geometric-origin construction must be infinite/nonholonomic in its longitudinal
sector while admitting a finite geometric rank-one transverse quotient.  This file proves the
exact separation law and its hostile falsification clause.  It does not construct the geometric
quotient; global existence of that quotient is equivalent to RH.
-/

namespace RHTower

noncomputable section

/-- The actual positive transverse Xi character has finite-order local monodromy.  This is the
transparent algebraic consequence a geometric rank-one transverse quotient would have to
supply; no geometric-origin claim is hidden in the definition. -/
def XiTransverseQuasiUnipotent
    (n : ℕ) (rho : XiDivisorSupport) : Prop :=
  ∃ r : ℕ, 0 < r ∧ deningerHalfDensityMateGain n (rho : ℂ) ^ r = 1

/-- A positive real transverse character is quasi-unipotent exactly at neutral grade. -/
theorem xiTransverseQuasiUnipotent_iff_re_eq_half
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    XiTransverseQuasiUnipotent n rho ↔ (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨r, hr, hpow⟩
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (pow_eq_one_iff_of_nonneg
        (deningerHalfDensityMateGain_pos n (rho : ℂ)).le
        (Nat.ne_of_gt hr)).mp hpow
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mp hgain
  · intro hline
    refine ⟨1, by omega, ?_⟩
    rw [(deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mpr hline]
    norm_num

/-- Finite-order transverse monodromy is exactly vanishing of the Route-R completion class. -/
theorem xiTransverseQuasiUnipotent_iff_completionDefect_eq_zero
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    XiTransverseQuasiUnipotent n rho ↔
      xiTransverseCompletionDefect rho = 0 := by
  have hdefect : xiTransverseCompletionDefect rho = 0 ↔
      (rho : ℂ).re = 1 / 2 :=
    (xiTransverseCompletionDefect_eq_zero_iff_eulerWickOrientation rho).trans
      (GaloisForLFunctions.RHTower.eulerWickPrimitiveCompletedJetGradedRealAt_iff_re_eq_half
        (rho : ℂ))
  exact (xiTransverseQuasiUnipotent_iff_re_eq_half hn rho).trans hdefect.symm

/-- Global finite-order transverse monodromy is equivalent to RH.  This prevents a future
geometric-origin construction from hiding the entire endpoint inside a weaker-looking word. -/
theorem riemannHypothesis_iff_all_xiTransverseQuasiUnipotent
    {n : ℕ} (hn : 2 ≤ n) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, XiTransverseQuasiUnipotent n rho := by
  constructor
  · intro hRH rho
    exact (xiTransverseQuasiUnipotent_iff_re_eq_half hn rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let q : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact (xiTransverseQuasiUnipotent_iff_re_eq_half hn q).1 (h q)

/-- **Transverse/longitudinal separation law.**  Quasi-unipotence may consistently constrain
the rank-one transverse character.  The multiplicity-bearing nearby invariant survives
unconditionally, whereas extending quasi-unipotence to the genuine Adams jet forces that jet
to be reduced. -/
theorem xiTransverseLongitudinalMonodromy_separation
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    (XiTransverseQuasiUnipotent n rho ↔
      xiTransverseCompletionDefect rho = 0) ∧
    (∀ x : ℝ,
      xiThetaTerminalNearbyInvariantClass rho x ≠ 0 ∧
      GaloisForLFunctions.HTGeometry.universalNodePicardLefschetzMonodromy ℂ
          (xiThetaTerminalNearbyInvariantClass rho x) =
        xiThetaTerminalNearbyInvariantClass rho x) ∧
    (∀ q : ℕ, 2 ≤ q →
      AdamsDilationQuasiUnipotent (xiSupportMultiplicity rho) q →
      xiSupportMultiplicity rho = 1) := by
  refine ⟨xiTransverseQuasiUnipotent_iff_completionDefect_eq_zero hn rho, ?_, ?_⟩
  · intro x
    exact ⟨xiThetaTerminalNearbyInvariantClass_ne_zero rho x,
      xiThetaTerminalNearbyInvariantClass_monodromy_fixed rho x⟩
  · intro q hq hqu
    exact adamsDilation_quasiUnipotent_forces_simple
      (xiSupportMultiplicity_pos rho) hq hqu

/-- **Hostile falsification clause.**  Any off-line Xi divisor disproves transverse geometric
quasi-unipotence while its multiplicity-bearing invariant nearby-cycle class remains nonzero
and Picard--Lefschetz fixed.  Failure is therefore purely transverse, not loss of divisor data. -/
theorem xiDivisor_offLine_falsifies_transverseQuasiUnipotence_but_nearbyInvariant_survives
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬ XiTransverseQuasiUnipotent n rho ∧
    ∀ x : ℝ,
      xiThetaTerminalNearbyInvariantClass rho x ≠ 0 ∧
      GaloisForLFunctions.HTGeometry.universalNodePicardLefschetzMonodromy ℂ
          (xiThetaTerminalNearbyInvariantClass rho x) =
        xiThetaTerminalNearbyInvariantClass rho x := by
  refine ⟨?_, ?_⟩
  · exact (xiTransverseQuasiUnipotent_iff_re_eq_half hn rho).not.mpr hoff
  · intro x
    exact ⟨xiThetaTerminalNearbyInvariantClass_ne_zero rho x,
      xiThetaTerminalNearbyInvariantClass_monodromy_fixed rho x⟩

end

end RHTower
