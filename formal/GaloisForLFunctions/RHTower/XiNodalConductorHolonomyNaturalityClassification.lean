import GaloisForLFunctions.RHTower.XiReducedConductorRoosRegulatorClassification

/-!
# Xi nodal conductor holonomy naturality classification

The reduced Xi node has a universal Picard--Lefschetz monodromy, and its actual terminal
multiplicity coefficient specializes to the fixed conductor line.  Independently, Deninger's
clock-two arithmetic character transports the same protected terminal coefficient by the genuine
horizontal half-density gain.

This file computes the missing naturality square exactly.  Picard--Lefschetz monodromy fixes the
terminal conductor class, while arithmetic monodromy fixes it exactly on the critical line because
the coefficient is nonzero.  Hence pointwise commutation is critical-line placement and global
commutation is RH.  The desired naturality square is therefore not an unconditional consequence of
reduced nodal geometry; it is the full remaining NDS assertion.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Deninger's clock-two arithmetic character acting on the conductor coordinate of the
universal-node nearby lattice. -/
def xiThetaTerminalArithmeticNearbyMonodromyTwo
    (rho : XiDivisorSupport) (v : ℂ × ℂ) : ℂ × ℂ :=
  (((deningerHalfDensityMateGain 2 (rho : ℂ) : ℝ) : ℂ) * v.1, v.2)

/-- The conductor/nearby-cycle naturality square commutes at one Xi fibre exactly on the critical
line.  Nonvanishing of the actual terminal multiplicity coefficient prevents fake commutation. -/
theorem xiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff
    (rho : XiDivisorSupport) :
    xiThetaTerminalArithmeticNearbyMonodromyTwo rho
        (xiThetaTerminalNearbyInvariantClass rho 0) =
      universalNodePicardLefschetzMonodromy ℂ
        (xiThetaTerminalNearbyInvariantClass rho 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiThetaTerminalNearbyInvariantClass_monodromy_fixed]
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    change (((deningerHalfDensityMateGain 2 (rho : ℂ) : ℝ) : ℂ) *
        xiThetaTerminalMultiplicityCutJet rho 0) =
      xiThetaTerminalMultiplicityCutJet rho 0 at hfirst
    have hc : xiThetaTerminalMultiplicityCutJet rho 0 ≠ 0 :=
      xiThetaTerminalMultiplicityCutJet_ne_zero rho 0
    have hgainC : ((deningerHalfDensityMateGain 2 (rho : ℂ) : ℝ) : ℂ) = 1 := by
      apply mul_right_cancel₀ hc
      simpa using hfirst
    have hgainR : deningerHalfDensityMateGain 2 (rho : ℂ) = 1 := by
      exact_mod_cast hgainC
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half
      (n := 2) (by norm_num) _).1 hgainR
  · intro hline
    have hgain :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half
        (n := 2) (by norm_num) (rho : ℂ)).2 hline
    simp [xiThetaTerminalArithmeticNearbyMonodromyTwo, hgain]

/-- Global commutation of arithmetic and Picard--Lefschetz monodromy on the actual nonzero
terminal conductor classes is equivalent to RH. -/
theorem everyXiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      xiThetaTerminalArithmeticNearbyMonodromyTwo rho
          (xiThetaTerminalNearbyInvariantClass rho 0) =
        universalNodePicardLefschetzMonodromy ℂ
          (xiThetaTerminalNearbyInvariantClass rho 0)) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    exact
      (xiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff rho).1
        (hall rho)
  · intro hRH rho
    apply (xiThetaTerminalArithmeticNearbyMonodromyTwo_eq_picardLefschetz_iff rho).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)

end

end RHTower
