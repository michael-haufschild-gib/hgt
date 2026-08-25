import GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort
import GaloisForLFunctions.RHTower.XiTerminalMultiplicityJetCurvatureTransgression

/-!
# Terminal multiplicity as an arithmetic differential character

The terminal theta-multiplicity transport, nodal second-order descent curvature, and Deninger
central monodromy were previously exact but separate Xi-fibre detectors.  This module proves that
they are one invariant in additive and multiplicative coordinates.  At clock `n`, the Deninger
gain is the exponential of terminal transport across cut `2 log n`; its logarithm reconstructs
the nodal mixed curvature after pairing with vertical phase.

This distinction matters because zero local curvature does not trivialize holonomy for a general
flat connection.  The actual arithmetic character has no such ambiguity: its positive-real
exponential lift is faithful, and its nonzero Xi multiplicity coefficient prevents the monodromy
defect from being erased.

These are exact cross-route transgression laws on actual Xi divisor fibres, not a source-side
global vanishing theorem and not an RH proof.
-/

open Complex

namespace RHTower

noncomputable section

/-- Terminal multiplicity transport is the logarithmic coordinate of Deninger's central
arithmetic character. -/
theorem deningerHalfDensityMateGain_eq_exp_terminalMultiplicityCutLogGain
    (n : ℕ) (rho : XiDivisorSupport) :
    deningerHalfDensityMateGain n (rho : ℂ) =
      Real.exp
        (xiThetaTerminalMultiplicityCutLogGain rho (2 * Real.log n)) := by
  rw [xiThetaTerminalMultiplicityCutLogGain_eq,
    primeDepthBVWoldXiCenteredRate]
  simp only [deningerHalfDensityMateGain]
  congr 1
  ring

/-- The Xi central monodromy defect is exponentiated terminal-jet holonomy acting on the
protected leading multiplicity coefficient. -/
theorem centralHolonomyDefect_eq_exp_terminalMultiplicityCutLogGain
    (n : ℕ) (rho : XiDivisorSupport) :
    GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (rho : ℂ)
        (thetaInternalJetLeadingSourceCoefficient rho) =
      (((Real.exp
          (xiThetaTerminalMultiplicityCutLogGain rho (2 * Real.log n)) : ℝ) : ℂ) - 1) *
        thetaInternalJetLeadingSourceCoefficient rho := by
  rw [GaloisForLFunctions.IrregularStokes.centralHolonomyDefect,
    deningerHalfDensityMateGain_eq_exp_terminalMultiplicityCutLogGain]

/-- On an actual Xi divisor fibre, the faithful arithmetic character has no flat-but-nontrivial
holonomy ambiguity: its monodromy defect vanishes exactly when its logarithmic terminal transport
vanishes.  Nonvanishing of the protected multiplicity coefficient is essential. -/
theorem centralHolonomyDefect_eq_zero_iff_terminalMultiplicityCutLogGain_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
        (thetaInternalJetLeadingSourceCoefficient q.1) = 0 ↔
      xiThetaTerminalMultiplicityCutLogGain q.1 (2 * Real.log n) = 0 := by
  rw [centralHolonomyDefect_eq_exp_terminalMultiplicityCutLogGain]
  let L := xiThetaTerminalMultiplicityCutLogGain q.1 (2 * Real.log n)
  have hc : thetaInternalJetLeadingSourceCoefficient q.1 ≠ 0 :=
    thetaInternalJetLeadingSourceCoefficient_ne_zero q.1
  constructor
  · intro h
    have hfactor : (((Real.exp L : ℝ) : ℂ) - 1) = 0 :=
      (mul_eq_zero.mp h).resolve_right hc
    have hreal : Real.exp L - 1 = 0 := by
      exact_mod_cast hfactor
    exact (Real.exp_eq_one_iff L).mp (sub_eq_zero.mp hreal)
  · intro h
    apply mul_eq_zero.mpr
    left
    rw [h]
    norm_num

/-- The local second-order descent curvature is the logarithm of the global arithmetic
holonomy, normalized by one clock length and paired with vertical phase. -/
theorem xiNodalArithmeticSecondOrderDefect_apply_eq_log_centralHolonomy
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy)
    (x : DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    GaloisForLFunctions.HTGeometry.secondOrderConstraintDescentDefect
        deningerCalderonWittGlobalOrientedKoszulTotalDifferential
        deningerCalderonWittNodalTopObservation
        (xiNodalTotalDefectEnd q) x =
      (((q.1 : ℂ).im / Real.log n *
          Real.log (deningerHalfDensityMateGain n (q.1 : ℂ)) : ℝ) : ℂ) •
        deningerCalderonWittNodalTopObservation x := by
  rw [xiNodalArithmeticSecondOrderDefect_apply,
    deningerHalfDensityMateGain, Real.log_exp]
  congr 1
  have hlog : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)))
  norm_cast
  rw [primeDepthBVWoldXiCenteredRate]
  field_simp [hlog]

/-- Differential-character closure: at every nontrivial arithmetic clock, trivial central
monodromy is exactly coherent second-order arithmetic descent, while the Xi multiplicity jet
itself remains nonzero. -/
theorem xiProtectedMultiplicityCentralHolonomy_secondOrderCoherence
    {n : ℕ} (hn : 2 ≤ n) (q : XiZeroCopy) :
    xiThetaTerminalMultiplicityCutJet q.1 0 ≠ 0 ∧
      (GaloisForLFunctions.IrregularStokes.centralHolonomyDefect n (q.1 : ℂ)
          (thetaInternalJetLeadingSourceCoefficient q.1) = 0 ↔
        XiNodalArithmeticSecondOrderCoherent q) := by
  refine ⟨xiThetaTerminalMultiplicityCutJet_ne_zero q.1 0, ?_⟩
  rw [centralHolonomyDefect_eq_zero_iff_terminalMultiplicityCutLogGain_eq_zero n q]
  have hlog : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hn)))
  exact xiThetaTerminalMultiplicityCutLogGain_eq_zero_iff_nodalArithmeticSecondOrderCoherent
    q (mul_ne_zero (by norm_num) hlog)

end

end RHTower
