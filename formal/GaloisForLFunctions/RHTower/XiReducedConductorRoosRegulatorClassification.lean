import GaloisForLFunctions.RHTower.XiThetaNodalConductorDegeneration
import GaloisForLFunctions.RHTower.PreDivisorTransverseRamificationRoosTransgression

/-!
# Reduced-conductor/Roos regulator classification

The universal Xi node has one reflection-even datum available after reduced specialization: its
exact multiplicity conductor on the Picard--Lefschetz invariant line.  The transverse completion
class which NDS seeks to annihilate is reflection-odd.  This file proves an exact obstruction:
even allowing an arbitrary set-theoretic regulator, with no linearity, continuity, or monodromy
assumption, the reduced conductor can recover every Xi transverse Roos class if and only if RH
already holds.

The no-go has a sharp positive survivor.  The actual nonzero theta terminal multiplicity jet has a
source-derived logarithmic cut holonomy.  At cut two it recovers the complete centered horizontal
rate.  Adjoining that one oriented coordinate to the reduced conductor gives a canonical,
coefficient-faithful regulator for every Xi fibre, unconditionally.  It preserves the Roos defect;
it does not make the defect exact.  Thus NDS cannot obtain RH from reduced nodal conductor data,
and its surviving proof burden is exactly a global source law forcing the oriented holonomy to
vanish without erasing multiplicity.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- The fixed derived target used by the transverse Route-R/NDS transgression. -/
abbrev XiTransverseDerivedCompletionTarget :=
  DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
    routeRTailRoosRestrictedBond

/-- Reduced nodal data with exact conductor multiplicity, specialized to the universal-node
Picard--Lefschetz invariant line. -/
def xiReducedMultiplicityConductorNearbyClass
    (rho : XiDivisorSupport) : ℂ × ℂ :=
  universalNodeConductorSpecialization ℂ (xiSupportMultiplicity rho : ℂ)

@[simp]
theorem xiReducedMultiplicityConductorNearbyClass_eq
    (rho : XiDivisorSupport) :
    xiReducedMultiplicityConductorNearbyClass rho =
      ((xiSupportMultiplicity rho : ℂ), 0) := rfl

/-- Reduced multiplicity-conductor data is blind to critical-line reflection. -/
theorem xiReducedMultiplicityConductorNearbyClass_lineConj
    (rho : XiDivisorSupport) :
    xiReducedMultiplicityConductorNearbyClass (xiZeroLineConjEquiv rho) =
      xiReducedMultiplicityConductorNearbyClass rho := by
  have hm : xiSupportMultiplicity (xiZeroLineConjEquiv rho) =
      xiSupportMultiplicity rho := by
    change xiSupportMultiplicity (xiZeroReflectEquiv (xiZeroConjEquiv rho)) =
      xiSupportMultiplicity rho
    rw [xiSupportMultiplicity_reflect]
    have hconj : xiZeroConjEquiv rho = xiSupportConj rho := Subtype.ext rfl
    rw [hconj, xiSupportMultiplicity_conj]
  simp [xiReducedMultiplicityConductorNearbyClass, hm]

/-- Proposed NDS regulator using only the reduced node and its exact multiplicity conductor.
No linearity, continuity, or monodromy hypothesis is imposed: failure at this level is stronger. -/
structure XiReducedConductorRoosRegulator where
  toFun : ℂ × ℂ → XiTransverseDerivedCompletionTarget
  realizes : ∀ rho : XiDivisorSupport,
    toFun (xiReducedMultiplicityConductorNearbyClass rho) =
      preDivisorTransverseDerivedCompletionClass (rho : ℂ)

/-- A reduced-conductor regulator can realize all transverse Roos classes iff RH already holds. -/
theorem nonempty_xiReducedConductorRoosRegulator_iff_riemannHypothesis :
    Nonempty XiReducedConductorRoosRegulator ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨R⟩
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    have hsame :
        preDivisorTransverseDerivedCompletionClass
            ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) =
          preDivisorTransverseDerivedCompletionClass (rho : ℂ) := by
      rw [← R.realizes (xiZeroLineConjEquiv rho), ← R.realizes rho,
        xiReducedMultiplicityConductorNearbyClass_lineConj]
    have hodd :
        preDivisorTransverseDerivedCompletionClass
            ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) =
          -preDivisorTransverseDerivedCompletionClass (rho : ℂ) := by
      simpa [PreDivisorReflectionDefectStabilization.preDivisorLineConj,
        xiZeroLineConjEquiv_apply] using
        preDivisorTransverseDerivedCompletionClass_lineConj (rho : ℂ)
    have hzero : preDivisorTransverseDerivedCompletionClass (rho : ℂ) = 0 := by
      have hselfneg :
          preDivisorTransverseDerivedCompletionClass (rho : ℂ) =
            -preDivisorTransverseDerivedCompletionClass (rho : ℂ) := hsame.symm.trans hodd
      have htwo :
          (2 : ℂ) • preDivisorTransverseDerivedCompletionClass (rho : ℂ) = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr hselfneg
      have hscaled := congrArg
        (fun y : XiTransverseDerivedCompletionTarget => (1 / 2 : ℂ) • y) htwo
      simpa [smul_smul] using hscaled
    exact (preDivisorTransverseDerivedCompletionClass_eq_zero_iff (rho : ℂ)).1 hzero
  · intro hRH
    refine ⟨⟨fun _ => 0, ?_⟩⟩
    intro rho
    exact (preDivisorTransverseDerivedCompletionClass_eq_zero_iff (rho : ℂ)).2
      ((riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
        (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)) |>.symm

/-! ## Exact oriented repair -/

/-- Reduced multiplicity conductor together with the actual terminal-jet holonomy at cut two. -/
def xiOrientedMultiplicityConductorDatum
    (rho : XiDivisorSupport) : (ℂ × ℂ) × ℝ :=
  (xiReducedMultiplicityConductorNearbyClass rho,
    xiThetaTerminalMultiplicityCutLogGain rho 2)

/-- Cut two recovers the full centered horizontal rate, not merely its sign. -/
theorem xiThetaTerminalMultiplicityCutLogGain_two
    (rho : XiDivisorSupport) :
    xiThetaTerminalMultiplicityCutLogGain rho 2 =
      PreDivisorReflectionDefectStabilization.preDivisorCenteredRate (rho : ℂ) := by
  rw [xiThetaTerminalMultiplicityCutLogGain_eq,
    primeDepthBVWoldXiCenteredRate,
    PreDivisorReflectionDefectStabilization.preDivisorCenteredRate]
  ring

/-- An oriented conductor regulator is allowed one source-derived reflection-odd holonomy
coordinate in addition to the reflection-even reduced conductor class. -/
structure XiOrientedConductorRoosRegulator where
  toFun : ((ℂ × ℂ) × ℝ) → XiTransverseDerivedCompletionTarget
  realizes : ∀ rho : XiDivisorSupport,
    toFun (xiOrientedMultiplicityConductorDatum rho) =
      preDivisorTransverseDerivedCompletionClass (rho : ℂ)

/-- Canonical oriented regulator: terminal-jet holonomy feeds the coefficient-faithful wall class. -/
def canonicalXiOrientedConductorRoosRegulator :
    XiOrientedConductorRoosRegulator where
  toFun d :=
    routeRSummableHadamardToTailRoos
      (routeRPrimeGammaCriticalWallSummableHadamardClass d.2)
  realizes rho := by
    rw [xiOrientedMultiplicityConductorDatum,
      xiThetaTerminalMultiplicityCutLogGain_two,
      preDivisorTransverseDerivedCompletionClass,
      preDivisorTransverseCompletionDefect]

/-- Exact NDS classification: reduced conductor data realizes the Roos class iff RH, while one
oriented terminal-jet holonomy coordinate gives an unconditional coefficient-faithful regulator. -/
theorem xiConductorRoosRegulator_orientationClassification :
    (Nonempty XiReducedConductorRoosRegulator ↔ RiemannHypothesis) ∧
      Nonempty XiOrientedConductorRoosRegulator := by
  exact ⟨nonempty_xiReducedConductorRoosRegulator_iff_riemannHypothesis,
    ⟨canonicalXiOrientedConductorRoosRegulator⟩⟩

end

end RHTower
