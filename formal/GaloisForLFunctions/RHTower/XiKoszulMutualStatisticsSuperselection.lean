import GaloisForLFunctions.RHTower.DeningerCalderonWittMilnorIncidence
import GaloisForLFunctions.RHTower.XiNodalDefectSuperselection

/-!
# Xi defects as failures of mutual-statistics descent

The all-prime Calderón--Witt degree-one cup is graded-skew.  The analytic mixed Xi jet is a
classical scalar and therefore has no memory of which source leg was applied first.  This file
isolates the resulting statistics collision.

For one Xi divisor copy, an order-independent Koszul lift consists of two source legs whose two
opposite ordered cups both complete to the same mixed grade--phase jet.  The legs may depend on
the zero: no common local producer is imposed.  Skewness says that the two source values are
opposites, while order-independence says that they are equal.  Characteristic zero then kills the
mixed jet.

This is mutual rather than exterior self-statistics.  Requiring a scalar character of the full
exterior algebra would kill each individual leg and is too strong.  Here only simultaneous
grade--phase occupancy is forbidden; either pure branch survives.
-/

open Complex

namespace RHTower

noncomputable section

/-- Zero-specific lift of one classical mixed jet through both orders of the actual all-prime
graded-skew cup.  Different divisor copies may use different source legs. -/
structure XiOrderIndependentKoszulLift (q : XiZeroCopy) where
  gradeLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  phaseLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  gradeThenPhase :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup gradeLeg phaseLeg) =
      (xiReflectedPhaseNeutralMixedJet q : ℂ)
  phaseThenGrade :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup phaseLeg gradeLeg) =
      (xiReflectedPhaseNeutralMixedJet q : ℂ)

/-- Mutual-statistics collision: one scalar cannot be the order-independent image of two
graded-skew source orderings unless it vanishes. -/
theorem xiReflectedPhaseNeutralMixedJet_eq_zero_of_orderIndependentKoszulLift
    (q : XiZeroCopy) (L : XiOrderIndependentKoszulLift q) :
    xiReflectedPhaseNeutralMixedJet q = 0 := by
  have hskew := congrArg deningerCalderonWittAlgebraicGlobalCenterTrace
    (deningerCalderonWittAlgebraicGlobalCup_skew L.gradeLeg L.phaseLeg)
  rw [map_neg, L.gradeThenPhase, L.phaseThenGrade] at hskew
  have htwo : (2 : ℂ) * (xiReflectedPhaseNeutralMixedJet q : ℂ) = 0 := by
    calc
      (2 : ℂ) * (xiReflectedPhaseNeutralMixedJet q : ℂ) =
          (xiReflectedPhaseNeutralMixedJet q : ℂ) +
            (xiReflectedPhaseNeutralMixedJet q : ℂ) := by ring
      _ = (xiReflectedPhaseNeutralMixedJet q : ℂ) +
          -(xiReflectedPhaseNeutralMixedJet q : ℂ) := by
        nth_rewrite 2 [hskew]
        rfl
      _ = 0 := add_neg_cancel _
  have hzero : (xiReflectedPhaseNeutralMixedJet q : ℂ) = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hre := congrArg Complex.re hzero
  simpa using hre

/-- An order-independent lift forces the local nodal superselection law. -/
theorem xiNodalDefectSuperselected_of_orderIndependentKoszulLift
    (q : XiZeroCopy) (L : XiOrderIndependentKoszulLift q) :
    XiNodalDefectSuperselected q :=
  (xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q).2
    (xiReflectedPhaseNeutralMixedJet_eq_zero_of_orderIndependentKoszulLift q L)

/-- At a pure defect the zero source legs give the degenerate order-independent lift.  Thus the
existence statement has exactly nodal strength; future work must construct it functorially from
completion, not assume it as extra data. -/
theorem nonempty_xiOrderIndependentKoszulLift_iff (q : XiZeroCopy) :
    Nonempty (XiOrderIndependentKoszulLift q) ↔ XiNodalDefectSuperselected q := by
  constructor
  · rintro ⟨L⟩
    exact xiNodalDefectSuperselected_of_orderIndependentKoszulLift q L
  · intro hpure
    have hjet := (xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q).1 hpure
    refine ⟨⟨0, 0, ?_, ?_⟩⟩ <;>
      simp [hjet]

/-- Universal order-independent Koszul completion.  Witness legs remain zero-specific. -/
def XiOrderIndependentKoszulCompletion : Prop :=
  ∀ q : XiZeroCopy, Nonempty (XiOrderIndependentKoszulLift q)

/-- New endpoint: universal anomaly-free mutual-statistics descent is exactly RH. -/
theorem xiOrderIndependentKoszulCompletion_iff_riemannHypothesis :
    XiOrderIndependentKoszulCompletion ↔ RiemannHypothesis := by
  rw [← xiNodalDefectSuperselection_iff_riemannHypothesis]
  apply forall_congr'
  exact nonempty_xiOrderIndependentKoszulLift_iff

end

end RHTower
