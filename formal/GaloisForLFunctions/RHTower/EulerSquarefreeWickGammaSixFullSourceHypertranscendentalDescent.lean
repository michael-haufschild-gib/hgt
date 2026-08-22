import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixHypertranscendentalDephasingRigidity
import GaloisForLFunctions.RHTower.FrankensteinXiFullIntegralGammaEvaluationProducer

/-!
# Hypertranscendental descent of the full Gamma source through the EWQ interaction

Strict inversion in the integral Laurent Gamma source closes by retaining a quadratic ghost:
forward defect plus inverse defect plus their product is zero.  The two linear defects belong to
the analytic marginal field.  Coefficient-faithful Euler--Wick completion instead decorates the
quadratic ghost by the relatively hypertranscendental mod-twelve interaction carrier.

The decorated relation cannot descend unless both its joint coefficient and its marginal part
vanish.  The joint coefficient is the negative Gamma-six paired curvature, whose radical is
exactly neutral horizontal grade.  Thus mixed-ghost descent at each Xi divisor is equivalent to
critical-line placement, and descent at every divisor copy is equivalent to RH.  This identifies
a concrete producer obligation rather than assuming a positivity or orientation law.
-/

open GaloisForLFunctions.HTGeometry
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance eulerWickFullSourceHTUpperEndAnalyticDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance eulerWickFullSourceHTUpperEndMeroComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance eulerWickFullSourceHTUpperEndMeroDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- A transcendental carrier is linearly independent from its base field. -/
theorem transcendental_linearBase_zero_rigidity
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (hx : Transcendental K x) (b c : K)
    (hzero : algebraMap K F b * x + algebraMap K F c = 0) :
    b = 0 ∧ c = 0 := by
  have hrepair :
      algebraMap K F (1 + b) * x + algebraMap K F c = x := by
    rw [map_add, map_one]
    linear_combination hzero
  have hrig := transcendental_affineBase_selfRepair_rigidity hx (1 + b) c hrepair
  refine ⟨?_, hrig.2⟩
  linear_combination hrig.1

/-- Concrete EWQ interaction carrier is linearly independent from every analytic marginal. -/
theorem quadraticResidueAnalyticProductCarrier_linearMarginal_zero_rigidity
    (shift : ℂ) (b c : quadraticResidueAnalyticMarginalField shift)
    (hzero :
      (b : upperEndMeroField) * quadraticResidueAnalyticProductCarrier shift +
          (c : upperEndMeroField) = 0) :
    b = 0 ∧ c = 0 := by
  have hrel := quadraticResidueAnalyticProductCarrier_relativeHT shift
  unfold GaloisForLFunctions.DifferentialIndependent at hrel
  have htrans : Transcendental (quadraticResidueAnalyticMarginalField shift)
      (quadraticResidueAnalyticProductCarrier shift) := by
    simpa using hrel.transcendental (0, 0)
  exact transcendental_linearBase_zero_rigidity htrans b c hzero

/-- A real Gamma source coefficient, embedded in the analytic marginal field. -/
def eulerWickGammaSixMarginalRealConstant
    (shift : ℂ) (r : ℝ) : quadraticResidueAnalyticMarginalField shift :=
  let z : upperEndRationalCoordinateField :=
    algebraMap ℂ upperEndRationalCoordinateField (r : ℂ)
  ⟨algebraMap upperEndRationalCoordinateField upperEndMeroField z,
    (quadraticResidueAnalyticMarginalField shift).algebraMap_mem z⟩

theorem eulerWickGammaSixMarginalRealConstant_coe
    (shift : ℂ) (r : ℝ) :
    (eulerWickGammaSixMarginalRealConstant shift r : upperEndMeroField) =
      algebraMap ℂ upperEndMeroField (r : ℂ) := by
  change algebraMap upperEndRationalCoordinateField upperEndMeroField
      (algebraMap ℂ upperEndRationalCoordinateField (r : ℂ)) = _
  exact IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField upperEndMeroField _

/-- Analytic marginal image of the two linear Laurent boundary defects. -/
def eulerWickGammaSixMarginalBoundarySum
    (shift : ℂ) (a : ℝ) : quadraticResidueAnalyticMarginalField shift :=
  eulerWickGammaSixMarginalRealConstant shift
    (_root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect a +
      _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect a)

/-- Analytic marginal coefficient of the strict-inversion quadratic Laurent ghost. -/
def eulerWickGammaSixMarginalQuadraticGhost
    (shift : ℂ) (a : ℝ) : quadraticResidueAnalyticMarginalField shift :=
  eulerWickGammaSixMarginalRealConstant shift
    (_root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
      _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect a)

theorem eulerWickGammaSixMarginalQuadraticGhost_eq_zero_iff
    (shift : ℂ) (a : ℝ) :
    eulerWickGammaSixMarginalQuadraticGhost shift a = 0 ↔ a = 0 := by
  rw [eulerWickGammaSixMarginalQuadraticGhost]
  constructor
  · intro h
    have hcoe := congrArg
      (fun z : quadraticResidueAnalyticMarginalField shift => (z : upperEndMeroField)) h
    rw [eulerWickGammaSixMarginalRealConstant_coe] at hcoe
    have hconst :
        upperEndComplexToMero
            ((_root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
              _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect a : ℝ) : ℂ) =
          (0 : upperEndMeroField) := hcoe
    rw [← map_zero upperEndComplexToMero] at hconst
    have hC := upperEndComplexToMero.injective hconst
    have hR :
        _root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
          _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect a = 0 :=
      Complex.ofReal_injective (by simpa using hC)
    have hcurv : _root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 := by
      rw [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]
      linear_combination -hR
    exact (_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1
      hcurv
  · rintro rfl
    apply Subtype.ext
    simp [eulerWickGammaSixMarginalRealConstant,
      _root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- Coefficient-faithful decoration of the full Laurent strict-inversion relation: linear defects
land in the marginal field, while the quadratic ghost retains the irreducible EWQ joint carrier. -/
def EulerWickGammaSixFullSourceInteractionDescendsAt
    (shift : ℂ) (a : ℝ) : Prop :=
  (eulerWickGammaSixMarginalQuadraticGhost shift a : upperEndMeroField) *
        quadraticResidueAnalyticProductCarrier shift +
      (eulerWickGammaSixMarginalBoundarySum shift a : upperEndMeroField) = 0

/-- Hypertranscendence prevents a nonzero Laurent quadratic ghost from being absorbed by its two
linear marginals.  The decorated full-source relation descends exactly at neutral grade. -/
theorem eulerWickGammaSixFullSourceInteractionDescendsAt_iff
    (shift : ℂ) (a : ℝ) :
    EulerWickGammaSixFullSourceInteractionDescendsAt shift a ↔ a = 0 := by
  constructor
  · intro hdescent
    have hrig := quadraticResidueAnalyticProductCarrier_linearMarginal_zero_rigidity
      shift (eulerWickGammaSixMarginalQuadraticGhost shift a)
        (eulerWickGammaSixMarginalBoundarySum shift a) hdescent
    exact (eulerWickGammaSixMarginalQuadraticGhost_eq_zero_iff shift a).1 hrig.1
  · rintro rfl
    simp [EulerWickGammaSixFullSourceInteractionDescendsAt,
      eulerWickGammaSixMarginalQuadraticGhost,
      eulerWickGammaSixMarginalBoundarySum,
      eulerWickGammaSixMarginalRealConstant,
      _root_.RHTower.sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
      _root_.RHTower.sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- The undecorated Laurent evaluation closes unconditionally; its quadratic ghost is the negative
Gamma-six paired curvature. -/
theorem deningerIntegralGammaEvaluation_quadraticGhost_one_eq_neg_curvature (a : ℝ) :
    _root_.RHTower.deningerIntegralGammaEvaluation a
        (_root_.RHTower.deningerIntegralGammaMultiplicityQuadraticGhost 1) =
      -_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [_root_.RHTower.deningerIntegralGammaEvaluation_multiplicityQuadraticGhost]
  norm_num
  rw [_root_.RHTower.sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]
  ring

def EulerWickGammaSixEveryXiFullSourceInteractionDescends (shift : ℂ) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    EulerWickGammaSixFullSourceInteractionDescendsAt shift
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)

theorem eulerWickGammaSixEveryXiFullSourceInteractionDescends_iff_riemannHypothesis
    (shift : ℂ) :
    EulerWickGammaSixEveryXiFullSourceInteractionDescends shift ↔ RiemannHypothesis := by
  constructor
  · intro hdescent
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hzero := (eulerWickGammaSixFullSourceInteractionDescendsAt_iff shift
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).1 (hdescent q)
    have hline :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hzero
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSixFullSourceInteractionDescendsAt_iff shift
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).2
    exact (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1)

end

end GaloisForLFunctions.RHTower

