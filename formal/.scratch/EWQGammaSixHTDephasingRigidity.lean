import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixBistochasticRecurrence
import GaloisForLFunctions.RHTower.EulerSquarefreeWickQuadraticCharacterBridge

open GaloisForLFunctions.HTGeometry
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance eulerWickHTRigidityUpperEndAnalyticDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance eulerWickHTRigidityUpperEndMeroComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance eulerWickHTRigidityUpperEndMeroDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- A transcendental carrier admits no affine self-repair over its base field. -/
theorem transcendental_affineBase_selfRepair_rigidity
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (hx : Transcendental K x) (b c : K)
    (hrepair : algebraMap K F b * x + algebraMap K F c = x) :
    b = 1 ∧ c = 0 := by
  have hb : b = 1 := by
    by_contra hb
    have hdenK : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    have hdenF : algebraMap K F (1 - b) ≠ 0 :=
      (map_ne_zero (algebraMap K F)).2 hdenK
    have hxbase : x = algebraMap K F (c / (1 - b)) := by
      rw [map_div₀]
      apply (eq_div_iff hdenF).2
      rw [map_sub, map_one]
      linear_combination -hrepair
    exact hx (hxbase ▸ isAlgebraic_algebraMap (c / (1 - b)))
  refine ⟨hb, ?_⟩
  subst b
  have hcmap : algebraMap K F c = 0 := by
    rw [map_one, one_mul] at hrepair
    linear_combination hrepair
  exact (algebraMap K F).injective (by simpa using hcmap)

/-- Relative hypertranscendence strengthens additive marginal-counterterm blindness to full affine
rigidity: a marginal rescaling plus a marginal correction fixes the EWQ joint carrier only
trivially. -/
theorem quadraticResidueAnalyticProductCarrier_affineMarginalRepair_rigidity
    (shift : ℂ)
    (b c : quadraticResidueAnalyticMarginalField shift)
    (hrepair :
      (b : upperEndMeroField) * quadraticResidueAnalyticProductCarrier shift +
          (c : upperEndMeroField) =
        quadraticResidueAnalyticProductCarrier shift) :
    b = 1 ∧ c = 0 := by
  have hrel := quadraticResidueAnalyticProductCarrier_relativeHT shift
  unfold GaloisForLFunctions.DifferentialIndependent at hrel
  have htrans : Transcendental (quadraticResidueAnalyticMarginalField shift)
      (quadraticResidueAnalyticProductCarrier shift) := by
    simpa using hrel.transcendental (0, 0)
  exact transcendental_affineBase_selfRepair_rigidity htrans b c hrepair

def eulerWickGammaSixMarginalDephasingScalar
    (shift : ℂ) (a : ℝ) : quadraticResidueAnalyticMarginalField shift :=
  let z : upperEndRationalCoordinateField :=
    algebraMap ℂ upperEndRationalCoordinateField
      (eulerWickGammaSixDephasingFactor a : ℂ)
  ⟨algebraMap upperEndRationalCoordinateField upperEndMeroField z,
    (quadraticResidueAnalyticMarginalField shift).algebraMap_mem z⟩

theorem eulerWickGammaSixMarginalDephasingScalar_coe
    (shift : ℂ) (a : ℝ) :
    (eulerWickGammaSixMarginalDephasingScalar shift a : upperEndMeroField) =
      algebraMap ℂ upperEndMeroField (eulerWickGammaSixDephasingFactor a : ℂ) := by
  change algebraMap upperEndRationalCoordinateField upperEndMeroField
      (algebraMap ℂ upperEndRationalCoordinateField
        (eulerWickGammaSixDephasingFactor a : ℂ)) = _
  exact IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField upperEndMeroField _

/-- No analytic marginal counterterm can restore the attenuated EWQ interaction unless Gamma-six
grade is neutral. -/
theorem eulerWickGammaSix_dephasedCarrier_add_marginal_eq_iff
    (shift : ℂ) (a : ℝ) (c : quadraticResidueAnalyticMarginalField shift) :
    (eulerWickGammaSixMarginalDephasingScalar shift a : upperEndMeroField) *
          quadraticResidueAnalyticProductCarrier shift +
        (c : upperEndMeroField) =
      quadraticResidueAnalyticProductCarrier shift ↔
      a = 0 ∧ c = 0 := by
  constructor
  · intro hrepair
    have hrig := quadraticResidueAnalyticProductCarrier_affineMarginalRepair_rigidity
      shift (eulerWickGammaSixMarginalDephasingScalar shift a) c hrepair
    refine ⟨?_, hrig.2⟩
    apply (eulerWickGammaSixDephasingFactor_eq_one_iff a).1
    have hcoe := congrArg
      (fun z : quadraticResidueAnalyticMarginalField shift => (z : upperEndMeroField)) hrig.1
    rw [eulerWickGammaSixMarginalDephasingScalar_coe] at hcoe
    have hconst :
        upperEndComplexToMero (eulerWickGammaSixDephasingFactor a : ℂ) =
          (1 : upperEndMeroField) := hcoe
    rw [← map_one upperEndComplexToMero] at hconst
    have hkC : (eulerWickGammaSixDephasingFactor a : ℂ) = 1 :=
      upperEndComplexToMero.injective hconst
    exact Complex.ofReal_injective (by simpa using hkC)
  · rintro ⟨rfl, rfl⟩
    simp [eulerWickGammaSixMarginalDephasingScalar,
      eulerWickGammaSixDephasingFactor]

theorem eulerWickGammaSix_exists_marginalRepair_iff
    (shift : ℂ) (a : ℝ) :
    (∃ c : quadraticResidueAnalyticMarginalField shift,
      (eulerWickGammaSixMarginalDephasingScalar shift a : upperEndMeroField) *
            quadraticResidueAnalyticProductCarrier shift +
          (c : upperEndMeroField) =
        quadraticResidueAnalyticProductCarrier shift) ↔
      a = 0 := by
  constructor
  · rintro ⟨c, hrepair⟩
    exact (eulerWickGammaSix_dephasedCarrier_add_marginal_eq_iff
      shift a c).1 hrepair |>.1
  · intro ha
    refine ⟨0, (eulerWickGammaSix_dephasedCarrier_add_marginal_eq_iff
      shift a 0).2 ⟨ha, rfl⟩⟩

/-- Every physical Xi fibre permits a marginal repair of the Gamma-six-dephased EWQ carrier. -/
def EulerWickGammaSixPhysicalCarrierMarginallyRepairable (shift : ℂ) : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    let a := Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1
    ∃ c : quadraticResidueAnalyticMarginalField shift,
      (eulerWickGammaSixMarginalDephasingScalar shift a : upperEndMeroField) *
            quadraticResidueAnalyticProductCarrier shift +
          (c : upperEndMeroField) =
        quadraticResidueAnalyticProductCarrier shift

/-- Hypertranscendental marginal rigidity makes global repairability exactly the critical-line
condition.  A completed Xi transport producing this repairability would therefore prove RH. -/
theorem eulerWickGammaSixPhysicalCarrierMarginallyRepairable_iff_riemannHypothesis
    (shift : ℂ) :
    EulerWickGammaSixPhysicalCarrierMarginallyRepairable shift ↔ RiemannHypothesis := by
  constructor
  · intro hrepair
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hzero := (eulerWickGammaSix_exists_marginalRepair_iff shift
      (Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).1
      (hrepair q)
    have hlog : Real.log (5 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hrate : _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hlog
    have hline :=
      (_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1 hrate
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSix_exists_marginalRepair_iff shift
      (Real.log (5 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)).2
    rw [(_root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
      (_root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1), mul_zero]

end

end GaloisForLFunctions.RHTower
