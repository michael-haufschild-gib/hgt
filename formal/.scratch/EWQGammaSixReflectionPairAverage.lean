import GaloisForLFunctions.RHTower.EulerSquarefreeWickGammaSixBistochasticRecurrence

open Complex Matrix
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder MatrixOrder

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Normalized average of the positive half-density landings at reciprocal horizontal grades. -/
def eulerWickGammaSixReflectionPairAverage (a : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (((2 * Real.cosh a)⁻¹ : ℝ) : ℂ) •
    (eulerWickGammaSixHalfDensityCongruence a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) +
      eulerWickGammaSixHalfDensityCongruence (-a)
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne))

/-- Reflection-pair averaging is exactly the balanced Gamma-six dephasing channel. -/
theorem eulerWickGammaSixReflectionPairAverage_eq_dephasing (a : ℝ) :
    eulerWickGammaSixReflectionPairAverage a =
      eulerWickGammaSixBalancedDephasing a
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) := by
  have hcosh : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  have hsumC : Complex.exp (a : ℂ) + Complex.exp (-(a : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hneg : -(a : ℂ) = ((-a : ℝ) : ℂ) := by push_cast; rfl
    rw [hneg] at hre
    simp only [add_re, zero_re, Complex.exp_ofReal_re] at hre
    linarith [Real.exp_pos a, Real.exp_pos (-a)]
  rw [eulerWickGammaSixReflectionPairAverage,
    eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq,
    eulerWickGammaSixHalfDensityCongruence_projector_thirteen_eq]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [eulerWickGammaSixBalancedDephasing_apply,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_thirteen,
      eulerWickGammaSixDephasingFactor, Real.cosh_eq]
  all_goals
    field_simp [hcosh, hsumC]
  all_goals ring

/-- The normalized positive reflection-pair state remains pure exactly at neutral grade. -/
theorem eulerWickGammaSixReflectionPairAverage_eq_source_iff (a : ℝ) :
    eulerWickGammaSixReflectionPairAverage a =
        eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne ↔
      a = 0 := by
  rw [eulerWickGammaSixReflectionPairAverage_eq_dephasing]
  constructor
  · intro h
    have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
    simp [eulerWickGammaSixBalancedDephasing_apply,
      eulerWickReplicaPureProjector_apply,
      eulerWickQuadraticDepthCharacter_thirteen] at h01
    apply (eulerWickGammaSixDephasingFactor_eq_one_iff a).1
    exact h01
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [eulerWickGammaSixBalancedDephasing_apply,
        eulerWickGammaSixDephasingFactor]

/-- The reflected Xi support point supplies the negative horizontal grade in the pair average. -/
theorem eulerWickGammaSixHalfDensityCongruence_reflected_grade
    (rho : _root_.RHTower.XiDivisorSupport) :
    eulerWickGammaSixHalfDensityCongruence
        (Real.log (13 : ℝ) *
          _root_.RHTower.primeDepthBVWoldXiCenteredRate
            (_root_.RHTower.xiZeroLineConjEquiv rho))
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) =
      eulerWickGammaSixHalfDensityCongruence
        (-(Real.log (13 : ℝ) *
          _root_.RHTower.primeDepthBVWoldXiCenteredRate rho))
        (eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne) := by
  rw [_root_.RHTower.primeDepthBVWoldXiCenteredRate_reflection]
  ring_nf

/-- Actual Xi reflection-orbit average of the two positive coefficient-faithful EWQ landings. -/
def eulerWickGammaSixXiReflectionPairAverage
    (q : _root_.RHTower.XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℂ :=
  eulerWickGammaSixReflectionPairAverage
    (Real.log (13 : ℝ) * _root_.RHTower.primeDepthBVWoldXiCenteredRate q.1)

theorem eulerWickGammaSixXiReflectionPairAverage_eq_source_iff
    (q : _root_.RHTower.XiZeroCopy) :
    eulerWickGammaSixXiReflectionPairAverage q =
        eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [eulerWickGammaSixXiReflectionPairAverage,
    eulerWickGammaSixReflectionPairAverage_eq_source_iff]
  have hlog : Real.log (13 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [mul_eq_zero]
  simp only [hlog, false_or]
  exact _root_.RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1

def EveryEulerWickGammaSixXiReflectionPairAverageIsPure : Prop :=
  ∀ q : _root_.RHTower.XiZeroCopy,
    eulerWickGammaSixXiReflectionPairAverage q =
      eulerWickReplicaPureProjector eulerWickPrimeThirteenDepthOne

theorem everyEulerWickGammaSixXiReflectionPairAverageIsPure_iff_riemannHypothesis :
    EveryEulerWickGammaSixXiReflectionPairAverageIsPure ↔ RiemannHypothesis := by
  constructor
  · intro hpure
    apply _root_.RHTower.riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline := (eulerWickGammaSixXiReflectionPairAverage_eq_source_iff q).1 (hpure q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [_root_.RHTower.xiSpectralPoint]
    · simp [_root_.RHTower.xiSpectralPoint, hline]
  · intro hRH q
    apply (eulerWickGammaSixXiReflectionPairAverage_eq_source_iff q).2
    exact _root_.RHTower.xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end GaloisForLFunctions.RHTower
