import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion
import GaloisForLFunctions.RHTower.RiemannGammaCoPoissonHodgeGreenDescentLaw
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCompletedGreenDefect
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianLineWronskianGreenComparison

/-!
# All-cross-prime Gamma admission operator

The actual Gamma/co-Poisson polarized boundary defect at the canonical
ordered `(2,3)` Calderon--Witt witness gives a scalar on every Xi-divisor
fibre.  Dividing it by `1 + norm` produces a bounded coefficient without
changing its zero locus.  Fibrewise multiplication therefore defines a
continuous operator on the genuine all-cross-prime incidence completion.

This file determines its kernel exactly.  On the simultaneous Xi incidence
comparison, the kernel consists of vectors supported on critical-line
fibres.  Completed Green provenance has the complementary support law: its
fracture factor vanishes on those fibres.  Hence the Gamma operator is
conservative on the entire completed Green sector.

For the fixed reflected-Gaussian Green vector, annihilation by this operator
is consequently equivalent to RH.  Thus the operator constructs the
conservative half of the required transverse arithmetic annihilator, while
proving that its missing source-null-homotopy cannot be obtained by silently
declaring Gamma annihilation: that declaration already has the full logical
strength of RH.
-/

open Complex Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Actual Gamma/co-Poisson boundary reflection defect evaluated at the
canonical ordered `(2,3)` Calderon--Witt source witness. -/
def deningerCalderonWittBaseGammaBoundaryDefectCoefficient
    (r : XiZeroCopy) : ℂ :=
  deningerCalderonWittGammaPolarizedBoundaryReflectionDefect
      (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
      (deningerCalderonWittCrossPrimeGammaWitness
        deningerCalderonWittTwoThreePacketIndex.2)
      deningerCalderonWittTwoThreePacketIndex.1.1
      deningerCalderonWittTwoThreePacketIndex.1.2 0 0

/-- The base boundary coefficient is the actual Gamma/Euler reflection-odd
exterior at the `(2,3)` source witness. -/
theorem deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      (xiGammaEulerPrimitiveReflectionOddExterior
        (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
        (deningerCalderonWittTwoThreePacketIndex.1.1, 0)
        (deningerCalderonWittTwoThreePacketIndex.1.2, 0) : ℂ) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient,
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq,
    deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness]

/-- Exact zero set of the actual base Gamma boundary coefficient. -/
theorem deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq]
  constructor
  · intro h
    have hreal :
        xiGammaEulerPrimitiveReflectionOddExterior
          (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
          (deningerCalderonWittTwoThreePacketIndex.1.1, 0)
          (deningerCalderonWittTwoThreePacketIndex.1.2, 0) = 0 := by
      exact_mod_cast h
    have ha :=
      (xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
        (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
        (deningerCalderonWittTwoThreePacketIndex.1.1, 0)
        (deningerCalderonWittTwoThreePacketIndex.1.2, 0)
        (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth
          deningerCalderonWittTwoThreePacketIndex.2 0)).mp hreal
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re] at ha
    simp at ha
    linarith
  · intro hline
    have ha :
        (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re = 0 := by
      rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
      simp
      linarith
    rw [ha, xiGammaEulerPrimitiveReflectionOddExterior_zero]
    exact_mod_cast rfl

private abbrev deningerCalderonWittBaseTwoPrime : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

private abbrev deningerCalderonWittBaseThreePrime : Nat.Primes :=
  ⟨3, Nat.prime_three⟩

/-- Undeformed exterior amplitude at the canonical ordered `(2,3)` source
witness. -/
def deningerCalderonWittBaseGammaUndeformedExteriorAmplitude : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0
      (deningerCalderonWittBaseTwoPrime, 0) *
    xiGammaEulerPrimitiveBoundaryAmplitude 0
      (deningerCalderonWittBaseThreePrime, 0) *
      (xiGammaEulerBoundaryHalfHeight
          deningerCalderonWittBaseTwoPrime 0 -
        xiGammaEulerBoundaryHalfHeight
          deningerCalderonWittBaseThreePrime 0)

/-- Sum of the two canonical source modular rates. -/
def deningerCalderonWittBaseGammaTotalModularRate : ℝ :=
  xiGammaEulerPrimitiveModularRate
      (deningerCalderonWittBaseTwoPrime, 0) +
    xiGammaEulerPrimitiveModularRate
      (deningerCalderonWittBaseThreePrime, 0)

/-- The ordered `(2,3)` undeformed exterior amplitude is negative. -/
theorem deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_neg :
    deningerCalderonWittBaseGammaUndeformedExteriorAmplitude < 0 := by
  have hlog : Real.log (2 : ℝ) < Real.log (3 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hampTwo :=
    xiGammaEulerPrimitiveBoundaryAmplitude_pos 0
      (deningerCalderonWittBaseTwoPrime, 0)
  have hampThree :=
    xiGammaEulerPrimitiveBoundaryAmplitude_pos 0
      (deningerCalderonWittBaseThreePrime, 0)
  rw [deningerCalderonWittBaseGammaUndeformedExteriorAmplitude]
  have hheight :
      xiGammaEulerBoundaryHalfHeight
          deningerCalderonWittBaseTwoPrime 0 <
        xiGammaEulerBoundaryHalfHeight
          deningerCalderonWittBaseThreePrime 0 := by
    simp only [xiGammaEulerBoundaryHalfHeight]
    norm_num
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos hampTwo hampThree)
    (sub_neg.mpr hheight)

/-- The total modular rate at the canonical source witness is negative. -/
theorem deningerCalderonWittBaseGammaTotalModularRate_neg :
    deningerCalderonWittBaseGammaTotalModularRate < 0 := by
  rw [deningerCalderonWittBaseGammaTotalModularRate,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  have hTwo := xiGammaEulerBoundaryHalfHeight_pos
    (deningerCalderonWittBaseTwoPrime, 0)
  have hThree := xiGammaEulerBoundaryHalfHeight_pos
    (deningerCalderonWittBaseThreePrime, 0)
  linarith

/-- Orientation and modular rate have the same effective sign. -/
theorem
    deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_mul_totalModularRate_pos :
    0 < deningerCalderonWittBaseGammaUndeformedExteriorAmplitude *
      deningerCalderonWittBaseGammaTotalModularRate :=
  mul_pos_of_neg_of_neg
    deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_neg
    deningerCalderonWittBaseGammaTotalModularRate_neg

/-- The actual canonical Gamma reflection defect is an exterior amplitude
times one hyperbolic sine of the total modular rate. -/
theorem deningerCalderonWittBaseGammaReflectionOddExterior_eq_sinh
    (a : ℝ) :
    xiGammaEulerPrimitiveReflectionOddExterior a
        (deningerCalderonWittBaseTwoPrime, 0)
        (deningerCalderonWittBaseThreePrime, 0) =
      deningerCalderonWittBaseGammaUndeformedExteriorAmplitude *
        Real.sinh
          (a * deningerCalderonWittBaseGammaTotalModularRate) := by
  rw [xiGammaEulerPrimitiveReflectionOddExterior,
    xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  rw [Real.sinh_eq]
  simp only [deningerCalderonWittBaseGammaUndeformedExteriorAmplitude,
    deningerCalderonWittBaseGammaTotalModularRate]
  ring_nf

/-- Positive analytic gauge relating actual Gamma boundary response to the
linear Green fracture.  The value at zero is the derivative value. -/
def deningerCalderonWittBaseGammaBoundaryGreenGauge (a : ℝ) : ℝ :=
  if a = 0 then
    deningerCalderonWittBaseGammaUndeformedExteriorAmplitude *
      deningerCalderonWittBaseGammaTotalModularRate
  else
    deningerCalderonWittBaseGammaUndeformedExteriorAmplitude *
      (Real.sinh
          (a * deningerCalderonWittBaseGammaTotalModularRate) / a)

/-- The Gamma/Green comparison gauge is strictly positive at every modular
displacement, including the critical section. -/
theorem deningerCalderonWittBaseGammaBoundaryGreenGauge_pos (a : ℝ) :
    0 < deningerCalderonWittBaseGammaBoundaryGreenGauge a := by
  by_cases ha : a = 0
  · simp [deningerCalderonWittBaseGammaBoundaryGreenGauge, ha,
      deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_mul_totalModularRate_pos]
  · rw [deningerCalderonWittBaseGammaBoundaryGreenGauge, if_neg ha]
    have hquotient :
        Real.sinh
            (a * deningerCalderonWittBaseGammaTotalModularRate) / a < 0 := by
      by_cases hapos : 0 < a
      · exact div_neg_of_neg_of_pos
          (Real.sinh_neg_iff.mpr
            (mul_neg_of_pos_of_neg hapos
              deningerCalderonWittBaseGammaTotalModularRate_neg))
          hapos
      · have haneg : a < 0 :=
          lt_of_le_of_ne (le_of_not_gt hapos) ha
        exact div_neg_of_pos_of_neg
          (Real.sinh_pos_iff.mpr
            (mul_pos_of_neg_of_neg haneg
              deningerCalderonWittBaseGammaTotalModularRate_neg))
          haneg
    exact mul_pos_of_neg_of_neg
      deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_neg
      hquotient

/-- Exact positive-gauge factorization of the canonical Gamma reflection
defect by the linear Green fracture parameter. -/
theorem deningerCalderonWittBaseGammaReflectionOddExterior_eq_mul_greenGauge
    (a : ℝ) :
    xiGammaEulerPrimitiveReflectionOddExterior a
        (deningerCalderonWittBaseTwoPrime, 0)
        (deningerCalderonWittBaseThreePrime, 0) =
      a * deningerCalderonWittBaseGammaBoundaryGreenGauge a := by
  rw [deningerCalderonWittBaseGammaReflectionOddExterior_eq_sinh]
  by_cases ha : a = 0
  · simp [ha]
  · rw [deningerCalderonWittBaseGammaBoundaryGreenGauge, if_neg ha]
    field_simp

/-- Fibrewise positive source gauge comparing actual Gamma boundary response
with completed Green fracture. -/
def deningerCalderonWittGammaBoundaryGreenGauge (r : XiZeroCopy) : ℝ :=
  deningerCalderonWittBaseGammaBoundaryGreenGauge
    (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re

/-- Strict positivity of the actual fibrewise Gamma/Green gauge. -/
theorem deningerCalderonWittGammaBoundaryGreenGauge_pos (r : XiZeroCopy) :
    0 < deningerCalderonWittGammaBoundaryGreenGauge r :=
  deningerCalderonWittBaseGammaBoundaryGreenGauge_pos _

/-- **Actual Gamma/Green factorization.**  The Gamma/co-Poisson boundary
defect is the completed Green fracture times a strictly positive source
gauge.  It therefore reinforces rather than cancels horizontal orientation. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_gauge
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ) *
        (deningerCalderonWittGammaBoundaryGreenGauge r : ℂ) := by
  rw [deningerCalderonWittGammaBoundaryGreenGauge,
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq]
  change
    (xiGammaEulerPrimitiveReflectionOddExterior
      (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
      (deningerCalderonWittBaseTwoPrime, 0)
      (deningerCalderonWittBaseThreePrime, 0) : ℂ) = _
  rw [deningerCalderonWittBaseGammaReflectionOddExterior_eq_mul_greenGauge]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [Complex.ofReal_re]
  push_cast
  ring_nf

/-- Division-free comparison of actual Gamma/co-Poisson boundary response
with the fixed Gaussian cohomology Wronskian.  Both are the same Green
fracture multiplied by independent strictly positive source gauges. -/
theorem deningerCalderonWittGammaBoundary_gaussianWronskian_cross_comparison
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r *
        DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLinePairScale r =
      DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian r *
        (deningerCalderonWittGammaBoundaryGreenGauge r : ℂ) := by
  rw [
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_greenFracture_mul_gauge,
    DeningerMeyerGaussianGreen.deningerMeyerReflectedGaussianLineWronskian_eq_greenFracture_mul]
  ring_nf

/-- Bounded normalization of the actual Gamma boundary coefficient. -/
def deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient
    (r : XiZeroCopy) : ℂ :=
  deningerCalderonWittBaseGammaBoundaryDefectCoefficient r /
    ((1 + ‖deningerCalderonWittBaseGammaBoundaryDefectCoefficient r‖ : ℝ) : ℂ)

/-- Uniform unit bound for the normalized Gamma coefficient. -/
theorem norm_deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_le_one
    (r : XiZeroCopy) :
    ‖deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r‖ ≤ 1 := by
  rw [deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient,
    norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).2
    (by
      linarith
        [norm_nonneg
          (deningerCalderonWittBaseGammaBoundaryDefectCoefficient r)])

/-- Normalization preserves the exact critical-line zero set. -/
theorem deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_zero_iff
    (r : XiZeroCopy) :
    deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r = 0 ↔
      (r.1 : ℂ).re = 1 / 2 := by
  have hden :
      (((1 + ‖deningerCalderonWittBaseGammaBoundaryDefectCoefficient r‖ : ℝ) : ℂ))
        ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  rw [deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient,
    div_eq_zero_iff,
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff]
  exact or_iff_left hden

private theorem
    norm_deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_smul_le
    (r : XiZeroCopy) (v : DeningerCalderonWittCrossPrimePacketHilbert) :
    ‖deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • v‖ ≤
      ‖v‖ := by
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg v)
    (norm_deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_le_one r)

private def deningerCalderonWittAllCrossPrimeGammaAdmissionOperatorToFun
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion) :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  ⟨fun r =>
      deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • z r,
    Memℓp.mono (lp.memℓp z).norm (fun r =>
      norm_deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_smul_le
        r (z r))⟩

/-- Bounded fibrewise actual Gamma/Hardy admission operator on the genuine
all-cross-prime incidence completion. -/
def deningerCalderonWittAllCrossPrimeGammaAdmissionOperator :
    DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion →L[ℂ]
      DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion :=
  LinearMap.mkContinuous
    { toFun := deningerCalderonWittAllCrossPrimeGammaAdmissionOperatorToFun
      map_add' := fun z w => by
        apply lp.ext
        funext r
        change
          deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r •
              (z r + w r) =
            deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • z r +
              deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • w r
        exact smul_add _ _ _
      map_smul' := fun c z => by
        apply lp.ext
        funext r
        change
          deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r •
              (c • z r) =
            c •
              (deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • z r)
        simp [smul_smul, mul_comm] }
    1 (fun z => by
      have hmono :
          ‖deningerCalderonWittAllCrossPrimeGammaAdmissionOperatorToFun z‖ ≤
            ‖z‖ :=
        lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun r =>
          norm_deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_smul_le
            r (z r))
      simpa using hmono)

@[simp]
theorem deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_apply
    (z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion)
    (r : XiZeroCopy) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator z r =
      deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r • z r :=
  rfl

/-- Completed Xi coefficient vectors supported on critical-line fibres. -/
def DeningerCalderonWittCriticalLineSupported :
    Submodule ℂ DeningerArithmeticCompletedH1 where
  carrier := {x | ∀ r, (r.1 : ℂ).re ≠ 1 / 2 → x r = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy r hr
    simp [hx r hr, hy r hr]
  smul_mem' := by
    intro c x hx r hr
    simp [hx r hr]

/-- Exact kernel of Gamma admission after the all-cross-prime Xi comparison:
only critical-line-supported coefficient vectors survive. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_comparison_eq_zero_iff
    (x : DeningerArithmeticCompletedH1) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x) = 0 ↔
      x ∈ DeningerCalderonWittCriticalLineSupported := by
  constructor
  · intro h r hr
    have hq := congrArg
      (fun z : DeningerCalderonWittAllCrossPrimeXiIncidenceCompletion =>
        z r deningerCalderonWittTwoThreePacketIndex) h
    rw [deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_apply] at hq
    change
      deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r *
          (x r * deningerCalderonWittCrossPrimePacketHorizon
            deningerCalderonWittTwoThreePacketIndex) = 0 at hq
    have hm :
        deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r ≠ 0 := by
      rw [ne_eq,
        deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_zero_iff]
      exact hr
    have hxeta := (mul_eq_zero.mp hq).resolve_left hm
    exact (mul_eq_zero.mp hxeta).resolve_right
      (deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero _)
  · intro hx
    apply lp.ext
    funext r
    rw [deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_apply]
    by_cases hr : (r.1 : ℂ).re = 1 / 2
    · rw [
        (deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient_eq_zero_iff r).2
          hr,
        zero_smul]
      rfl
    · change
        deningerCalderonWittNormalizedBaseGammaBoundaryDefectCoefficient r •
          (x r • deningerCalderonWittCrossPrimePacketHorizon) = 0
      rw [hx r hr, zero_smul, smul_zero]

/-- Completed Xi coefficient vectors vanishing on critical-line fibres. -/
def DeningerCalderonWittCriticalLineVanishing :
    Submodule ℂ DeningerArithmeticCompletedH1 where
  carrier := {x | ∀ r, (r.1 : ℂ).re = 1 / 2 → x r = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy r hr
    simp [hx r hr, hy r hr]
  smul_mem' := by
    intro c x hx r hr
    simp [hx r hr]

/-- Gamma admission is conservative on the critical-line-vanishing sector:
that sector meets its comparison kernel only at zero. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_comparison_eq_zero_iff_of_criticalLineVanishing
    (x : DeningerArithmeticCompletedH1)
    (hx : x ∈ DeningerCalderonWittCriticalLineVanishing) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison x) = 0 ↔
      x = 0 := by
  constructor
  · intro hA
    have hs : x ∈ DeningerCalderonWittCriticalLineSupported :=
      (deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_comparison_eq_zero_iff
        x).1 hA
    apply lp.ext
    funext r
    by_cases hr : (r.1 : ℂ).re = 1 / 2
    · exact hx r hr
    · exact hs r hr
  · intro hxzero
    rw [hxzero,
      map_zero deningerCalderonWittAllCrossPrimeXiIncidenceComparison,
      map_zero deningerCalderonWittAllCrossPrimeGammaAdmissionOperator]

/-- Every completed Green provenance has the complementary support law:
its fracture factor vanishes on critical-line fibres. -/
theorem
    deningerArithmeticCompletedGreenProvenance_mem_deningerCalderonWittCriticalLineVanishing
    (a : XiDivisorL2) :
    DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a ∈
      DeningerCalderonWittCriticalLineVanishing := by
  intro r hr
  rw [DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance_apply,
    (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (r.1 : ℂ)).2 hr,
    zero_mul]

/-- Exact Green-sector conservativity of the actual Gamma/Hardy detector. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_greenProvenance_eq_zero_iff
    (a : XiDivisorL2) :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a)) = 0 ↔
      DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance a = 0 := by
  exact
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_comparison_eq_zero_iff_of_criticalLineVanishing
      _
      (deningerArithmeticCompletedGreenProvenance_mem_deningerCalderonWittCriticalLineVanishing
        a)

/-- For the fixed source-defined Green vector, Gamma/Hardy annihilation is
not a free source identity: it is logically equivalent to RH. -/
theorem
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_reflectedGaussianGreen_eq_zero_iff_riemannHypothesis :
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance) = 0 ↔
      RiemannHypothesis := by
  change
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator
        (deningerCalderonWittAllCrossPrimeXiIncidenceComparison
          (DeningerMeyerGaussianGreen.deningerArithmeticCompletedGreenProvenance
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)) = 0 ↔
      RiemannHypothesis
  rw [
    deningerCalderonWittAllCrossPrimeGammaAdmissionOperator_greenProvenance_eq_zero_iff]
  simpa [DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance] using
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis

end

end RHTower
