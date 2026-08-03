import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCountertransportXiCapacity
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGreenParityObstruction

/-!
# Anti-reflected Gaussian countertransport and the missing odd multiplier

The reflection-fixed Gaussian also has an antisymmetric two-sided centered
countertransport

`A_c = V_c h - V_{-c} h`.

It is anti-fixed by Paugam reflection and has the same unconditional,
depth-uniform half-density capacity bound `2` as the symmetric
countertransport.  Its Mellin character is the odd centered-flow factor

`exp(c(s-1/2)) - exp(-c(s-1/2))`.

For every fixed nonzero depth this character is nonzero at every off-critical
divisor point.  At depth one it therefore supplies a source-native
reflection-odd grade which is nonzero on the support of the actual reflected
Green defect.  Multiplying the reflection-even Green record by this grade
produces a reflection-odd, pointwise faithful record.  The final theorem
isolates the sole remaining incidence: if this explicit product factors
through any reflection-invariant arithmetic observation, RH follows.

No RH premise, divisor-selected damping, or computation is used.
-/

open Complex Function Set Topology MeasureTheory
open scoped Real
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Antisymmetric two-sided centered countertransport of the reflected
log-Gaussian. -/
def deningerMeyerAntiReflectedGaussianCountertransport (c : ℝ) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogCenteredFlow c
      deningerMeyerReflectedLogGaussianSource -
    deningerMeyerStrongLogCenteredFlow (-c)
      deningerMeyerReflectedLogGaussianSource

/-- Paugam reflection reverses the antisymmetric countertransport. -/
theorem deningerMeyerAntiReflectedGaussianCountertransport_J_antiFixed
    (c : ℝ) :
    deningerMeyerStrongLogJ
        (deningerMeyerAntiReflectedGaussianCountertransport c) =
      -deningerMeyerAntiReflectedGaussianCountertransport c := by
  rw [deningerMeyerAntiReflectedGaussianCountertransport,
    LinearMap.map_sub, deningerMeyerStrongLogJ_centeredFlow,
    deningerMeyerStrongLogJ_centeredFlow,
    deningerMeyerReflectedLogGaussianSource_J_fixed, neg_neg]
  module

/-- **Uniform odd-sector source capacity.**  Every real depth has
half-density capacity at most two. -/
theorem deningerMeyerAntiReflectedGaussianCountertransport_uniform_capacity
    (c : ℝ) :
    deningerMeyerHalfDensityL1Seminorm
        (deningerMeyerAntiReflectedGaussianCountertransport c) ≤ 2 := by
  calc
    deningerMeyerHalfDensityL1Seminorm
        (deningerMeyerAntiReflectedGaussianCountertransport c) ≤
      deningerMeyerHalfDensityL1Seminorm
          (deningerMeyerStrongLogCenteredFlow c
            deningerMeyerReflectedLogGaussianSource) +
        deningerMeyerHalfDensityL1Seminorm
          (deningerMeyerStrongLogCenteredFlow (-c)
            deningerMeyerReflectedLogGaussianSource) :=
      map_sub_le_add _ _ _
    _ = 2 := by
      rw [deningerMeyerHalfDensityL1Seminorm_centeredFlow,
        deningerMeyerHalfDensityL1Seminorm_centeredFlow,
        deningerMeyerReflectedLogGaussian_halfDensityL1]
      norm_num

/-- Exact sinh-type Mellin profile of the antisymmetric countertransport. -/
theorem deningerMeyerAntiReflectedGaussianCountertransport_mellin
    (c : ℝ) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerAntiReflectedGaussianCountertransport c) s =
      (Complex.exp ((c : ℂ) * (s - 1 / 2)) -
        Complex.exp (-(c : ℂ) * (s - 1 / 2))) *
        Complex.exp ((s - 1 / 2) ^ 2 / (4 * π)) := by
  change (deningerMeyerStrongLogMellinLM s)
      (deningerMeyerStrongLogCenteredFlow c
          deningerMeyerReflectedLogGaussianSource -
        deningerMeyerStrongLogCenteredFlow (-c)
          deningerMeyerReflectedLogGaussianSource) = _
  rw [(deningerMeyerStrongLogMellinLM s).map_sub,
    show (deningerMeyerStrongLogMellinLM s)
        (deningerMeyerStrongLogCenteredFlow c
          deningerMeyerReflectedLogGaussianSource) =
        deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogCenteredFlow c
            deningerMeyerReflectedLogGaussianSource) s by rfl,
    show (deningerMeyerStrongLogMellinLM s)
        (deningerMeyerStrongLogCenteredFlow (-c)
          deningerMeyerReflectedLogGaussianSource) =
        deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogCenteredFlow (-c)
            deningerMeyerReflectedLogGaussianSource) s by rfl,
    deningerMeyerStrongLogMellin_centeredFlow,
    deningerMeyerStrongLogMellin_centeredFlow,
    deningerMeyerReflectedLogGaussianSource_mellin]
  push_cast
  ring

/-- Literal Meyer middle class of the odd countertransport. -/
def deningerMeyerAntiReflectedGaussianCountertransportClass (c : ℝ) :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk
    (deningerMeyerAntiReflectedGaussianCountertransport c)

/-- The literal class stays in the anti-reflected Hodge sector. -/
theorem deningerMeyerAntiReflectedGaussianCountertransportClass_J_antiFixed
    (c : ℝ) :
    deningerMeyerStrongLogCohomologyJ
        (deningerMeyerAntiReflectedGaussianCountertransportClass c) =
      -deningerMeyerAntiReflectedGaussianCountertransportClass c := by
  rw [deningerMeyerAntiReflectedGaussianCountertransportClass,
    deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerAntiReflectedGaussianCountertransport_J_antiFixed]
  rfl

/-- Uniform capacity survives passage to literal Meyer cohomology. -/
theorem
    deningerMeyerAntiReflectedGaussianCountertransportClass_uniform_capacity
    (c : ℝ) :
    deningerMeyerHalfDensityCohomologySeminorm
        (deningerMeyerAntiReflectedGaussianCountertransportClass c) ≤ 2 := by
  exact
    (deningerQuotientSeminorm_mk_le
      (LinearMap.range deningerMeyerStrongLogSumLM)
      deningerMeyerHalfDensityL1Seminorm
      (deningerMeyerAntiReflectedGaussianCountertransport c)).trans
        (deningerMeyerAntiReflectedGaussianCountertransport_uniform_capacity c)

/-- Exact actual Xi evaluation of the odd countertransport class. -/
theorem deningerMeyerAntiReflectedGaussianCountertransportClass_evaluation
    (rho : XiDivisorSupport) (c : ℝ) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerAntiReflectedGaussianCountertransportClass c) =
      (Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) -
        Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))) *
        Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π)) := by
  rw [deningerMeyerAntiReflectedGaussianCountertransportClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerAntiReflectedGaussianCountertransport_mellin c (rho : ℂ)

namespace DeningerMeyerGaussianGreen

/-- Odd centered-flow character on one multiplicity-exact Xi copy. -/
def deningerMeyerAntiReflectedGaussianXiMultiplier
    (c : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2)) -
    Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- Fixed-depth coordinate bound, sufficient for global Gaussian landing. -/
theorem norm_deningerMeyerAntiReflectedGaussianXiMultiplier_le
    (c : ℝ) (q : XiZeroCopy) :
    ‖deningerMeyerAntiReflectedGaussianXiMultiplier c q‖ ≤
      2 * Real.exp (|c| / 2) := by
  have hrange := xi_divisor_support_re_mem_open_unit q.1
  have habs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hrange.1, hrange.2]
  have hmul (d : ℝ) :
      d * ((q.1 : ℂ).re - 1 / 2) ≤ |d| / 2 := by
    calc
      d * ((q.1 : ℂ).re - 1 / 2) ≤
          |d * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
      _ = |d| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
      _ ≤ |d| * (1 / 2) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg d)
      _ = |d| / 2 := by ring
  have hpos :
      ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        Real.exp (|c| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using hmul c
  have hneg :
      ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        Real.exp (|c| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := hmul (-c)
    simpa [Complex.mul_re, abs_neg] using h
  calc
    ‖deningerMeyerAntiReflectedGaussianXiMultiplier c q‖ ≤
        ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ +
          ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
      norm_sub_le _ _
    _ ≤ Real.exp (|c| / 2) + Real.exp (|c| / 2) :=
      add_le_add hpos hneg
    _ = 2 * Real.exp (|c| / 2) := by ring

/-- Reflection negates the centered-flow character. -/
theorem deningerMeyerAntiReflectedGaussianXiMultiplier_reflect
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerAntiReflectedGaussianXiMultiplier c
        (xiZeroCopyReflectEquiv q) =
      -deningerMeyerAntiReflectedGaussianXiMultiplier c q := by
  rw [deningerMeyerAntiReflectedGaussianXiMultiplier,
    deningerMeyerAntiReflectedGaussianXiMultiplier]
  have hreflect :
      ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  rw [hreflect]
  have hpos : (c : ℂ) * (1 - (q.1 : ℂ) - 1 / 2) =
      -(c : ℂ) * ((q.1 : ℂ) - 1 / 2) := by ring
  have hneg : -(c : ℂ) * (1 - (q.1 : ℂ) - 1 / 2) =
      (c : ℂ) * ((q.1 : ℂ) - 1 / 2) := by ring
  rw [hpos, hneg]
  ring

/-- A nonzero real flow depth has nonzero odd character at every off-line
divisor copy. -/
theorem deningerMeyerAntiReflectedGaussianXiMultiplier_ne_zero_of_re_ne_half
    {c : ℝ} (hc : c ≠ 0) (q : XiZeroCopy)
    (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    deningerMeyerAntiReflectedGaussianXiMultiplier c q ≠ 0 := by
  intro hzero
  have hexp :
      Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2)) =
        Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2)) :=
    sub_eq_zero.mp hzero
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, Complex.norm_exp] at hnorm
  have hre := Real.exp_injective hnorm
  have hmul : c * ((q.1 : ℂ).re - 1 / 2) = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, neg_zero, zero_mul, sub_zero,
      Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hre
    nlinarith
  rcases mul_eq_zero.mp hmul with hc0 | hq0
  · exact hc hc0
  · apply hq
    linarith

/-- Global multiplicity-exact landing of the odd source packet. -/
def deningerMeyerAntiReflectedGaussianXiField (c : ℝ) : XiDivisorL2 :=
  ⟨fun q =>
      deningerMeyerAntiReflectedGaussianXiMultiplier c q *
        reflectedGaussianHorizonGrade q,
    Memℓp.mono
      ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul
        (2 * Real.exp (|c| / 2) : ℝ))
      (fun q => by
        rw [norm_mul, Pi.smul_apply, smul_eq_mul,
          reflectedGaussianHorizonGradeL2_apply]
        exact mul_le_mul_of_nonneg_right
          (norm_deningerMeyerAntiReflectedGaussianXiMultiplier_le c q)
          (norm_nonneg _))⟩

@[simp]
theorem deningerMeyerAntiReflectedGaussianXiField_apply
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerAntiReflectedGaussianXiField c q =
      deningerMeyerAntiReflectedGaussianXiMultiplier c q *
        reflectedGaussianHorizonGrade q := rfl

/-- Every global coordinate is the literal source evaluation. -/
theorem deningerMeyerAntiReflectedGaussianXiField_source_evaluation
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerAntiReflectedGaussianXiField c q =
      deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1)
        (deningerMeyerAntiReflectedGaussianCountertransportClass c) := by
  rw [deningerMeyerAntiReflectedGaussianXiField_apply,
    deningerMeyerAntiReflectedGaussianCountertransportClass_evaluation,
    deningerMeyerAntiReflectedGaussianXiMultiplier,
    reflectedGaussianHorizonGrade,
    deningerMeyerReflectedLogGaussianSource_mellin]

/-- The global source packet lies in the odd reflection sector. -/
theorem deningerMeyerAntiReflectedGaussianXiField_reflect
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerAntiReflectedGaussianXiField c
        (xiZeroCopyReflectEquiv q) =
      -deningerMeyerAntiReflectedGaussianXiField c q := by
  rw [deningerMeyerAntiReflectedGaussianXiField_apply,
    deningerMeyerAntiReflectedGaussianXiField_apply,
    deningerMeyerAntiReflectedGaussianXiMultiplier_reflect,
    reflectedGaussianHorizonGrade_reflect]
  ring

/-- Canonical source-native odd grade, taken at unit centered-flow depth. -/
def deningerMeyerAntiReflectedGaussianOddXiGrade : XiDivisorL2 :=
  deningerMeyerAntiReflectedGaussianXiField 1

/-- The canonical odd grade is nonzero wherever the divisor is off line. -/
theorem deningerMeyerAntiReflectedGaussianOddXiGrade_ne_zero_of_re_ne_half
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    deningerMeyerAntiReflectedGaussianOddXiGrade q ≠ 0 := by
  rw [deningerMeyerAntiReflectedGaussianOddXiGrade,
    deningerMeyerAntiReflectedGaussianXiField_apply]
  exact mul_ne_zero
    (deningerMeyerAntiReflectedGaussianXiMultiplier_ne_zero_of_re_ne_half
      (by norm_num) q hq)
    (reflectedGaussianHorizonGrade_ne_zero q)

/-- The canonical unit-depth odd grade reverses under reflection. -/
theorem deningerMeyerAntiReflectedGaussianOddXiGrade_reflect
    (q : XiZeroCopy) :
    deningerMeyerAntiReflectedGaussianOddXiGrade
        (xiZeroCopyReflectEquiv q) =
      -deningerMeyerAntiReflectedGaussianOddXiGrade q := by
  exact deningerMeyerAntiReflectedGaussianXiField_reflect 1 q

/-- Explicit third odd grade multiplied by the actual reflection-even Green
coefficient. -/
def adaptivePrimeNormalAntiReflectedGreenOddProduct
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  deningerMeyerAntiReflectedGaussianOddXiGrade q *
    adaptivePrimeNormalReflectedHorizonGreenCoefficient p q

/-- The explicit source/Green product is reflection-odd. -/
theorem adaptivePrimeNormalAntiReflectedGreenOddProduct_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalAntiReflectedGreenOddProduct p
        (xiZeroCopyReflectEquiv q) =
      -adaptivePrimeNormalAntiReflectedGreenOddProduct p q := by
  rw [adaptivePrimeNormalAntiReflectedGreenOddProduct,
    adaptivePrimeNormalAntiReflectedGreenOddProduct,
    deningerMeyerAntiReflectedGaussianOddXiGrade_reflect,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient]
  change
    -deningerMeyerAntiReflectedGaussianOddXiGrade q *
        adaptivePrimeNormalReflectedHorizonGreenProvenance p
          (xiZeroCopyReflectEquiv q) = _
  rw [adaptivePrimeNormalReflectedHorizonGreenProvenance_reflect]
  ring

/-- The odd product loses no off-line Green support. -/
theorem adaptivePrimeNormalAntiReflectedGreenOddProduct_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalAntiReflectedGreenOddProduct p q = 0 ↔
      adaptivePrimeNormalReflectedHorizonGreenCoefficient p q = 0 := by
  constructor
  · intro hzero
    by_contra hgreen
    have hq : (q.1 : ℂ).re ≠ 1 / 2 := by
      intro hline
      exact hgreen
        ((adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff
          p q).2 hline)
    exact (mul_ne_zero
      (deningerMeyerAntiReflectedGaussianOddXiGrade_ne_zero_of_re_ne_half
        q hq)
      hgreen) hzero
  · intro hzero
    rw [adaptivePrimeNormalAntiReflectedGreenOddProduct, hzero, mul_zero]

/-- Pointwise zero set of the explicit odd product is exactly the critical
line. -/
theorem adaptivePrimeNormalAntiReflectedGreenOddProduct_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalAntiReflectedGreenOddProduct p q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [adaptivePrimeNormalAntiReflectedGreenOddProduct_eq_zero_iff,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff]

/-- **Explicit odd-multiplier reduction.**  The source packet, its uniform
capacity, its global landing, oddness, and support faithfulness are all
unconditional.  If its product with the actual Green record factors through
any reflection-invariant arithmetic observation, RH follows. -/
theorem riemannHypothesis_of_antiReflectedGreenOddProduct_factorization
    {Q : Type*} (p : Nat.Primes) (obs : XiZeroCopy → Q) (d : Q → ℂ)
    (hobs : ∀ q : XiZeroCopy,
      obs (xiZeroCopyReflectEquiv q) = obs q)
    (hfactor : ∀ q : XiZeroCopy,
      adaptivePrimeNormalAntiReflectedGreenOddProduct p q = d (obs q)) :
    RiemannHypothesis := by
  rw [←
    adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis
      p]
  apply lp.ext
  funext q
  change adaptivePrimeNormalReflectedHorizonGreenCoefficient p q = 0
  apply
    (adaptivePrimeNormalAntiReflectedGreenOddProduct_eq_zero_iff p q).mp
  have heven :
      adaptivePrimeNormalAntiReflectedGreenOddProduct p
          (xiZeroCopyReflectEquiv q) =
        adaptivePrimeNormalAntiReflectedGreenOddProduct p q := by
    rw [hfactor, hfactor, hobs]
  rw [adaptivePrimeNormalAntiReflectedGreenOddProduct_reflect] at heven
  linear_combination (-1 / 2 : ℂ) * heven

end DeningerMeyerGaussianGreen

end

end RHTower
