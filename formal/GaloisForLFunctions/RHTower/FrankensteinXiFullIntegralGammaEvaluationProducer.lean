import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource

/-!
# Full integral Gamma evaluation producer and exact conormal obstruction

The integral Cartier source does carry an unconditional coefficient-faithful Gamma producer—but
on the full Laurent source, with its quadratic inversion ghost retained.  At clock `a`, evaluation
at `q = exp(a)` sends the forward, inverse, and quadratic representatives to

`m(exp(a)-1)`, `m(exp(-a)-1)`, and `m(exp(a)-1)(exp(-a)-1)`.

Their sum is zero because strict inversion is multiplicative.  Passing to `I/I²` deletes exactly
the third term.  This file proves that the canonical full producer factors through the additive
Cartier conormal exactly when `a=0`; on an Xi divisor and any ordinary prime, that is exactly the
critical line.  Thus full-source Gamma production is unconditional, while ghost erasure—not
source-class construction—is the RH-strength step.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry
open LaurentPolynomial

noncomputable section

/-- Positive Laurent unit used by the literal Gamma character `q ↦ exp(a)`. -/
def deningerIntegralGammaUnit (a : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp a) (Real.exp_ne_zero a)

/-- Canonical integral-source Gamma evaluation.  This is a ring map on the full Laurent source,
not an assumed additive reporter on its first conormal. -/
def deningerIntegralGammaEvaluation (a : ℝ) :
    DeningerIntegralCartierSourceRing →+* ℝ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℝ) (deningerIntegralGammaUnit a)

@[simp] theorem deningerIntegralGammaEvaluation_T_one (a : ℝ) :
    deningerIntegralGammaEvaluation a (T 1) = Real.exp a := by
  simp [deningerIntegralGammaEvaluation, deningerIntegralGammaUnit]

@[simp] theorem deningerIntegralGammaEvaluation_T_neg_one (a : ℝ) :
    deningerIntegralGammaEvaluation a (T (-1)) = Real.exp (-a) := by
  rw [deningerIntegralGammaEvaluation, LaurentPolynomial.eval₂_T]
  simp [deningerIntegralGammaUnit, Real.exp_neg]

/-- Full evaluation reads the exact forward Gamma defect. -/
theorem deningerIntegralGammaEvaluation_generator (a : ℝ) :
    deningerIntegralGammaEvaluation a deningerIntegralCartierSourceGenerator =
      sourceHorizontalGammaSixUnitForwardBoundaryDefect a := by
  rw [deningerIntegralCartierSourceGenerator, map_sub, map_one,
    deningerIntegralGammaEvaluation_T_one,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq]

/-- Full evaluation reads the exact inverse Gamma defect. -/
theorem deningerIntegralGammaEvaluation_inverseGenerator (a : ℝ) :
    deningerIntegralGammaEvaluation a
        (inversion ℤ deningerIntegralCartierSourceGenerator) =
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect a := by
  unfold deningerIntegralCartierSourceGenerator
  rw [inversion_sub_one, map_mul, map_neg,
    deningerIntegralGammaEvaluation_T_neg_one]
  change -Real.exp (-a) *
      deningerIntegralGammaEvaluation a deningerIntegralCartierSourceGenerator = _
  rw [deningerIntegralGammaEvaluation_generator,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]
  have h : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith

/-- Multiplicity-faithful forward representative before the conormal quotient. -/
def deningerIntegralGammaMultiplicityForwardRepresentative (m : ℕ) :
    DeningerIntegralCartierSourceRing :=
  m • deningerIntegralCartierSourceGenerator

/-- Multiplicity-faithful inverse representative before the conormal quotient. -/
def deningerIntegralGammaMultiplicityInverseRepresentative (m : ℕ) :
    DeningerIntegralCartierSourceRing :=
  m • inversion ℤ deningerIntegralCartierSourceGenerator

/-- Quadratic strict-inversion ghost, retained once per divisor copy. -/
def deningerIntegralGammaMultiplicityQuadraticGhost (m : ℕ) :
    DeningerIntegralCartierSourceRing :=
  m • (deningerIntegralCartierSourceGenerator *
    inversion ℤ deningerIntegralCartierSourceGenerator)

/-- Strict inversion closes only after retaining the quadratic ghost. -/
theorem deningerIntegralGammaRepresentatives_add_ghost (m : ℕ) :
    deningerIntegralGammaMultiplicityForwardRepresentative m +
        deningerIntegralGammaMultiplicityInverseRepresentative m +
      deningerIntegralGammaMultiplicityQuadraticGhost m = 0 := by
  rw [deningerIntegralGammaMultiplicityForwardRepresentative,
    deningerIntegralGammaMultiplicityInverseRepresentative,
    deningerIntegralGammaMultiplicityQuadraticGhost,
    ← smul_add, ← smul_add]
  suffices deningerIntegralCartierSourceGenerator +
      inversion ℤ deningerIntegralCartierSourceGenerator +
        deningerIntegralCartierSourceGenerator *
          inversion ℤ deningerIntegralCartierSourceGenerator = 0 by
    rw [this, smul_zero]
  unfold deningerIntegralCartierSourceGenerator
  rw [inversion_sub_one]
  let q : DeningerIntegralCartierSourceRing := T 1
  let qinv : DeningerIntegralCartierSourceRing := T (-1)
  change (q - 1) + -qinv * (q - 1) +
      (q - 1) * (-qinv * (q - 1)) = 0
  have hT : q * qinv = 1 := by
    dsimp only [q, qinv]
    rw [← LaurentPolynomial.T_add]
    simp
  calc
    (q - 1) + -qinv * (q - 1) +
          (q - 1) * (-qinv * (q - 1)) =
        (q - 1) * (1 - q * qinv) := by ring
    _ = 0 := by rw [hT]; ring

theorem deningerIntegralGammaEvaluation_multiplicityForward
    (m : ℕ) (a : ℝ) :
    deningerIntegralGammaEvaluation a
        (deningerIntegralGammaMultiplicityForwardRepresentative m) =
      (m : ℝ) * sourceHorizontalGammaSixUnitForwardBoundaryDefect a := by
  rw [deningerIntegralGammaMultiplicityForwardRepresentative, map_nsmul,
    deningerIntegralGammaEvaluation_generator]
  simp [nsmul_eq_mul]

theorem deningerIntegralGammaEvaluation_multiplicityInverse
    (m : ℕ) (a : ℝ) :
    deningerIntegralGammaEvaluation a
        (deningerIntegralGammaMultiplicityInverseRepresentative m) =
      (m : ℝ) * sourceHorizontalGammaSixUnitReflectedBoundaryDefect a := by
  rw [deningerIntegralGammaMultiplicityInverseRepresentative, map_nsmul,
    deningerIntegralGammaEvaluation_inverseGenerator]
  simp [nsmul_eq_mul]

theorem deningerIntegralGammaEvaluation_multiplicityQuadraticGhost
    (m : ℕ) (a : ℝ) :
    deningerIntegralGammaEvaluation a
        (deningerIntegralGammaMultiplicityQuadraticGhost m) =
      (m : ℝ) *
        (sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
          sourceHorizontalGammaSixUnitReflectedBoundaryDefect a) := by
  rw [deningerIntegralGammaMultiplicityQuadraticGhost, map_nsmul, map_mul,
    deningerIntegralGammaEvaluation_generator,
    deningerIntegralGammaEvaluation_inverseGenerator]
  simp [nsmul_eq_mul]

/-- Concrete source-selected producer on one Xi divisor and one ordinary-prime clock.  Unlike the
desired conormal reporter, this structure stores no existence premise: its evaluation is the
canonical Laurent character and its quadratic ghost is forced by strict inversion. -/
structure DeningerXiFullIntegralGammaProducer
    (rho : XiDivisorSupport) (p : Nat.Primes) where
  source : DeningerXiBidirectionalIntegralSourceClass rho
  evaluation : DeningerIntegralCartierSourceRing →+* ℝ
  evaluation_eq : evaluation = deningerIntegralGammaEvaluation
    (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)
  ward_identity :
    evaluation
      (deningerIntegralGammaMultiplicityForwardRepresentative
          (xiSupportMultiplicity rho)) +
      evaluation
        (deningerIntegralGammaMultiplicityInverseRepresentative
          (xiSupportMultiplicity rho)) +
      evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) = 0

/-- Every retained Xi divisor has the full coefficient-faithful Gamma producer unconditionally. -/
def deningerXiFullIntegralGammaProducer
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerXiFullIntegralGammaProducer rho p where
  source := deningerXiBidirectionalIntegralSourceClass rho
  evaluation := deningerIntegralGammaEvaluation
    (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)
  evaluation_eq := rfl
  ward_identity := by
    rw [← map_add, ← map_add, deningerIntegralGammaRepresentatives_add_ghost,
      map_zero]

theorem DeningerXiFullIntegralGammaProducer.forward_coefficient
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiFullIntegralGammaProducer rho p) :
    h.evaluation
        (deningerIntegralGammaMultiplicityForwardRepresentative
          (xiSupportMultiplicity rho)) =
      (xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitForwardBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) := by
  rw [h.evaluation_eq]
  exact deningerIntegralGammaEvaluation_multiplicityForward _ _

theorem DeningerXiFullIntegralGammaProducer.inverse_coefficient
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiFullIntegralGammaProducer rho p) :
    h.evaluation
        (deningerIntegralGammaMultiplicityInverseRepresentative
          (xiSupportMultiplicity rho)) =
      (xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) := by
  rw [h.evaluation_eq]
  exact deningerIntegralGammaEvaluation_multiplicityInverse _ _

/-- Exact coefficient of the one-copy quadratic ghost discarded by the conormal quotient. -/
theorem DeningerXiFullIntegralGammaProducer.quadraticGhost_coefficient
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiFullIntegralGammaProducer rho p) :
    h.evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) =
      (xiSupportMultiplicity rho : ℝ) *
        (sourceHorizontalGammaSixUnitForwardBoundaryDefect
            (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) *
          sourceHorizontalGammaSixUnitReflectedBoundaryDefect
            (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)) := by
  rw [h.evaluation_eq]
  exact deningerIntegralGammaEvaluation_multiplicityQuadraticGhost _ _

theorem everyXiFullIntegralGammaProducer :
    ∀ (rho : XiDivisorSupport) (p : Nat.Primes),
      Nonempty (DeningerXiFullIntegralGammaProducer rho p) := by
  intro rho p
  exact ⟨deningerXiFullIntegralGammaProducer rho p⟩

/-- Canonical full Laurent evaluation factors through the first additive Cartier conormal. -/
def DeningerIntegralGammaEvaluationDescends (a : ℝ) : Prop :=
  ∃ reporter : DeningerIntegralCartierConormal →+ ℝ,
    ∀ x : DeningerIntegralCartierSourceIdeal,
      reporter (DeningerIntegralCartierSourceIdeal.toCotangent x) =
        deningerIntegralGammaEvaluation a x.1

/-- Exact hostile classification: the unconditional full producer loses its quadratic ghost in
`I/I²` exactly at neutral Gamma clock. -/
theorem deningerIntegralGammaEvaluationDescends_iff (a : ℝ) :
    DeningerIntegralGammaEvaluationDescends a ↔ a = 0 := by
  constructor
  · rintro ⟨reporter, hreporter⟩
    let forward : DeningerIntegralCartierSourceIdeal :=
      ⟨deningerIntegralCartierSourceGenerator, generator_mem⟩
    let inverse : DeningerIntegralCartierSourceIdeal :=
      ⟨inversion ℤ deningerIntegralCartierSourceGenerator,
        inversion_mem_span⟩
    have hzero := congrArg reporter deningerIntegralCartierForward_add_inverse
    rw [map_add, map_zero, deningerIntegralCartierForwardClass,
      deningerIntegralCartierInverseClass, hreporter forward, hreporter inverse,
      deningerIntegralGammaEvaluation_generator,
      deningerIntegralGammaEvaluation_inverseGenerator] at hzero
    exact
      (sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_zero_iff a).1 hzero
  · rintro rfl
    refine ⟨0, fun x => ?_⟩
    simp only [AddMonoidHom.zero_apply]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp x.2
    rw [← hc, map_mul]
    change 0 = deningerIntegralGammaEvaluation 0 c *
      deningerIntegralGammaEvaluation 0 deningerIntegralCartierSourceGenerator
    rw [deningerIntegralGammaEvaluation_generator]
    simp [sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq]

/-- Pointwise ghost-erasure target on the actual prime-labelled Xi source. -/
def DeningerXiFullIntegralGammaProducerDescends
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  DeningerIntegralGammaEvaluationDescends
    (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)

/-- The retained ghost is not a disposable contractible pair: its canonical coefficient vanishes
exactly on the critical line. -/
theorem DeningerXiFullIntegralGammaProducer.quadraticGhost_eq_zero_iff_line
    {rho : XiDivisorSupport} {p : Nat.Primes}
    (h : DeningerXiFullIntegralGammaProducer rho p) :
    h.evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [h.quadraticGhost_coefficient, mul_eq_zero]
  have hm : (xiSupportMultiplicity rho : ℝ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  simp only [hm, false_or]
  let a : ℝ := Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho
  change sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
      sourceHorizontalGammaSixUnitReflectedBoundaryDefect a = 0 ↔ _
  have hprod :
      sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
          sourceHorizontalGammaSixUnitReflectedBoundaryDefect a = 0 ↔ a = 0 := by
    rw [← neg_eq_zero, ← neg_mul,
      ← sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects,
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff]
  rw [hprod]
  dsimp only [a]
  rw [mul_eq_zero]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  simp [hlog, primeDepthBVWoldXiCenteredRate_eq_zero_iff]

theorem deningerXiFullIntegralGammaProducerDescends_iff_line
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerXiFullIntegralGammaProducerDescends rho p ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [DeningerXiFullIntegralGammaProducerDescends,
    deningerIntegralGammaEvaluationDescends_iff, mul_eq_zero]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  simp [hlog, primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- The earlier additive reporter is exactly ghost erasure from the canonical full producer. -/
theorem xiBidirectionalIntegralGammaReporter_iff_fullProducerDescends
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    Nonempty (DeningerXiBidirectionalIntegralGammaReporter rho p) ↔
      DeningerXiFullIntegralGammaProducerDescends rho p := by
  rw [deningerXiBidirectionalIntegralGammaReporter_nonempty_iff,
    deningerXiFullIntegralGammaProducerDescends_iff_line]

/-- Global ghost erasure for the unconditional full producer remains exactly RH. -/
theorem everyXiFullIntegralGammaProducerDescends_iff_riemannHypothesis :
    (∀ (rho : XiDivisorSupport) (p : Nat.Primes),
      DeningerXiFullIntegralGammaProducerDescends rho p) ↔
        RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (deningerXiFullIntegralGammaProducerDescends_iff_line rho
      (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
        (h rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro h rho p
    exact (deningerXiFullIntegralGammaProducerDescends_iff_line rho p).2
      (xi_divisor_support_re_eq_half_of_rh h rho)

end

end RHTower
