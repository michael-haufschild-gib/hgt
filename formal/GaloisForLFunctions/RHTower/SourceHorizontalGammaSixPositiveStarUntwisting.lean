import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCovariantStokesFlat
import GaloisForLFunctions.RHTower.FrankensteinXiFullIntegralGammaEvaluationProducer

/-!
# Positive-star untwisting of the Gamma-six cyclic character

The covariant cyclic character is Stokes-flat for every horizontal grade, so flatness alone cannot
trivialize its local-system holonomy.  This file identifies the smallest additional source law
which does: positivity on one literal Hermitian square.

For the cyclic generator `t`, the source square is

`(t⁻¹ - 1)(t - 1)`.

Physical evaluation at holonomy `exp(a)` sends it to

`(exp(-a) - 1)(exp(a) - 1) = -2(cosh(a)-1)`.

Thus source-star positivity and the already-proved opposite-boundary positivity have opposite
signs, and their common radical is exactly `a = 0`.  The same square is the integral Cartier
quadratic ghost, so the theorem retains prime labels and Xi divisor multiplicity.  An explicit
nonneutral counterexample proves covariant Stokes flatness does not itself imply untwisting.

No positivity premise is manufactured here: global physical positivity on this square is proved
equivalent to RH.  The unconditional contribution is the exact one-square untwisting theorem and
the sharp sign obstruction any genuine source-positive producer must overcome.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Literal cyclic Hermitian square -/

/-- Forward augmentation difference `t - 1` in the Gamma-six cyclic group algebra. -/
def sourceHorizontalGammaSixCyclicForwardDifference :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) 1 -
    MonoidAlgebra.single 1 1

/-- Inverse augmentation difference `t⁻¹ - 1`. -/
def sourceHorizontalGammaSixCyclicInverseDifference :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  MonoidAlgebra.single
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv)⁻¹ 1 -
    MonoidAlgebra.single 1 1

/-- Canonical source Hermitian square `(t⁻¹ - 1)(t - 1)`. -/
def sourceHorizontalGammaSixCyclicHermitianSquare :
    MonoidAlgebra ℝ SourceHorizontalGammaSixCyclicGroup :=
  sourceHorizontalGammaSixCyclicInverseDifference *
    sourceHorizontalGammaSixCyclicForwardDifference

/-- Physical evaluation of the source Hermitian square is minus the positive paired Gamma
curvature.  This is the exact sign wall behind untwisting. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare
    (a : ℝ) :
    sourceHorizontalGammaSixCyclicCharacterReadout a
        sourceHorizontalGammaSixCyclicHermitianSquare =
      -sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [sourceHorizontalGammaSixCyclicHermitianSquare,
    sourceHorizontalGammaSixCyclicInverseDifference,
    sourceHorizontalGammaSixCyclicForwardDifference]
  simp only [sub_mul, mul_sub, MonoidAlgebra.single_mul_single, one_mul,
    map_sub, sourceHorizontalGammaSixCyclicCharacterReadout_single]
  have hgen : Multiplicative.toAdd
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv) = (1 : ℤ) := rfl
  have hgenInv : Multiplicative.toAdd
      (deningerZGen sourceHorizontalGammaSixCyclicGroupEquiv)⁻¹ = (-1 : ℤ) := rfl
  simp [hgen, hgenInv]
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    Real.cosh_eq]
  ring

/-- Positivity on this single Hermitian square forces and is forced by trivial holonomy. -/
theorem sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare_nonneg_iff
    (a : ℝ) :
    0 ≤ sourceHorizontalGammaSixCyclicCharacterReadout a
        sourceHorizontalGammaSixCyclicHermitianSquare ↔ a = 0 := by
  rw [sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare]
  constructor
  · intro h
    have hle : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a ≤ 0 := by
      linarith
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1
      (le_antisymm hle
        (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg a))
  · rintro rfl
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-! ## Integral Cartier identification -/

/-- Integral Laurent presentation of the same Hermitian square. -/
def sourceHorizontalGammaSixIntegralHermitianSquare :
    DeningerIntegralCartierSourceRing :=
  deningerIntegralCartierSourceGenerator *
    inversion ℤ deningerIntegralCartierSourceGenerator

/-- The integral Hermitian square is literally the one-copy quadratic inversion ghost. -/
theorem sourceHorizontalGammaSixIntegralHermitianSquare_eq_quadraticGhost :
    sourceHorizontalGammaSixIntegralHermitianSquare =
      deningerIntegralGammaMultiplicityQuadraticGhost 1 := by
  simp [sourceHorizontalGammaSixIntegralHermitianSquare,
    deningerIntegralGammaMultiplicityQuadraticGhost]

/-- Full integral Gamma evaluation has the same negative-curvature sign. -/
theorem deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature
    (a : ℝ) :
    deningerIntegralGammaEvaluation a
        sourceHorizontalGammaSixIntegralHermitianSquare =
      -sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
  rw [sourceHorizontalGammaSixIntegralHermitianSquare, map_mul,
    deningerIntegralGammaEvaluation_generator,
    deningerIntegralGammaEvaluation_inverseGenerator,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]
  ring

/-- One-square positivity of the full integral evaluation is also exactly neutral grade. -/
theorem deningerIntegralGammaEvaluation_hermitianSquare_nonneg_iff
    (a : ℝ) :
    0 ≤ deningerIntegralGammaEvaluation a
        sourceHorizontalGammaSixIntegralHermitianSquare ↔ a = 0 := by
  rw [deningerIntegralGammaEvaluation_hermitianSquare_eq_neg_curvature]
  constructor
  · intro h
    have hle : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a ≤ 0 := by
      linarith
    have hz : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a = 0 :=
      le_antisymm hle (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg a)
    exact (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff a).1 hz
  · rintro rfl
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

/-! ## Xi-selected untwisting -/

/-- Minimal Xi-selected positive-star law: the literal physical character is nonnegative on the
one canonical cyclic Hermitian square. -/
def SourceHorizontalGammaSixPhysicalStarPositive (q : XiZeroCopy) : Prop :=
  0 ≤ sourceHorizontalGammaSixCyclicCharacterReadout
      (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))
      sourceHorizontalGammaSixCyclicHermitianSquare

/-- Xi-selected one-square positivity is exactly critical-line placement. -/
theorem sourceHorizontalGammaSixPhysicalStarPositive_iff_line
    (q : XiZeroCopy) :
    SourceHorizontalGammaSixPhysicalStarPositive q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [SourceHorizontalGammaSixPhysicalStarPositive,
    sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare_nonneg_iff,
    sourceHorizontalGammaSixPhysicalCharacterParameter]
  have hlog : Real.log (6 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · intro h
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((mul_eq_zero.mp h).resolve_right hlog)
  · intro h
    rw [h]
    norm_num

/-- **Untwisting theorem.** Positive-star evaluation of one literal source square is equivalent
to equality of the physical covariant boundary and the fixed Deninger boundary. -/
theorem sourceHorizontalGammaSixPhysicalStarPositive_iff_sourceUntwisting
    (q : XiZeroCopy) :
    SourceHorizontalGammaSixPhysicalStarPositive q ↔
      sourceHorizontalGammaSixPhysicalCovariantBoundary q =
        (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap := by
  rw [sourceHorizontalGammaSixPhysicalStarPositive_iff_line,
    sourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff]

/-- Positive-star source law literally untwists the physical covariant differential. -/
theorem sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_starPositive
    (q : XiZeroCopy) (hpos : SourceHorizontalGammaSixPhysicalStarPositive q) :
    sourceHorizontalGammaSixPhysicalCovariantBoundary q =
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap :=
  (sourceHorizontalGammaSixPhysicalStarPositive_iff_sourceUntwisting q).1 hpos

/-- After untwisting, the unconditional covariant producer becomes fixed-source Stokes flatness. -/
theorem sourceZeroGammaSixCyclicPhysicalCharacter_fixedStokesFlat_of_starPositive
    (q : XiZeroCopy) (hpos : SourceHorizontalGammaSixPhysicalStarPositive q) :
    (sourceHorizontalGammaSixCyclicCharacterReadout
        (sourceHorizontalGammaSixPhysicalCharacterParameter (q.1 : ℂ))).comp
      (deningerZBoundary sourceHorizontalGammaSixCyclicGroupEquiv ℝ).hom.toLinearMap = 0 := by
  rw [← sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_starPositive q hpos]
  exact sourceZeroGammaSixCyclicPhysicalCharacter_covariantStokesFlat q

/-- Sharp no-go: covariant Stokes flatness alone does not imply positive-star untwisting.  Grade
`a = 1` is an explicit nonneutral counterexample. -/
theorem exists_covariantStokesFlat_without_positiveStarUntwisting :
    ∃ a : ℝ,
      (sourceHorizontalGammaSixCyclicCharacterReadout a).comp
          (sourceHorizontalGammaSixHolonomyBoundary (Real.exp a)) = 0 ∧
        ¬ 0 ≤ sourceHorizontalGammaSixCyclicCharacterReadout a
          sourceHorizontalGammaSixCyclicHermitianSquare := by
  refine ⟨1, sourceHorizontalGammaSixCyclicCharacterReadout_covariantStokesFlat 1, ?_⟩
  rw [sourceHorizontalGammaSixCyclicCharacterReadout_hermitianSquare]
  exact not_le_of_gt (neg_lt_zero.mpr
    ((sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff 1).2 one_ne_zero))

/-! ## Prime- and multiplicity-faithful full producer -/

/-- Positive-star law on the actual full integral producer, retaining Xi multiplicity and prime
clock. -/
def DeningerXiFullIntegralGammaProducerStarPositive
    (rho : XiDivisorSupport) (p : Nat.Primes) : Prop :=
  0 ≤ (deningerXiFullIntegralGammaProducer rho p).evaluation
    (deningerIntegralGammaMultiplicityQuadraticGhost
      (xiSupportMultiplicity rho))

/-- Unconditionally, the full producer reads its source Hermitian square nonpositively. -/
theorem deningerXiFullIntegralGammaProducer_quadraticGhost_nonpos
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    (deningerXiFullIntegralGammaProducer rho p).evaluation
        (deningerIntegralGammaMultiplicityQuadraticGhost
          (xiSupportMultiplicity rho)) ≤ 0 := by
  let h := deningerXiFullIntegralGammaProducer rho p
  let a : ℝ := Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho
  rw [h.quadraticGhost_coefficient,
    show Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho = a from rfl]
  have hprod :
      sourceHorizontalGammaSixUnitForwardBoundaryDefect a *
          sourceHorizontalGammaSixUnitReflectedBoundaryDefect a =
        -sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a := by
    rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]
    ring
  rw [hprod]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
    (neg_nonpos.mpr
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg a))

/-- Requiring the same coefficient-faithful source square to be nonnegative forces its value to
zero and hence forces the selected Xi divisor onto the line. -/
theorem deningerXiFullIntegralGammaProducerStarPositive_iff_line
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerXiFullIntegralGammaProducerStarPositive rho p ↔
      (rho : ℂ).re = 1 / 2 := by
  let h := deningerXiFullIntegralGammaProducer rho p
  have hnonpos := deningerXiFullIntegralGammaProducer_quadraticGhost_nonpos rho p
  constructor
  · intro hpos
    change 0 ≤ h.evaluation
      (deningerIntegralGammaMultiplicityQuadraticGhost
        (xiSupportMultiplicity rho)) at hpos
    apply h.quadraticGhost_eq_zero_iff_line.mp
    exact le_antisymm hnonpos hpos
  · intro hline
    have hz := h.quadraticGhost_eq_zero_iff_line.mpr hline
    change 0 ≤ h.evaluation
      (deningerIntegralGammaMultiplicityQuadraticGhost
        (xiSupportMultiplicity rho))
    rw [hz]

/-- Positive-star evaluation and conormal ghost erasure are the same pointwise operation. -/
theorem deningerXiFullIntegralGammaProducerStarPositive_iff_descends
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    DeningerXiFullIntegralGammaProducerStarPositive rho p ↔
      DeningerXiFullIntegralGammaProducerDescends rho p := by
  rw [deningerXiFullIntegralGammaProducerStarPositive_iff_line,
    deningerXiFullIntegralGammaProducerDescends_iff_line]

/-- Global positive-star untwisting of every physical Gamma-six character is exactly RH. -/
theorem everySourceHorizontalGammaSixPhysicalStarPositive_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, SourceHorizontalGammaSixPhysicalStarPositive q) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    rw [← everySourceHorizontalGammaSixPhysicalCovariantBoundary_eq_fixed_iff_riemannHypothesis]
    intro q
    exact sourceHorizontalGammaSixPhysicalCovariantBoundary_untwist_of_starPositive q (h q)
  · intro hRH q
    exact (sourceHorizontalGammaSixPhysicalStarPositive_iff_line q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)

end

end RHTower
