import GaloisForLFunctions.RHTower.XiHurwitzAnchoredVandermondeOrientation
import GaloisForLFunctions.RHTower.XiHurwitzFESchwarzValueReflectionAperture
import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergyConsumers
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.XiHurwitzOrientationSeparatedSourceReconstruction
import GaloisForLFunctions.RHTower.XiHurwitzTropicalSoninLoop
import GaloisForLFunctions.RHTower.XiArakelovHurwitzDependenceCollision

/-!
# Xi--Hurwitz orientation universality

The terminal Xi--Hurwitz classifiers all carry one orientation datum.  This module packages the
maximal common closure across differential constraints, finite Hurwitz values, Hilbert and Hankel
positivity, continued prime--Gamma sources, sharp growth, and tropical Sonin memory.  It also
packages the complementary positive-energy witness chamber.
-/

open Complex Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- Simultaneous bounded-ray, all-power, dyadic, and arbitrary two-scale linearity of every
nondegenerate normalized rational-Hurwitz reflection energy. -/
def XiRationalHurwitzAllFiniteRefinements : Prop :=
  (∀ n : ℕ, 1 < n → XiRationalHurwitzPowerEnergyBounded n) ∧
  (∀ n : ℕ, 1 < n → ∀ k : ℕ, 1 < k →
    XiRationalHurwitzPowerLinearRefinement n k) ∧
  (∀ n : ℕ, 1 < n → XiRationalHurwitzDyadicLinearRefinement n) ∧
  (∀ m n : ℕ, 1 < m → m < n → XiRationalHurwitzTwoScaleEnergyEqual m n)

/-- Every nondegenerate finite rational-Hurwitz refinement chart carries exactly RH. -/
theorem xiRationalHurwitzAllFiniteRefinements_iff_riemannHypothesis :
    XiRationalHurwitzAllFiniteRefinements ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis 2
      (by norm_num)).mp (h.1 2 (by norm_num))
  · intro hRH
    exact ⟨
      fun n hn =>
        (xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis n hn).2 hRH,
      fun n hn k hk =>
        (xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis
          n hn k hk).2 hRH,
      fun n hn =>
        (xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis n hn).2 hRH,
      fun m n hm hmn =>
        (xiRationalHurwitzTwoScaleEnergyEqual_iff_riemannHypothesis hm hmn).2 hRH⟩

/-- Rectangular Weil norms are subpower at every positive width. -/
def XiHurwitzAllWidthRectangularNormSubpower : Prop :=
  ∀ L : ℝ, 0 < L →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → L ≤ Real.log n / 2 →
        ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
            C * (n : ℝ) ^ ε

/-- All-width rectangular subpower growth is still exactly RH. -/
theorem xiHurwitzAllWidthRectangularNormSubpower_iff_riemannHypothesis :
    XiHurwitzAllWidthRectangularNormSubpower ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (riemannHypothesis_iff_rectangular_weil_norm_subpower
      (L := 1) (by norm_num)).2 (h 1 (by norm_num))
  · intro hRH L hL
    exact (riemannHypothesis_iff_rectangular_weil_norm_subpower hL).1 hRH

/-- At every positive width there is an admissible rectangular tail with arbitrarily small
one-sided polynomial loss. -/
def XiHurwitzAllWidthRectangularTailSubpowerLower : Prop :=
  ∀ L : ℝ, 0 < L → ∃ N : ℕ, XiRectangularWeilTailSubpowerLower L N

/-- All-width one-sided rectangular tail control is exactly RH. -/
theorem xiHurwitzAllWidthRectangularTailSubpowerLower_iff_riemannHypothesis :
    XiHurwitzAllWidthRectangularTailSubpowerLower ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (riemannHypothesis_iff_exists_rectangularWeilTailSubpowerLower
      (L := 1) (by norm_num)).2 (h 1 (by norm_num))
  · intro hRH L hL
    exact (riemannHypothesis_iff_exists_rectangularWeilTailSubpowerLower hL).1 hRH

/-- The phase-coded closed Sonin loop is absorbed by its direct endpoint Gram at every positive
operator parameter. -/
def XiHurwitzAllScaleTropicalLoopAbsorption : Prop :=
  ∀ a : ℝ, 0 < a →
    xiHurwitzTropicalLoop.operator a =ₖ
      (soninGramFactorOfScales xiHurwitzTropicalLoop.start
        xiHurwitzTropicalLoop.endpoint xiHurwitzTropicalLoop.start_gt_one
        xiHurwitzTropicalLoop.endpoint_gt_one).operator a

/-- All-scale tropical Sonin absorption is exactly RH. -/
theorem xiHurwitzAllScaleTropicalLoopAbsorption_iff_riemannHypothesis :
    XiHurwitzAllScaleTropicalLoopAbsorption ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact (riemannHypothesis_iff_xiHurwitzTropicalLoop_compactEq_direct
      1 (by norm_num)).2 (h 1 (by norm_num))
  · intro hRH a ha
    exact (riemannHypothesis_iff_xiHurwitzTropicalLoop_compactEq_direct a ha).1 hRH

/-- One continued prime--Gamma Cauchy-core sequence converges to the orientation vector and its
energy while remaining eventually Weil-nonnegative. -/
def XiHurwitzContinuedCauchySequenceNonnegative : Prop :=
  ∃ V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2,
    (∀ n, V n ∈ xiWeilContinuedCauchyAlgebraicSubspace) ∧
    Tendsto V atTop (nhds xiHurwitzOrientationVector) ∧
    Tendsto (fun n => xiWeilHilbertQuadratic (V n)) atTop
      (nhds (-xiHurwitzOrientationEnergy)) ∧
    ∀ᶠ n in atTop, 0 ≤ xiWeilHilbertQuadratic (V n)

/-- The existence of one convergent eventually nonnegative continued-source sequence is exactly
RH; convergence to the negative orientation energy makes this independent of witness choice. -/
theorem xiHurwitzContinuedCauchySequenceNonnegative_iff_riemannHypothesis :
    XiHurwitzContinuedCauchySequenceNonnegative ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨V, _hmem, _hV, hQ, hnonneg⟩
    have hlimit : 0 ≤ -xiHurwitzOrientationEnergy := ge_of_tendsto hQ hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.2
    linarith [xiHurwitzOrientationEnergy_nonneg]
  · intro hRH
    obtain ⟨V, hmem, hV, hQ, hiff⟩ :=
      exists_continuedCauchyCore_sequence_eventually_nonnegative_iff_riemannHypothesis
    exact ⟨V, hmem, hV, hQ, hiff.1 hRH⟩

/-- One sequence of pairwise-separated finite continued prime--Gamma packets converges to the
orientation vector and energy while remaining eventually source-nonnegative. -/
def XiHurwitzSeparatedSourceSequenceNonnegative : Prop :=
  ∃ P : ℕ → XiSeparatedContinuedCauchyPacket,
    Tendsto (fun n => (P n).evaluation) atTop
      (nhds xiHurwitzOrientationVector) ∧
    Tendsto (fun n => (P n).sourceEnergy) atTop
      (nhds (-xiHurwitzOrientationEnergy)) ∧
    ∀ᶠ n in atTop, 0 ≤ (P n).sourceEnergy

/-- The existence of one convergent eventually nonnegative separated finite-source sequence is
exactly RH. -/
theorem xiHurwitzSeparatedSourceSequenceNonnegative_iff_riemannHypothesis :
    XiHurwitzSeparatedSourceSequenceNonnegative ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨P, _hP, hE, hnonneg⟩
    have hlimit : 0 ≤ -xiHurwitzOrientationEnergy := ge_of_tendsto hE hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.2
    linarith [xiHurwitzOrientationEnergy_nonneg]
  · intro hRH
    obtain ⟨P, hP, hE, hiff⟩ :=
      exists_separatedContinuedSource_sequence_eventually_nonnegative_iff_riemannHypothesis
    exact ⟨P, hP, hE, hiff.1 hRH⟩

/-- Every actual critical-line Xi anchor has both zero anchored orientation energy and real
two-node Hurwitz Vandermonde separators. -/
def XiHurwitzAllCriticalAnchorsRigid : Prop :=
  ∀ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2 →
    xiHurwitzAnchoredPairOrientationEnergy τ = 0 ∧
      XiHurwitzAnchoredPairVandermondeReal τ

/-- Simultaneous positive-chamber realization of the canonical Xi--Hurwitz orientation datum. -/
def XiHurwitzOrientationUniversalCertificate : Prop :=
  XiHurwitzNegativeCharacterChamber ∧
  (∀ ρ : XiDivisorSupport,
    xiHurwitzMonodromyCharacter ρ =
      -((Real.exp (2 * Real.pi * (ρ : ℂ).im) : ℝ) : ℂ)) ∧
  (∀ ρ : XiDivisorSupport,
    (xiCentralReciprocalSquare (ρ : ℂ)).im = 0) ∧
  xiHurwitzOrientationVector = 0 ∧
  0 ≤ xiWeilHilbertQuadratic xiHurwitzOrientationVector ∧
  XiCentralTraceHankelNonnegative ∧
  XiCentralMomentHankelDeterminantsPositive ∧
  (∀ F : ℂ → ℂ, XiWeilSquareSummable F →
    0 ≤ (xiWeilPolarization F F).re) ∧
  XiFirstPrimeSeamChargesVanish ∧
  XiHurwitzAnchorPrimeTwoSeamsVanish ∧
  XiHurwitzFESchwarzPairCircuit ∧
  XiHurwitzFESchwarzTripleCircuit ∧
  XiHurwitzAnchorJetProjectiveReflectionLaw ∧
  XiAllPositivePrimeSeamDamping ∧
  XiRationalHurwitzFiberTwoReflectionFixed ∧
  XiRationalHurwitzAllFiniteRefinements ∧
  xiHurwitzRightPrincipalPhaseSup = 0 ∧
  XiHurwitzAllWidthRectangularNormSubpower ∧
  XiHurwitzAllWidthRectangularTailSubpowerLower ∧
  XiHurwitzAllScaleTropicalLoopAbsorption ∧
  XiExteriorContinuedCauchySourcePassivity (218 / 25) ∧
  XiPositivePairedContinuedCauchyCorePassivity (218 / 25) ∧
  XiPositivePairedReducedSourcePassivity (218 / 25) ∧
  XiHurwitzContinuedCauchySequenceNonnegative ∧
  XiHurwitzSeparatedSourceSequenceNonnegative ∧
  XiHurwitzAllCriticalAnchorsRigid ∧
  XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter ∧
  XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace

/-- **Xi--Hurwitz orientation universality law.**  Vanishing of one trace-class scalar is
equivalent to simultaneous realization in twenty-eight differential, finite-value, Hilbert,
Hankel, source, growth, and tropical charts. -/
theorem xiHurwitzOrientationEnergy_eq_zero_iff_universalCertificate :
    xiHurwitzOrientationEnergy = 0 ↔
      XiHurwitzOrientationUniversalCertificate := by
  constructor
  · intro henergy
    have hRH : RiemannHypothesis :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.2 henergy
    refine ⟨
      riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.1 hRH,
      riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height.1 hRH,
      xiHurwitzOrientationEnergy_eq_zero_iff_centralSpectrum_real.1 henergy,
      xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.2 henergy,
      riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.1 hRH,
      xiHurwitzOrientationEnergy_eq_zero_iff_traceHankelNonnegative.1 henergy,
      xiHurwitzOrientationEnergy_eq_zero_iff_hankelDeterminantsPositive.1 henergy,
      riemannHypothesis_iff_xiWeilPolarization_nonneg.1 hRH,
      xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero.2 henergy,
      xiHurwitzAnchorPrimeTwoSeamsVanish_iff_orientationEnergy_zero.2 henergy,
      xiHurwitzFESchwarzPairCircuit_iff_orientationEnergy_zero.2 henergy,
      xiHurwitzFESchwarzTripleCircuit_iff_riemannHypothesis.2 hRH,
      xiHurwitzAnchorJetProjectiveReflectionLaw_iff_riemannHypothesis.2 hRH,
      xiAllPositivePrimeSeamDamping_iff_riemannHypothesis.2 hRH,
      xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis.2 hRH,
      xiRationalHurwitzAllFiniteRefinements_iff_riemannHypothesis.2 hRH,
      riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_eq_zero.1 hRH,
      xiHurwitzAllWidthRectangularNormSubpower_iff_riemannHypothesis.2 hRH,
      xiHurwitzAllWidthRectangularTailSubpowerLower_iff_riemannHypothesis.2 hRH,
      xiHurwitzAllScaleTropicalLoopAbsorption_iff_riemannHypothesis.2 hRH,
      exteriorContinuedCauchySourcePassivity_twoHundredEighteen_twentyFifths_iff_rh.2 hRH,
      positivePairedContinuedCauchyCorePassivity_twoHundredEighteen_twentyFifths_iff_rh.2 hRH,
      positivePairedReducedSourcePassivity_twoHundredEighteen_twentyFifths_iff_rh.2 hRH,
      xiHurwitzContinuedCauchySequenceNonnegative_iff_riemannHypothesis.2 hRH,
      xiHurwitzSeparatedSourceSequenceNonnegative_iff_riemannHypothesis.2 hRH,
      fun τ hτ => ⟨
        (riemannHypothesis_iff_xiHurwitzAnchoredPairOrientationEnergy_eq_zero
          τ hτ).1 hRH,
        (riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal
          τ hτ).1 hRH⟩,
      xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_iff_riemannHypothesis.2 hRH,
      xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_riemannHypothesis.2 hRH⟩
  · intro hcertificate
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.1
    exact riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.2 hcertificate.1

/-- The unconditional differential-independence factor remains present across the complete
orientation certificate, so this capstone subsumes both earlier constraint-orientation product
laws. -/
theorem xi_hurwitz_differential_orientation_universality_law :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
        (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero (ρ : ℂ)) ∧
      (xiHurwitzOrientationEnergy = 0 ↔
        XiHurwitzOrientationUniversalCertificate) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact ⟨xi_hurwitz_scalar_constraint_orientation_product_law.1,
    xiHurwitzOrientationEnergy_eq_zero_iff_universalCertificate⟩

/-- Simultaneous negative-chamber witnesses forced by positive Xi--Hurwitz orientation energy. -/
def XiHurwitzOrientationFailureUniversalCertificate : Prop :=
  (∃ ρ : XiDivisorSupport, (ρ : ℂ).re ≠ 1 / 2) ∧
  (∃ p : Polynomial ℝ, (xiCentralTraceHankel p).re < 0) ∧
  (∃ n : ℕ, (xiCentralMomentHankelMatrix n).det ≤ 0) ∧
  (∃ F : ℂ → ℂ, XiWeilSquareSummable F ∧
    (xiWeilPolarization F F).re < 0) ∧
  xiWeilHilbertQuadratic xiHurwitzOrientationVector < 0 ∧
  0 < xiHurwitzRightPrincipalPhaseSup

/-- **Complementary Xi--Hurwitz failure universality law.**  Positive scalar energy is equivalent
to simultaneous off-line, trace-Hankel, determinant, Weil, canonical-vector, and sharp-phase
witnesses. -/
theorem xiHurwitzOrientationEnergy_pos_iff_failureUniversalCertificate :
    0 < xiHurwitzOrientationEnergy ↔
      XiHurwitzOrientationFailureUniversalCertificate := by
  constructor
  · intro henergy
    have hnotRH : ¬RiemannHypothesis :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.1 henergy
    exact ⟨
      xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero.1 henergy,
      xiHurwitzOrientationEnergy_pos_iff_exists_traceHankel_negative.1 henergy,
      xiHurwitzOrientationEnergy_pos_iff_exists_hankelDet_nonpos.1 henergy,
      xiHurwitzOrientationEnergy_pos_iff_exists_weil_negativeSquare.1 henergy,
      not_riemannHypothesis_iff_xiHurwitzOrientationVector_weil_neg.1 hnotRH,
      not_riemannHypothesis_iff_xiHurwitzRightPrincipalPhaseSup_pos.1 hnotRH⟩
  · intro hcertificate
    exact xiHurwitzOrientationEnergy_pos_iff_exists_offCriticalZero.2 hcertificate.1

end

end RHTower
