import GaloisForLFunctions.BiScaleUncertainty.ExplicitApertureSplineInputs
import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthFunctor
import GaloisForLFunctions.ArithmeticOrientationTheory.AnIndexFormulaForTheActualReceiver
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.VanishingApertureFloorAndGradedTransport
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LambdaRingEffectivityAndHeckeLefschetzRigidity
import GaloisForLFunctions.ArithmeticIncidencePositivity.SharedDerivativeEnergyAndGlobalAllocationSynthesis
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalFirstVariation
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowPrimeTwoMargin

/-!
# Concrete applications of the width, energy, and incidence dictionaries

The boosted spline and its odd part supply every regularity premise. The
aperture chain 1/10, 1/5, 3/10 stays inside the certified ground-energy
window. The half-damped Möbius source has empty obstruction hull and index
zero. Riemann–Roch on the odd window pays the selected incidence source,
while the global graded allocation retains rate 1/2 and constant 75.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped BigOperators
open Zeta23 RHTower
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.HTGeometry (hermNegIndex)

namespace GaloisForLFunctions.ArithmeticOrientationTheory
noncomputable section

/-- The six arithmetic receivers admit the proved half-width threshold. -/
theorem canonicalReceivers_admitted_half :
    spectralZeroReceiver.admittedAt (1/2) ∧ abscissaReceiver.admittedAt (1/2) ∧
    moebiusDampingReceiver.admittedAt (1/2) ∧ liouvilleDampingReceiver.admittedAt (1/2) ∧
    xiHalfPlaneReceiver.admittedAt (1/2) ∧ suzukiFormationReceiver.admittedAt (1/2) := by
  have h (R : ReceiverObject) : R.admittedAt (1/2) :=
    (R.admittedAt_iff (by norm_num)).mpr (widthFunctor.obj R).2.2
  exact ⟨h _,h _,h _,h _,h _,h _⟩

/-- Applying the spline width dictionary gives the unconditional rate 3/2 prime envelope. -/
theorem exists_splinePrimeSum_halfWidth_bound :
    ∃ K : ℝ, ∀ τ : ℝ, 4 < τ →
      splinePrimeSum τ ≤ splinePolarMass τ+K*Real.exp (3/2*τ) := by
  have hXi : XiZeroHalfPlaneBound (1/2) := canonicalReceivers_admitted_half.2.2.2.2.1
  simpa only [show (1 : ℝ)+1/2 = 3/2 by norm_num] using
    (xiZeroHalfPlaneBound_iff_spline_prime_sum_le_of_gt_four
      (β := 1/2) (by norm_num)).mp hXi

/-- A specified radius-one-fifth real spline. -/
def fifthSpline : ℝ → ℝ := apertureSpline (1/5)

theorem fifthSpline_ne_zero : fifthSpline ≠ 0 := apertureSpline_ne_zero (by norm_num)

theorem fifthSpline_contDiff : ContDiff ℝ 2 fifthSpline := contDiff_apertureSpline _

theorem fifthSpline_compact : HasCompactSupport fifthSpline :=
  hasCompactSupport_apertureSpline (by norm_num)

theorem fifthSpline_support (x : ℝ) (hx : (1/5 : ℝ) < |x|) : fifthSpline x = 0 :=
  apertureSpline_eq_zero (by norm_num) hx

/-- The ground-energy aperture dictionary pays the specified full spline source. -/
theorem fifthSpline_fullZeroForm_nonneg : 0 ≤ fullZeroForm fifthSpline := by
  have hμ : 0 ≤ ccmRestrictedWeilGroundEnergy ⟨3/10, by norm_num⟩ :=
    le_trans (by norm_num) (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths le_rfl)
  exact zetaWindowPositive_of_ccmRestrictedWeilGroundEnergy_nonneg
    (A' := 1/5) (by norm_num) hμ
    fifthSpline fifthSpline_contDiff fifthSpline_compact fifthSpline_support

/-- Three explicit apertures, held fixed after the third. -/
def certifiedApertureChain (j : ℕ) : SuzukiPositiveAperture :=
  ⟨if j = 0 then 1/10 else if j = 1 then 1/5 else 3/10, by split_ifs <;> norm_num⟩

/-- Exact finite transport with a surviving 1/5000 margin at the final aperture. -/
theorem certifiedApertureChain_jump_budget :
    0 ≤ ∑ j ∈ Finset.range 2,
      apertureSpectralJump (certifiedApertureChain j) (certifiedApertureChain (j+1)) ∧
    (∑ j ∈ Finset.range 2,
      apertureSpectralJump (certifiedApertureChain j) (certifiedApertureChain (j+1))) ≤
      ccmRestrictedWeilGroundEnergy (certifiedApertureChain 0)-1/5000 := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    have hj2 : j < 2 := Finset.mem_range.mp hj
    apply apertureSpectralJump_nonneg
    interval_cases j <;> norm_num [certifiedApertureChain]
  · rw [sum_apertureSpectralJump_eq]
    have hfloor := one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths
      (A := certifiedApertureChain 2) (by norm_num [certifiedApertureChain])
    linarith only [hfloor]

/-- The same endpoint has compensated sampling constant -1/5000. -/
theorem certifiedApertureChain_compensated_floor :
    CompensatedSamplingBound (certifiedApertureChain 2) (-1/5000) :=
  compensatedSamplingBound_neg_one_div_5000_of_le_three_tenths _
    (by norm_num [certifiedApertureChain])

/-- The actual half-damped Möbius receiver has full repairing ideal, empty hull, and index zero. -/
theorem halfDampedMoebius_index_certificate :
    paidIdeal (pmPowerDampedRealWeight (1/2))
      (summable_abs_pmPowerDamped_div (by norm_num)) = ⊤ ∧
    obstructionHull (pmPowerDampedRealWeight (1/2))
      (summable_abs_pmPowerDamped_div (by norm_num)) = ∅ ∧
    Module.rank ℂ (WienerAlgebraAt (1/2) ⧸ paidIdeal (pmPowerDampedRealWeight (1/2))
      (summable_abs_pmPowerDamped_div (by norm_num))) = 0 ∧
    Module.finrank ℂ (WienerAlgebraAt (1/2) ⧸ paidIdeal (pmPowerDampedRealWeight (1/2))
      (summable_abs_pmPowerDamped_div (by norm_num))) = 0 := by
  exact ⟨(paidIdeal_eq_top_iff_receiverBounded _).mpr receiverBounded_pmPowerDamped_half,
    (obstructionHull_eq_empty_iff_receiverBounded _).mpr receiverBounded_pmPowerDamped_half,
    (rank_quotient_paidIdeal_eq_zero_iff_receiverBounded _).mpr receiverBounded_pmPowerDamped_half,
    finrank_quotient_paidIdeal_eq_zero_of_receiverBounded _ receiverBounded_pmPowerDamped_half⟩

/-- The positive prime-two polar margin yields the exact finite-degree heat window. -/
theorem primeTwoMargin_heatWindow_certificate :
    (1/20 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy primeTwoAperture ∧
    (∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ 1/32/n →
      hermNegIndex (heatMomentSection a (n+1)) ≤ 1) :=
  ⟨one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo,
    eventually_hermNegIndex_heatMomentSection_le_one_primeTwo⟩

/-- The concrete spline's first variation retains the complete Weil energy. -/
theorem fifthSpline_suzuki_firstVariation :
    Tendsto (fun omega : ℝ =>
      (autocorr fifthSpline 0-suzukiCriticalSourcePairing fifthSpline omega)/omega)
      (𝓝[>] 0) (𝓝 (fullZeroForm fifthSpline)) := by
  rw [ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional
    fifthSpline_contDiff.continuous fifthSpline_compact]
  exact tendsto_suzukiCriticalSourcePairing_firstVariation_of_contDiff
    fifthSpline_contDiff fifthSpline_compact

/-- Twice the odd part of the selected spline. -/
def oddFifthSpline (x : ℝ) : ℝ := fifthSpline x-fifthSpline (-x)

theorem oddFifthSpline_contDiff : ContDiff ℝ 2 oddFifthSpline :=
  fifthSpline_contDiff.sub (fifthSpline_contDiff.comp contDiff_id.neg)

theorem oddFifthSpline_odd (x : ℝ) : oddFifthSpline (-x) = -oddFifthSpline x := by
  simp only [oddFifthSpline, neg_neg]
  ring

theorem oddFifthSpline_support (x : ℝ) (hx : (1/5 : ℝ) < |x|) : oddFifthSpline x = 0 := by
  rw [oddFifthSpline, fifthSpline_support x hx,
    fifthSpline_support (-x) (by simpa only [abs_neg] using hx), sub_self]

theorem oddFifthSpline_compact : HasCompactSupport oddFifthSpline := by
  have hs : tsupport oddFifthSpline ⊆ Icc (-(1/5 : ℝ)) (1/5) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact abs_le.mp (le_of_not_gt (fun h => hx (oddFifthSpline_support x h)))
  exact IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure hs

/-- Riemann–Roch for the certified odd cone pays this exact prime–polar allocation. -/
theorem oddFifthSpline_riemannRoch_allocation :
    (scalingSubsurface (oddRealTestsAt (1/5))).RiemannRochAxiom
      (strictCoupledArithmeticCone (oddRealTestsAt (1/5))) ∧
    GlobalIncidenceAllocation (1/5) (1/4) oddFifthSpline := by
  have hRR := (strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths
    (r := 1/5) (by norm_num)).1
  refine ⟨hRR, ?_⟩
  have hH := (strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex
    (oddRealTestsAt (1/5))).mp hRR
  let f : oddRealTestsAt (1/5) := mkOddRealTestsAt oddFifthSpline
    oddFifthSpline_contDiff oddFifthSpline_compact oddFifthSpline_odd oddFifthSpline_support
  have hQ := (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg
    (oddRealTestsAt (1/5))).mp hH f
  change 0 ≤ weilPair oddFifthSpline oddFifthSpline at hQ
  rw [weilPair_self_eq_fullZeroForm oddFifthSpline_contDiff oddFifthSpline_compact] at hQ
  exact (globalIncidenceAllocation_iff_fullZeroForm_nonneg oddFifthSpline_contDiff
    oddFifthSpline_compact oddFifthSpline_odd (by norm_num) oddFifthSpline_support
    (by norm_num)).mpr hQ

/-- The explicit all-aperture (1/2,75) law specializes to the selected odd source. -/
theorem oddFifthSpline_graded_allocation :
    reflectedPrimePolarCost oddFifthSpline (1/5) ≤
      incidenceBudget (1/5) (1/4) oddFifthSpline+
        75*Real.exp (1/5)*∫ x, oddFifthSpline x^2 := by
  have h := gradedIncidenceAllocation_half_seventyFive
    (1/5) (1/4) oddFifthSpline (by norm_num) (by norm_num)
    oddFifthSpline_contDiff oddFifthSpline_compact oddFifthSpline_odd oddFifthSpline_support
  change _ ≤ _ at h
  unfold reflectedPrimePolarCost incidenceBudget
  norm_num only [show (2 : ℝ)*(1/2)*(1/5) = 1/5 by norm_num] at h
  linarith only [h]

/-- The spline as a pure test cycle on the scaling surface. -/
def fifthSplineCycle : ScalingCycle :=
  (0,0,⟨fifthSpline,fifthSpline_contDiff,fifthSpline_compact⟩)

/-- Scale four makes the Lefschetz–adjunction coefficients exactly 5/2, 1/2, and one. -/
theorem fifthSplineCycle_lefschetz_four :
    arithLefschetz fifthSplineCycle 4-5/2*scalingSurface.pair fifthSplineCycle fifthSplineCycle =
      1/2*scalingSurface.defect fifthSplineCycle fifthSplineCycle+
        scalingSurface.defect (adamsVar 4 fifthSplineCycle) (adamsVar 4 fifthSplineCycle) := by
  have h := arithLefschetz_eq_selfPair_add_defect_add_adamsVar fifthSplineCycle
    (a := 4) (by norm_num)
  norm_num at h
  exact h

end
end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.canonicalReceivers_admitted_half
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_splinePrimeSum_halfWidth_bound
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_ne_zero
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_contDiff
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_compact
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_support
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_fullZeroForm_nonneg
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.certifiedApertureChain
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.certifiedApertureChain_jump_budget
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.certifiedApertureChain_compensated_floor
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.halfDampedMoebius_index_certificate
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.primeTwoMargin_heatWindow_certificate
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSpline_suzuki_firstVariation
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_contDiff
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_odd
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_support
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_compact
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_riemannRoch_allocation
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.oddFifthSpline_graded_allocation
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSplineCycle
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.fifthSplineCycle_lefschetz_four
