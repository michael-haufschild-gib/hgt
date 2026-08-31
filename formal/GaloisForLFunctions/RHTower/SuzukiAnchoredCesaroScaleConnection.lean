import GaloisForLFunctions.HTGeometry.AnchoredCesaroScaleConnection
import GaloisForLFunctions.RHTower.SuzukiCheckpointChebyshevMassErrorWeld

/-!
# Anchored Cesàro scale connection across the Suzuki route organs

The generic anchored Cesàro current is instantiated on the literal floor-selected Suzuki affine
slope.  Its scale acceleration is exactly the coefficient-faithful prime--polar--Gamma curvature
prefix.  The Route-RG archimedean-minus-mass-error split is an exact conservation law for the
formation potential, while completed Abel, aligned Gamma energy, and the multiplicity- and
orientation-faithful Xi short are exact readouts of the same scale current plus the retained
terminal correction.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Formation potential of the literal floor-selected affine checkpoint slope. -/
def suzukiCheckpointAffineSlopeCesaroPotential (N : ℕ) : ℝ :=
  anchoredCesaroPotential suzukiCheckpointAffineSlope N

/-- Formation potential of the Route-RG weighted Chebyshev mass error. -/
def suzukiChebyshevMassErrorCesaroPotential (N : ℕ) : ℝ :=
  anchoredCesaroPotential
    (fun j => RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) N

/-- Formation potential of the explicit Route-RG archimedean lower-order slope. -/
def suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential (N : ℕ) : ℝ :=
  anchoredCesaroPotential
    (fun j => RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
      (Real.log (j : ℝ))) N

/-- The previously isolated affine-slope Cesàro defect is literally the generic scale
connection. -/
theorem suzukiCheckpointAffineSlopeCesaroDefect_eq_highPass (N : ℕ) :
    suzukiCheckpointAffineSlopeCesaroDefect N =
      anchoredCesaroHighPass suzukiCheckpointAffineSlope N := by
  rfl

/-- The Route-RG mass-error defect is its generic scale connection. -/
theorem suzukiChebyshevMassErrorCesaroDefect_eq_highPass (N : ℕ) :
    suzukiChebyshevMassErrorCesaroDefect N =
      anchoredCesaroHighPass
        (fun j => RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) N := by
  rfl

/-- The explicit archimedean defect is its generic scale connection. -/
theorem suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect_eq_highPass (N : ℕ) :
    suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect N =
      anchoredCesaroHighPass
        (fun j => RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
          (Real.log (j : ℝ))) N := by
  rfl

/-- The normalized coefficient-faithful curvature current is the scale-weighted successor
increment of the affine formation potential. -/
theorem suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_scaleConnection
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) =
      (N + 2 : ℕ) *
        (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
          suzukiCheckpointAffineSlopeCesaroPotential N) := by
  rw [suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_affineSlopeCesaroDefect hN,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_highPass,
    anchoredCesaroHighPass_eq_scaled_potentialIncrement _ hN]
  rfl

/-- The unnormalized prime--polar--Gamma curvature prefix is exact scale acceleration. -/
theorem suzukiCheckpointWeightedSignedCurvaturePrefix_eq_scaleAcceleration
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N =
      (N + 1 : ℕ) * (N + 2 : ℕ) *
        (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
          suzukiCheckpointAffineSlopeCesaroPotential N) := by
  have hconn :=
    suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_scaleConnection hN
  have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hne] at hconn
  push_cast at hconn ⊢
  nlinarith

/-- Pointwise Route-RG splitting integrates to exact conservation of formation potential. -/
theorem suzukiCheckpointAffineSlopeCesaroPotential_eq_arch_sub_massError
    (N : ℕ) :
    suzukiCheckpointAffineSlopeCesaroPotential N =
      suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential N -
        suzukiChebyshevMassErrorCesaroPotential N := by
  have htwo := suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError
    (N := 2) (by omega)
  have hsum :
      (∑ j ∈ Finset.Ico 3 (N + 1), suzukiCheckpointAffineSlope j) =
        ∑ j ∈ Finset.Ico 3 (N + 1),
          (RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
              (Real.log (j : ℝ)) -
            RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError
    have hj3 := (Finset.mem_Ico.mp hj).1
    omega
  unfold suzukiCheckpointAffineSlopeCesaroPotential
    suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential
    suzukiChebyshevMassErrorCesaroPotential anchoredCesaroPotential
  rw [htwo, hsum, Finset.sum_sub_distrib]
  ring

/-- Route-RG conservation at connection level: affine current is archimedean current minus mass
error current. -/
theorem suzukiCheckpointScaleConnection_eq_arch_sub_massError
    (N : ℕ) :
    (N + 2 : ℕ) *
        (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
          suzukiCheckpointAffineSlopeCesaroPotential N) =
      (N + 2 : ℕ) *
          (suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential (N + 1) -
            suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential N) -
        (N + 2 : ℕ) *
          (suzukiChebyshevMassErrorCesaroPotential (N + 1) -
            suzukiChebyshevMassErrorCesaroPotential N) := by
  rw [suzukiCheckpointAffineSlopeCesaroPotential_eq_arch_sub_massError N,
    suzukiCheckpointAffineSlopeCesaroPotential_eq_arch_sub_massError (N + 1)]
  ring

/-- Every completed terminal term outside the affine high-pass, retained exactly. -/
def suzukiTransitionCoreCesaroTerminalCorrection (N : ℕ) : ℝ :=
  ((Real.sqrt 2 - 1) * psiRemainder 1 +
      (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 -
      Real.sqrt 3 * psiRemainder 2 +
      (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
        (Real.log ((N + 1 : ℕ) : ℝ)) -
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
      coherentSquareRootPolarLatticeDefect (N + 1)) / (N + 1 : ℕ) -
    unitRieszSuzukiPolarCorrection (Real.log ((N + 1 : ℕ) : ℝ)) +
    unitRieszSuzukiArchCorrection (Real.log ((N + 1 : ℕ) : ℝ))

/-- The affine source is exactly scale connection plus its explicit terminal correction. -/
theorem suzukiTransitionCoreAffineSlopeCesaroSource_eq_scaleConnection
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreAffineSlopeCesaroSource N =
      (N + 2 : ℕ) *
          (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
            suzukiCheckpointAffineSlopeCesaroPotential N) +
        suzukiTransitionCoreCesaroTerminalCorrection N := by
  rw [suzukiTransitionCoreAffineSlopeCesaroSource,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_highPass,
    anchoredCesaroHighPass_eq_scaled_potentialIncrement _ hN]
  unfold suzukiCheckpointAffineSlopeCesaroPotential
    suzukiTransitionCoreCesaroTerminalCorrection
  ring

/-- Fourth-organ prediction: the completed Abel source is the same scale connection plus the
retained terminal correction. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_scaleConnection
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      (N + 2 : ℕ) *
          (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
            suzukiCheckpointAffineSlopeCesaroPotential N) +
        suzukiTransitionCoreCesaroTerminalCorrection N := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_affineSlopeCesaro hN,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_scaleConnection hN]

/-- Completed Abel in the exact Route-RG potential split. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_rgScaleConnection
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      (N + 2 : ℕ) *
          (suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential (N + 1) -
            suzukiChebyshevArchimedeanSlopeLowerOrderCesaroPotential N) -
        (N + 2 : ℕ) *
          (suzukiChebyshevMassErrorCesaroPotential (N + 1) -
            suzukiChebyshevMassErrorCesaroPotential N) +
        suzukiTransitionCoreCesaroTerminalCorrection N := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_scaleConnection hN,
    suzukiCheckpointScaleConnection_eq_arch_sub_massError N]

/-- Fifth-organ prediction: aligned Gamma energy is the square of scale connection plus the exact
terminal correction. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_scaleConnection
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
        (((N + 2 : ℕ) *
            (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
              suzukiCheckpointAffineSlopeCesaroPotential N) +
            suzukiTransitionCoreCesaroTerminalCorrection N) /
          unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ 2 := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_affineSlopeCesaro
      hN hcharge,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_scaleConnection hN]

/-- The multiplicity- and orientation-faithful Xi short reads the same scale connection. -/
theorem suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_scaleConnection
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy (N + 1) rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
          ((((N + 2 : ℕ) *
              (suzukiCheckpointAffineSlopeCesaroPotential (N + 1) -
                suzukiCheckpointAffineSlopeCesaroPotential N) +
              suzukiTransitionCoreCesaroTerminalCorrection N) /
            unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ 2) *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_affineSlopeCesaro
      hN hcharge,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_scaleConnection hN]

/-- Divisor-free corrected formation action at the natural aperture. -/
def suzukiCorrectedScaleConnectionAction (N : ℕ) : ℝ :=
  suzukiNaturalApertureTransitionCoreCauchyEnergy N *
    (((N + 1 : ℕ) *
          (suzukiCheckpointAffineSlopeCesaroPotential N -
            suzukiCheckpointAffineSlopeCesaroPotential (N - 1)) +
        suzukiTransitionCoreCesaroTerminalCorrection (N - 1)) /
      unitRieszCoherentPrimeOutgoingCharge N) ^ 2

/-- The divisor-free corrected formation action and aligned Gamma energy are eventually the same
quantity. -/
theorem eventually_suzukiCorrectedScaleConnectionAction_eq_alignedGammaCompletedEnergy :
    suzukiCorrectedScaleConnectionAction =ᶠ[atTop]
      suzukiTransitionCoreAlignedGammaCompletedEnergy := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero] with N hN hcharge
  have hK : 2 ≤ N - 1 := by omega
  have hchargeK : unitRieszCoherentPrimeOutgoingCharge (N - 1 + 1) ≠ 0 := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hcharge
  have henergy :=
    suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_scaleConnection
      hK hchargeK
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at henergy
  have hidx : N - 1 + 2 = N + 1 := by omega
  rw [hidx] at henergy
  rw [suzukiCorrectedScaleConnectionAction]
  exact henergy.symm

/-- Eventual boundedness of the corrected source formation action. -/
def SuzukiCorrectedScaleConnectionActionEventuallyBounded : Prop :=
  ∃ B : ℝ, ∀ᶠ N : ℕ in atTop, suzukiCorrectedScaleConnectionAction N ≤ B

/-- Source-action boundedness is exactly aligned-energy boundedness. -/
theorem suzukiCorrectedScaleConnectionActionEventuallyBounded_iff_alignedGamma :
    SuzukiCorrectedScaleConnectionActionEventuallyBounded ↔
      SuzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB,
      eventually_suzukiCorrectedScaleConnectionAction_eq_alignedGammaCompletedEnergy]
      with N hbound heq
    rwa [← heq]
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB,
      eventually_suzukiCorrectedScaleConnectionAction_eq_alignedGammaCompletedEnergy]
      with N hbound heq
    rwa [heq]

/-- Exact RH selection coordinate in divisor-free formation-connection variables. -/
theorem riemannHypothesis_iff_suzukiCorrectedScaleConnectionActionEventuallyBounded :
    RiemannHypothesis ↔ SuzukiCorrectedScaleConnectionActionEventuallyBounded :=
  riemannHypothesis_iff_suzukiTransitionCoreAlignedGammaCompletedEnergyEventuallyBounded.trans
    suzukiCorrectedScaleConnectionActionEventuallyBounded_iff_alignedGamma.symm

/-- Bounded affine formation potential forbids an eventual positive curvature high-pass separated
from zero. -/
theorem not_eventually_suzukiCheckpointAffineSlopeCesaroDefect_ge_of_potential_bounded
    {B c : ℝ} (hc : 0 < c)
    (hpot : ∀ N, |suzukiCheckpointAffineSlopeCesaroPotential N| ≤ B) :
    ¬ ∀ᶠ N in atTop, c ≤ suzukiCheckpointAffineSlopeCesaroDefect N := by
  simpa only [suzukiCheckpointAffineSlopeCesaroPotential,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_highPass] using
    (not_eventually_anchoredCesaroHighPass_ge_of_potential_bounded
      suzukiCheckpointAffineSlope hc hpot)

/-- Bounded affine formation potential also forbids an eventual negative curvature high-pass
separated from zero. -/
theorem not_eventually_suzukiCheckpointAffineSlopeCesaroDefect_le_neg_of_potential_bounded
    {B c : ℝ} (hc : 0 < c)
    (hpot : ∀ N, |suzukiCheckpointAffineSlopeCesaroPotential N| ≤ B) :
    ¬ ∀ᶠ N in atTop, suzukiCheckpointAffineSlopeCesaroDefect N ≤ -c := by
  simpa only [suzukiCheckpointAffineSlopeCesaroPotential,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_highPass] using
    (not_eventually_anchoredCesaroHighPass_le_neg_of_potential_bounded
      suzukiCheckpointAffineSlope hc hpot)

end

end GaloisForLFunctions.RHTower
