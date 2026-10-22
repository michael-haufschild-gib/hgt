import GaloisForLFunctions.RHTower.Suzuki.SuzukiCheckpointCurvatureSlopeCesaroWeld
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCoupling

/-!
# Checkpoint curvature as a Route-RG Chebyshev mass-error high-pass

This module identifies two source constructions that previously met only downstream.  The
checkpoint reservoir derivative is exactly the pointwise Route-RG archimedean slope: its Lerch
tail derivative is negative one quarter of the positive Lerch-gap slope, term by term.  The
checkpoint Mangoldt mass is exactly Route-RG's Abel weighted mass at every integer endpoint.
Consequently the floor-selected affine slope is the explicit bounded archimedean lower-order
slope minus the weighted Chebyshev mass error.

Discrete summation by parts transports this equality to the coefficient-faithful curvature first
moment.  Its normalized current is negative Route-RG mass-error Cesaro high-pass up to an explicit
archimedean high-pass bounded by twice the already-proved first-tail constant.  The same coordinate
then descends through completed Abel, prime--polar--Gamma energy, and the multiplicity- and
orientation-faithful Xi short.  No order assumption or RH-equivalent hypothesis is introduced.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

theorem screwLerchTail₁_eq_neg_quarter_suzukiPointwiseLerchGapSlope
    (t : ℝ) :
    screwLerchTail₁ t =
      -(1 / 4 : ℝ) * RiemannGaussian.suzukiPointwiseLerchGapSlope t := by
  rw [screwLerchTail₁, RiemannGaussian.suzukiPointwiseLerchGapSlope,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold RiemannGaussian.suzukiPointwiseLerchGapSlopeSummand
  rw [show lerchExp n = 2 * ((n : ℝ) + 1 / 4) by
    unfold lerchExp
    ring]
  have hn : ((n : ℝ) + 1 / 4) ≠ 0 := by positivity
  field_simp [hn]
  ring_nf

theorem suzukiCheckpointReservoirDeriv_eq_pointwiseArchimedeanSlope
    (t : ℝ) :
    suzukiCheckpointReservoirDeriv t =
      RiemannGaussian.suzukiPointwiseArchimedeanSlope t := by
  unfold suzukiCheckpointReservoirDeriv
    RiemannGaussian.suzukiPointwiseArchimedeanSlope screwLinearCoeff
  rw [screwLerchTail₁_eq_neg_quarter_suzukiPointwiseLerchGapSlope]
  ring_nf

theorem suzukiCheckpointMass_eq_chebyshevWeightedMass
    {N : ℕ} (hN : 1 ≤ N) :
    suzukiCheckpointMass N =
      RiemannGaussian.suzukiChebyshevWeightedMass (N : ℝ) := by
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel hN
  calc
    suzukiCheckpointMass N =
        ∑ n ∈ Finset.Ioc 1 N,
          RiemannGaussian.suzukiChebyshevMassKernel n *
            ArithmeticFunction.vonMangoldt n := by
      unfold suzukiCheckpointMass
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      intro n hn
      unfold screwPrimeWeight
      rw [RiemannGaussian.suzukiChebyshevMassKernel_nat_eq]
      ring_nf
    _ = RiemannGaussian.screwPrefixMass
          RiemannGaussian.suzukiPrimeWeight (N - 1) := by
      simpa [hsub] using
        (RiemannGaussian.screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum
          (N - 1)).symm
    _ = RiemannGaussian.suzukiChebyshevWeightedMass (N : ℝ) := by
      simpa [hsub] using
        RiemannGaussian.screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass
          (N - 1)

theorem suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointAffineSlope N =
      RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
          (Real.log (N : ℝ)) -
        RiemannGaussian.suzukiChebyshevWeightedMassError (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have harch :=
    RiemannGaussian.suzukiPointwiseArchimedeanSlope_sub_continuousMass_eq
      (Real.log (N : ℝ)) hNpos
  have harch' :
      RiemannGaussian.suzukiPointwiseArchimedeanSlope (Real.log (N : ℝ)) -
          RiemannGaussian.suzukiChebyshevContinuousMass (N : ℝ) =
        RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
          (Real.log (N : ℝ)) := by
    simpa using harch
  rw [suzukiCheckpointAffineSlope,
    suzukiCheckpointReservoirDeriv_eq_pointwiseArchimedeanSlope,
    suzukiCheckpointMass_eq_chebyshevWeightedMass (by omega)]
  unfold RiemannGaussian.suzukiChebyshevWeightedMassError
  linarith

/-- Terminal Route-RG mass error minus its checkpoint Cesaro history. -/
def suzukiChebyshevMassErrorCesaroDefect (N : ℕ) : ℝ :=
  RiemannGaussian.suzukiChebyshevWeightedMassError ((N + 1 : ℕ) : ℝ) -
    (3 * RiemannGaussian.suzukiChebyshevWeightedMassError 2 +
      ∑ j ∈ Finset.Ico 3 (N + 1),
        RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) /
      (N + 1 : ℕ)

/-- Terminal explicit archimedean lower-order slope minus its checkpoint Cesaro history. -/
def suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect (N : ℕ) : ℝ :=
  RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
      (Real.log ((N + 1 : ℕ) : ℝ)) -
    (3 * RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder (Real.log 2) +
      ∑ j ∈ Finset.Ico 3 (N + 1),
        RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
          (Real.log (j : ℝ))) /
      (N + 1 : ℕ)

theorem suzukiCheckpointAffineSlopeCesaroDefect_eq_arch_sub_massError
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointAffineSlopeCesaroDefect N =
      suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect N -
        suzukiChebyshevMassErrorCesaroDefect N := by
  have hterminal :=
    suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError
      (N := N + 1) (by omega)
  have htwo :=
    suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError
      (N := 2) (by omega)
  have hsum :
      (∑ j ∈ Finset.Ico 3 (N + 1), suzukiCheckpointAffineSlope j) =
        ∑ j ∈ Finset.Ico 3 (N + 1),
          (RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder
              (Real.log (j : ℝ)) -
            RiemannGaussian.suzukiChebyshevWeightedMassError (j : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [suzukiCheckpointAffineSlope_eq_lowerOrder_sub_massError]
    simp only [Finset.mem_Ico] at hj
    omega
  unfold suzukiCheckpointAffineSlopeCesaroDefect
    suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect
    suzukiChebyshevMassErrorCesaroDefect
  rw [hterminal, htwo, hsum]
  rw [Finset.sum_sub_distrib]
  ring_nf

/-- Uniform first-tail bound from the pointwise Route-RG source theorem. -/
def suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound : ℝ :=
  2 +
    |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
    1 / 4 * RiemannGaussian.suzukiPointwiseLerchGapSlope (Real.log 2)

theorem suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound_nonnegative :
    0 ≤ suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound := by
  have h := RiemannGaussian.abs_suzukiChebyshevArchimedeanSlopeLowerOrder_le
    (center := Real.log 2) le_rfl
  exact (abs_nonneg _).trans h

theorem abs_suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect_le
    {N : ℕ} (hN : 2 ≤ N) :
    |suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect N| ≤
      2 * suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound := by
  let C := suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound
  let f : ℕ → ℝ := fun j =>
    RiemannGaussian.suzukiChebyshevArchimedeanSlopeLowerOrder (Real.log (j : ℝ))
  have hC : 0 ≤ C := by
    exact suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound_nonnegative
  have hf (j : ℕ) (hj : 2 ≤ j) : |f j| ≤ C := by
    dsimp only [f, C, suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound]
    apply RiemannGaussian.abs_suzukiChebyshevArchimedeanSlopeLowerOrder_le
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    exact (Real.log_le_log_iff (by norm_num) hjpos).mpr (by exact_mod_cast hj)
  have hhistory :
      |3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j| ≤ (N + 1 : ℕ) * C := by
    calc
      |3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j| ≤
          |3 * f 2| + |∑ j ∈ Finset.Ico 3 (N + 1), f j| := abs_add_le _ _
      _ ≤ 3 * C + ∑ j ∈ Finset.Ico 3 (N + 1), |f j| := by
        apply add_le_add
        · rw [abs_mul]
          norm_num
          nlinarith [hf 2 (by omega)]
        · exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 3 * C + ∑ _j ∈ Finset.Ico 3 (N + 1), C := by
        gcongr with j hj
        apply hf j
        simp only [Finset.mem_Ico] at hj
        omega
      _ = (N + 1 : ℕ) * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [Nat.card_Ico]
        rw [Nat.cast_sub (by omega : 3 ≤ N + 1)]
        push_cast
        ring_nf
  have haverage :
      |(3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ)| ≤ C := by
    have hden : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    rw [abs_div, abs_of_pos hden]
    calc
      |3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j| / (N + 1 : ℕ) ≤
          ((N + 1 : ℕ) * C) / (N + 1 : ℕ) :=
        div_le_div_of_nonneg_right hhistory hden.le
      _ = C := by field_simp
  change |f (N + 1) -
      (3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ)| ≤ 2 * C
  calc
    |f (N + 1) -
        (3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ)| ≤
        |f (N + 1)| +
          |(3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ)| :=
      by
        rw [sub_eq_add_neg]
        calc
          |f (N + 1) +
              -((3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ))| ≤
              |f (N + 1)| +
                |-((3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ))| :=
            abs_add_le _ _
          _ = |f (N + 1)| +
                |(3 * f 2 + ∑ j ∈ Finset.Ico 3 (N + 1), f j) / (N + 1 : ℕ)| := by
            rw [abs_neg]
    _ ≤ C + C := add_le_add (hf (N + 1) (by omega)) haverage
    _ = 2 * C := by ring

/-- The coefficient-faithful curvature current differs from the negative RG mass-error
high-pass by a uniformly bounded, fully explicit archimedean term. -/
theorem abs_suzukiCheckpointCurvature_div_add_massErrorCesaroDefect_le
    {N : ℕ} (hN : 2 ≤ N) :
    |suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) +
        suzukiChebyshevMassErrorCesaroDefect N| ≤
      2 * suzukiChebyshevArchimedeanSlopeLowerOrderUniformBound := by
  rw [suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_affineSlopeCesaroDefect hN,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_arch_sub_massError hN]
  simpa only [sub_add_cancel] using
    abs_suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect_le hN

/-- Completed transition source in Route-RG mass-error coordinates. -/
def suzukiTransitionCoreChebyshevMassErrorCesaroSource (N : ℕ) : ℝ :=
  suzukiChebyshevArchimedeanSlopeLowerOrderCesaroDefect N -
    suzukiChebyshevMassErrorCesaroDefect N +
    ((Real.sqrt 2 - 1) * psiRemainder 1 +
      (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 -
      Real.sqrt 3 * psiRemainder 2 +
      (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
        (Real.log ((N + 1 : ℕ) : ℝ)) -
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
      coherentSquareRootPolarLatticeDefect (N + 1)) / (N + 1 : ℕ) -
    unitRieszSuzukiPolarCorrection (Real.log ((N + 1 : ℕ) : ℝ)) +
    unitRieszSuzukiArchCorrection (Real.log ((N + 1 : ℕ) : ℝ))

theorem suzukiTransitionCoreAffineSlopeCesaroSource_eq_massErrorCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreAffineSlopeCesaroSource N =
      suzukiTransitionCoreChebyshevMassErrorCesaroSource N := by
  rw [suzukiTransitionCoreAffineSlopeCesaroSource,
    suzukiTransitionCoreChebyshevMassErrorCesaroSource,
    suzukiCheckpointAffineSlopeCesaroDefect_eq_arch_sub_massError hN]

theorem suzukiTransitionCorePrimePolarGammaCurvatureSource_eq_massErrorCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCorePrimePolarGammaCurvatureSource N =
      suzukiTransitionCoreChebyshevMassErrorCesaroSource N := by
  rw [suzukiTransitionCorePrimePolarGammaCurvatureSource_eq_affineSlopeCesaro hN,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_massErrorCesaro hN]

theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_massErrorCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      suzukiTransitionCoreChebyshevMassErrorCesaroSource N := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_affineSlopeCesaro hN,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_massErrorCesaro hN]

theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_massErrorCesaro
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
        (suzukiTransitionCoreChebyshevMassErrorCesaroSource N /
          unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ (2 : ℕ) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_affineSlopeCesaro hN hcharge,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_massErrorCesaro hN]

theorem suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_massErrorCesaro
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy (N + 1) rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
          (suzukiTransitionCoreChebyshevMassErrorCesaroSource N /
            unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ (2 : ℕ) *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_affineSlopeCesaro
      hN hcharge,
    suzukiTransitionCoreAffineSlopeCesaroSource_eq_massErrorCesaro hN]

end

end GaloisForLFunctions.RHTower
