import GaloisForLFunctions.RHTower.SuzukiTransitionCoreCheckpointCurvatureWeld

/-!
# Affine-slope Cesàro form of the completed Suzuki source

The signed Suzuki curvature cell is the jump of the floor-selected affine checkpoint slope.
Discrete summation by parts therefore turns its event-label first moment into one terminal slope
minus the Cesàro history of all preceding slopes.  Combining this identity with the exact
prime--polar--Gamma checkpoint weld gives a single pre-divisor source coordinate shared by the
CCM-FU affine current, completed Abel action, growing-rank Gamma transition energy, and the
multiplicity- and orientation-faithful Xi short.

No positivity or boundedness is asserted.  The arithmetic order problem is sharpened to control
of this literal affine-slope high-pass together with the displayed completed terminal corrections.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Adding one aperture cell adds its event-label-weighted signed curvature and nothing else. -/
theorem suzukiCheckpointWeightedSignedCurvaturePrefix_succ
    {N : ℕ} (hN : 1 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix (N + 1) =
      suzukiCheckpointWeightedSignedCurvaturePrefix N +
        (N + 2 : ℕ) * suzukiCheckpointSignedCurvatureCell (N + 1) := by
  rw [suzukiCheckpointWeightedSignedCurvaturePrefix,
    suzukiCheckpointWeightedSignedCurvaturePrefix,
    show N + 1 + 2 = (N + 2) + 1 by omega,
    Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 2)]
  rw [show N + 2 - 1 = N + 1 by omega]

/-- Discrete integration by parts for the coefficient-faithful curvature first moment. -/
theorem suzukiCheckpointWeightedSignedCurvaturePrefix_eq_terminalSlope_sub_cesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N =
      (N + 1 : ℕ) * suzukiCheckpointAffineSlope (N + 1) -
        3 * suzukiCheckpointAffineSlope 2 -
        ∑ j ∈ Finset.Ico 3 (N + 1), suzukiCheckpointAffineSlope j := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [suzukiCheckpointWeightedSignedCurvaturePrefix]
      norm_num
      rw [← suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell
        (by norm_num : 2 ≤ 2)]
      ring
  | succ N hN ih =>
      rw [suzukiCheckpointWeightedSignedCurvaturePrefix_succ (by omega : 1 ≤ N), ih]
      rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 1)]
      rw [← suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell
        (by omega : 2 ≤ N + 1)]
      push_cast at ih ⊢
      linarith

/-- Terminal affine slope minus its discrete Cesàro history. -/
def suzukiCheckpointAffineSlopeCesaroDefect (N : ℕ) : ℝ :=
  suzukiCheckpointAffineSlope (N + 1) -
    (3 * suzukiCheckpointAffineSlope 2 +
      ∑ j ∈ Finset.Ico 3 (N + 1), suzukiCheckpointAffineSlope j) /
        (N + 1 : ℕ)

/-- The normalized prime--polar--Gamma curvature first moment is exactly the affine-slope
high-pass. -/
theorem suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_affineSlopeCesaroDefect
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointWeightedSignedCurvaturePrefix N / (N + 1 : ℕ) =
      suzukiCheckpointAffineSlopeCesaroDefect N := by
  rw [suzukiCheckpointAffineSlopeCesaroDefect,
    suzukiCheckpointWeightedSignedCurvaturePrefix_eq_terminalSlope_sub_cesaro hN]
  have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hne]
  ring

/-- Completed source written as one affine-slope high-pass plus explicit terminal corrections. -/
def suzukiTransitionCoreAffineSlopeCesaroSource (N : ℕ) : ℝ :=
  suzukiCheckpointAffineSlopeCesaroDefect N +
    ((Real.sqrt 2 - 1) * psiRemainder 1 +
      (Real.sqrt 3 - Real.sqrt 2) * psiRemainder 2 -
      Real.sqrt 3 * psiRemainder 2 +
      (N + 1 : ℕ) * criticalMellinNormalizedChebyshevError
        (Real.log ((N + 1 : ℕ) : ℝ)) -
      suzukiCheckpointWeightedSelbergArchRemainderPrefix N +
      coherentSquareRootPolarLatticeDefect (N + 1)) / (N + 1 : ℕ) -
    unitRieszSuzukiPolarCorrection (Real.log ((N + 1 : ℕ) : ℝ)) +
    unitRieszSuzukiArchCorrection (Real.log ((N + 1 : ℕ) : ℝ))

/-- The completed checkpoint source is exactly the affine-slope high-pass source. -/
theorem suzukiTransitionCoreCheckpointCurvatureSource_eq_affineSlopeCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCheckpointCurvatureSource N =
      suzukiTransitionCoreAffineSlopeCesaroSource N := by
  rw [suzukiTransitionCoreCheckpointCurvatureSource,
    suzukiTransitionCoreAffineSlopeCesaroSource,
    ← suzukiCheckpointWeightedSignedCurvaturePrefix_div_eq_affineSlopeCesaroDefect hN]
  ring

/-- Literal prime--polar--Gamma curvature and the affine-current high-pass are the same source. -/
theorem suzukiTransitionCorePrimePolarGammaCurvatureSource_eq_affineSlopeCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCorePrimePolarGammaCurvatureSource N =
      suzukiTransitionCoreAffineSlopeCesaroSource N := by
  rw [← suzukiTransitionCoreCheckpointCurvatureSource_eq_primePolarGamma,
    suzukiTransitionCoreCheckpointCurvatureSource_eq_affineSlopeCesaro hN]

/-- Completed Abel source in the same affine-current coordinate. -/
theorem suzukiTransitionCoreCompletedAbelSource_succ_eq_affineSlopeCesaro
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiTransitionCoreCompletedAbelSource (N + 1) =
      suzukiTransitionCoreAffineSlopeCesaroSource N := by
  rw [suzukiTransitionCoreCompletedAbelSource_succ_eq_checkpointCurvature hN,
    suzukiTransitionCoreCheckpointCurvatureSource_eq_affineSlopeCesaro hN]

/-- The affine-current high-pass drives the completed growing-rank Gamma energy. -/
theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_succ_eq_affineSlopeCesaro
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy (N + 1) =
      suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
        (suzukiTransitionCoreAffineSlopeCesaroSource N /
          unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ 2 := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_eq_completedAbelSource
      (by omega : 2 ≤ N + 1) hcharge,
    suzukiTransitionCoreCompletedAbelSource_succ_eq_affineSlopeCesaro hN]

/-- Multi-gate Xi landing in affine-current coordinates, preserving multiplicity, both reflection
orientations, and the four-orientation non-spectral conormal factor. -/
theorem suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_succ_eq_affineSlopeCesaro
    {N : ℕ} (hN : 2 ≤ N)
    (hcharge : unitRieszCoherentPrimeOutgoingCharge (N + 1) ≠ 0)
    (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy (N + 1) rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy (N + 1) *
          (suzukiTransitionCoreAffineSlopeCesaroSource N /
            unitRieszCoherentPrimeOutgoingCharge (N + 1)) ^ 2 *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq_completedAbelSource
      (by omega : 2 ≤ N + 1) hcharge,
    suzukiTransitionCoreCompletedAbelSource_succ_eq_affineSlopeCesaro hN]

end


end GaloisForLFunctions.RHTower
