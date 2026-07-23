import GaloisForLFunctions.RHTower.XiArbitraryJetSuccessorGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiApertureTraceClassGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianRadicalConnector
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity

/-!
# Positive Xi derivative orders, trace class, and intrinsic dimension

The successor aperture of a positive collision-free completed-Xi derivative dictionary carries
both the trace-class Gaussian-curvature phase and a one-dimensional first-valuation intrinsic
Gaussian determinant sandwich.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HilbertMetric

/-- First transverse valuation of the successor aperture, in mathlib's Euclidean wrapper. -/
def xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    Fin d → EuclideanSpace ℝ (Fin 1) :=
  fun j => WithLp.toLp 2
    (xiTransversePrimeFirstValuationGaussianFeature (order j + 1) p)

/-- The intrinsic successor configuration remembers exactly derivative-order collisions. -/
theorem xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_injective_iff
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    Function.Injective
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) ↔
      Function.Injective order := by
  constructor
  · intro hconfiguration i j hij
    apply hconfiguration
    simp [xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration, hij]
  · intro horder i j hij
    apply horder
    apply Nat.add_right_cancel
    apply xiTransversePrimeFirstValuationGaussianFeature_injective p
    exact WithLp.toLp_injective 2 hij

/-- Intrinsic corrected Gaussian log scale of the successor first-valuation packet. -/
def xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) (s : ℝ) : ℝ :=
  gaussianCorrectedLogScale
    (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) s

/-- Intrinsic dimension-power log determinant of the successor first-valuation packet. -/
def xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) (u : ℝ) : ℝ :=
  gaussianCorrectedDimensionPowerLogDet
    (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) u

/-- Literal positive-bandwidth corrected log determinant of the successor packet. -/
def xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) (u : ℝ) : ℝ :=
  Real.log
    (gaussianCorrectedDeterminant
      (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) u)

/-- Collision freedom and rank two force exact intrinsic affine dimension one. -/
theorem
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_gaussianAffineDimension_eq_one
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) :
    gaussianAffineDimension
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) = 1 := by
  let x := xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p
  have hx : Function.Injective x :=
    (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_injective_iff
      order p).2 hinjective
  have hpos : 0 < gaussianAffineDimension x :=
    gaussianAffineDimension_pos_of_injective x hx (by omega)
  have hle :
      gaussianAffineDimension x ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) := by
    unfold gaussianAffineDimension
    exact Submodule.finrank_le _
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1 := by
    simp
  rw [hambient] at hle
  change gaussianAffineDimension x = 1
  omega

/-- In intrinsic dimension one, dimension-power is logarithmic reparametrization. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_log
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) (u : ℝ) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet order p u =
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
        order p (Real.log u) := by
  unfold xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
    gaussianCorrectedDimensionPowerLogDet
  rw [
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_gaussianAffineDimension_eq_one
      order p hinjective htwo]
  simp

/-- On positive bandwidth, dimension-power is the literal corrected log determinant. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d)
    {u : ℝ} (hu : 0 < u) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet order p u =
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet order p u := by
  unfold xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
  rw [gaussianCorrectedDimensionPowerLogDet_eq_rpow _ hu]
  rw [
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_gaussianAffineDimension_eq_one
      order p hinjective htwo]
  simp

/-- Literal bandwidth concavity of the corrected successor determinant. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet order p) := by
  have hx :
      Function.Injective
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) :=
    (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_injective_iff
      order p).2 hinjective
  have hconcave :
      ConcaveOn ℝ (Set.Ioi 0)
        (xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
          order p) := by
    simpa [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet] using
      (gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p)
        hx (by omega)).2
  apply hconcave.congr
  intro u hu
  exact
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
      order p hinjective htwo hu

/-- Joint trace-class successor-aperture geometry and first-valuation intrinsic dimension. -/
structure XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) : Prop where
  arbitraryJetCurvature :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
      order sourcePrime curvaturePrime m t
  traceClassCurvature :
    XiApertureTraceClassGaussianCurvatureCertificate
      (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
      sourcePrime curvaturePrime m t
  affineDimensionOne :
    gaussianAffineDimension
      (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration
        order intrinsicPrime) = 1
  correctedLogScaleConvex :
    ConvexOn ℝ Set.univ
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
        order intrinsicPrime)
  correctedDimensionPowerConcave :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
        order intrinsicPrime)
  correctedBandwidthLogDetConcave :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
        order intrinsicPrime)
  dimensionPowerBandwidthCollapse :
    Set.EqOn
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
        order intrinsicPrime)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
        order intrinsicPrime)
      (Set.Ioi 0)
  dimensionPowerCollapse :
    ∀ u,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
          order intrinsicPrime u =
        xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
          order intrinsicPrime (Real.log u)

/-- **Positive derivative-order trace-class intrinsic-dimension law.** Distinct positive
derivative orders and rank at least two exactly control the joint three-prime certificate. -/
theorem xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧ 2 ≤ d) ↔
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t := by
  constructor
  · rintro ⟨⟨hinjective, hpositive⟩, hrank⟩
    have hx :
        Function.Injective
          (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration
            order intrinsicPrime) :=
      (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_injective_iff
        order intrinsicPrime).2 hinjective
    have hsandwich :=
      gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration
          order intrinsicPrime) hx (by omega)
    exact {
      arbitraryJetCurvature :=
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
          order sourcePrime curvaturePrime m t ht).1 ⟨hinjective, hrank⟩
      traceClassCurvature :=
        (xiAperture_traceClassGaussianCurvatureCertificate_iff
          (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
          sourcePrime curvaturePrime m t ht).1
            ⟨⟨(xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective,
              fun j ↦ by
                refine ⟨?_, rfl⟩
                have hone : 1 ≤ order j := Nat.one_le_iff_ne_zero.mpr (hpositive j)
                simpa [xiDerivativeOrderSuccessorAperture] using Nat.succ_le_succ hone⟩,
              hrank⟩
      affineDimensionOne :=
        xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_gaussianAffineDimension_eq_one
          order intrinsicPrime hinjective hrank
      correctedLogScaleConvex := by
        simpa [xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale] using
          hsandwich.1
      correctedDimensionPowerConcave := by
        simpa
          [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet] using
          hsandwich.2
      correctedBandwidthLogDetConcave :=
        xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
          order intrinsicPrime hinjective hrank
      dimensionPowerBandwidthCollapse :=
        fun _ hu ↦
          xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
            order intrinsicPrime hinjective hrank hu
      dimensionPowerCollapse :=
        xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_log
          order intrinsicPrime hinjective hrank }
  · intro h
    have harbitrary :=
      (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
        order sourcePrime curvaturePrime m t ht).2 h.arbitraryJetCurvature
    have htrace :=
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
        sourcePrime curvaturePrime m t ht).2 h.traceClassCurvature
    refine ⟨⟨harbitrary.1, ?_⟩, harbitrary.2⟩
    intro j
    apply Nat.one_le_iff_ne_zero.mp
    exact Nat.le_of_succ_le_succ (by
      simpa [xiDerivativeOrderSuccessorAperture] using (htrace.1.2 j).1)

/-- The same elementary stratum controls the stronger certificate uniformly in all three primes,
jet depth, and every nonnegative scale. -/
theorem
    xiPositiveDerivativeOrder_injective_and_rank_two_iff_every_traceClassIntrinsicDimensionCertificate
    {d : ℕ} (order : Fin d → ℕ) :
    ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧ 2 ≤ d) ↔
      ∀ (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
        (m : ℕ) (t : ℝ), 0 ≤ t →
          XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
            order sourcePrime curvaturePrime intrinsicPrime m t := by
  constructor
  · intro h sourcePrime curvaturePrime intrinsicPrime m t ht
    exact
      (xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
        order sourcePrime curvaturePrime intrinsicPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    exact
      (xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
        order p p p 0 0 le_rfl).2 (hall p p p 0 0 le_rfl)

end

end RHTower
