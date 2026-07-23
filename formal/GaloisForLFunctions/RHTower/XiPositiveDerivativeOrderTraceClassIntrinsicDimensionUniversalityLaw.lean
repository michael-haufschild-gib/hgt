import GaloisForLFunctions.RHTower.XiPositiveDerivativeOrderTraceClassGaussianUniversalityLaw
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianIntrinsicDimensionUniversalityLaw

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

/-- The successor intrinsic configuration is exactly the general transverse configuration
specialized to the canonical successor aperture. -/
@[simp] theorem
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_eq_transverse
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p =
      xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration
        (xiDerivativeOrderSuccessorAperture order) p := by
  rfl

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

/-- Successor corrected log scale is the transverse corrected log scale under successor
relabeling. -/
@[simp] theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale_eq_transverse
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale order p =
      xiTransversePrimeValuationCorrectedGaussianLogScale
        (xiDerivativeOrderSuccessorAperture order) p := by
  rfl

/-- Successor dimension-power coordinate is the transverse dimension-power coordinate under
successor relabeling. -/
@[simp] theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet order p =
      xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet
        (xiDerivativeOrderSuccessorAperture order) p := by
  rfl

/-- Successor literal bandwidth coordinate is the transverse bandwidth coordinate under
successor relabeling. -/
@[simp] theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_eq_transverse
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet order p =
      xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet
        (xiDerivativeOrderSuccessorAperture order) p := by
  rfl

/-- Collision freedom and rank two force exact intrinsic affine dimension one. -/
theorem
    xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_gaussianAffineDimension_eq_one
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) :
    gaussianAffineDimension
        (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration order p) = 1 := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_eq_transverse] using
      (xiTransversePrimeFirstValuationIntrinsicHilbertConfiguration_gaussianAffineDimension_eq_one
        (xiDerivativeOrderSuccessorAperture order) p
        ((xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective)
        htwo)

/-- In intrinsic dimension one, dimension-power is logarithmic reparametrization. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_log
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) (u : ℝ) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet order p u =
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
        order p (Real.log u) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale_eq_transverse] using
      (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_log
        (xiDerivativeOrderSuccessorAperture order) p
        ((xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective)
        htwo u)

/-- On positive bandwidth, dimension-power is the literal corrected log determinant. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d)
    {u : ℝ} (hu : 0 < u) :
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet order p u =
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet order p u := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_eq_transverse] using
      (xiTransversePrimeValuationCorrectedGaussianDimensionPowerLogDet_eq_bandwidthLogDet
        (xiDerivativeOrderSuccessorAperture order) p
        ((xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective)
        htwo hu)

/-- Literal bandwidth concavity of the corrected successor determinant. -/
theorem
    xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
    {d : ℕ} (order : Fin d → ℕ) (p : Nat.Primes)
    (hinjective : Function.Injective order) (htwo : 2 ≤ d) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet order p) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_eq_transverse] using
      (xiTransversePrimeValuationCorrectedGaussianBandwidthLogDet_concaveOn_of_injective
        (xiDerivativeOrderSuccessorAperture order) p
        ((xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective)
        htwo)

/-- Minimal joint trace-class successor-aperture and first-valuation intrinsic-dimension
certificate.  Trace-class curvature already supplies arbitrary-jet reconstruction and collision
freedom; affine dimension one supplies packet rank.  All convexity, concavity,
coordinate-collapse, and cross-prime valuation laws are derived below. -/
structure XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) : Prop where
  traceClassCurvature :
    XiApertureTraceClassGaussianCurvatureCertificate
      (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
      sourcePrime curvaturePrime m t
  affineDimensionOne :
    gaussianAffineDimension
      (xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration
        order intrinsicPrime) = 1

namespace XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate

/-- Trace-class curvature contains the same successor exact-Hilbert field, so the arbitrary-jet
certificate is derived rather than stored twice. -/
theorem arbitraryJetCurvature
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
      order sourcePrime curvaturePrime m t :=
  { successorApertureExactHilbertCurvature :=
      hcertificate.traceClassCurvature.exactHilbertCurvature }

/-- Derived arbitrary-jet reconstruction discharges derivative-order collision freedom without
any sign condition on the scale carried by the certificate. -/
theorem orderInjective
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    Function.Injective order :=
  (xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order).1
    hcertificate.arbitraryJetCurvature.complexCofiniteReconstruction

/-- Collision freedom passes unconditionally to the canonical successor aperture. -/
theorem successorApertureInjective
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    Function.Injective (xiDerivativeOrderSuccessorAperture order) :=
  (xiDerivativeOrderSuccessorAperture_injective_iff order).2
    hcertificate.orderInjective

/-- Existing trace-class Gaussian certificate is the non-intrinsic projection of the minimal
certificate. -/
theorem traceClassGaussianCertificate
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    XiPositiveDerivativeOrderTraceClassGaussianCertificate
      order sourcePrime curvaturePrime m t :=
  { traceClassCurvature := hcertificate.traceClassCurvature }

/-- The positive-order intrinsic packet is exactly an instance of the general transverse
intrinsic certificate. -/
theorem successorApertureIntrinsicCertificate
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (xiDerivativeOrderSuccessorAperture order) intrinsicPrime :=
  { injective := hcertificate.successorApertureInjective
    affineDimensionOne := by
      simpa only
        [xiPositiveDerivativeOrderSuccessorIntrinsicConfiguration_eq_transverse] using
          hcertificate.affineDimensionOne }

/-- Affine dimension one now discharges the former explicit packet-rank premise. -/
theorem rankTwo
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    2 ≤ d :=
  hcertificate.successorApertureIntrinsicCertificate.rankTwo

/-- Corrected logarithmic scale convexity is inherited from transverse intrinsic geometry. -/
theorem correctedLogScaleConvex
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    ConvexOn ℝ Set.univ
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
        order intrinsicPrime) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale_eq_transverse] using
      hcertificate.successorApertureIntrinsicCertificate.correctedLogScaleConvex

/-- Corrected dimension-power concavity is inherited from transverse intrinsic geometry. -/
theorem correctedDimensionPowerConcave
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
        order intrinsicPrime) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse] using
      hcertificate.successorApertureIntrinsicCertificate.correctedDimensionPowerConcave

/-- Literal positive-bandwidth concavity follows from the minimal certificate. -/
theorem correctedBandwidthLogDetConcave
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    ConcaveOn ℝ (Set.Ioi 0)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
        order intrinsicPrime) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_eq_transverse] using
      hcertificate.successorApertureIntrinsicCertificate.correctedBandwidthLogDetConcave

/-- Dimension-power and literal positive-bandwidth coordinates agree on the positive ray. -/
theorem dimensionPowerBandwidthCollapse
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    Set.EqOn
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
        order intrinsicPrime)
      (xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet
        order intrinsicPrime)
      (Set.Ioi 0) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianBandwidthLogDet_eq_transverse] using
      hcertificate.successorApertureIntrinsicCertificate.dimensionPowerBandwidthCollapse

/-- Dimension-power globally collapses to logarithmic reparametrization. -/
theorem dimensionPowerCollapse
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t) :
    ∀ u,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet
          order intrinsicPrime u =
        xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale
          order intrinsicPrime (Real.log u) := by
  simpa only
    [xiPositiveDerivativeOrderSuccessorCorrectedGaussianDimensionPowerLogDet_eq_transverse,
      xiPositiveDerivativeOrderSuccessorCorrectedGaussianLogScale_eq_transverse] using
      hcertificate.successorApertureIntrinsicCertificate.dimensionPowerCollapse

/-- One positive trace-class/intrinsic certificate forces collision sign duality for the
successor aperture at every independently chosen prime and nonnegative scale. -/
theorem successorApertureCollisionSignDualityCertificate
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t)
    (valuationPrime : Nat.Primes) (valuationScale : ℝ)
    (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCollisionSignDualityCertificate
      (xiDerivativeOrderSuccessorAperture order) valuationPrime valuationScale :=
  (xiTransversePrimeValuationGaussianCollisionSignDualityCertificate_iff_intrinsicDimensionCertificate
    (xiDerivativeOrderSuccessorAperture order)
    valuationPrime intrinsicPrime valuationScale hvaluationScale).2
      hcertificate.successorApertureIntrinsicCertificate

/-- **Derivative-order/valuation universality connector.**  One stored trace-class/intrinsic
certificate forces the full transverse curvature, nonnormality, intrinsic-dimension, and
differential-rank equivalence chain at independently chosen primes and nonnegative scales. -/
theorem successorApertureValuationUniversalityPhase
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime curvaturePrime intrinsicPrime : Nat.Primes}
    {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t)
    (valuationCurvaturePrime operatorPrime valuationIntrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (xiDerivativeOrderSuccessorAperture order)
      valuationCurvaturePrime operatorPrime valuationIntrinsicPrime
      valuationCurvatureScale operatorScale :=
  xiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase_of_collisionSignDualityCertificate
    (xiDerivativeOrderSuccessorAperture order)
    valuationCurvaturePrime operatorPrime valuationIntrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale
    (hcertificate.successorApertureCollisionSignDualityCertificate
      valuationCurvaturePrime valuationCurvatureScale hvaluationCurvatureScale)

end XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate

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
    exact {
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

/-- **Intrinsic interface discharge.**  At a nonnegative stored scale, the existing positive
derivative-order trace-class Gaussian certificate already determines the complete intrinsic
certificate at every independently chosen intrinsic prime. -/
theorem
    xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_traceClassIntrinsicDimensionCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime curvaturePrime m t ↔
      XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t := by
  constructor
  · intro hcertificate
    exact
      (xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff
        order sourcePrime curvaturePrime intrinsicPrime m t ht).1
          ((xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
            order sourcePrime curvaturePrime m t ht).2 hcertificate)
  · intro hcertificate
    exact hcertificate.traceClassGaussianCertificate

/-- **Exact intrinsic/sign-duality factorization.**  The first-valuation affine-dimension
interface contributes no extra hypothesis: the joint trace-class/intrinsic certificate is
exactly derivative-order positivity plus successor-aperture sign duality at any target. -/
theorem
    xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff_positive_and_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t ↔
      (∀ j, order j ≠ 0) ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (xiDerivativeOrderSuccessorAperture order)
          jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiPositiveDerivativeOrderTraceClassGaussianCertificate
          order sourcePrime curvaturePrime m t :=
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_traceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t ht).symm
    _ ↔ _ :=
      xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_positive_and_curvatureSignDuality
        order sourcePrime curvaturePrime m t ht
        jetDepth valuationPrime valuationScale hvaluationScale

/-- **Universal intrinsic/sign-duality factorization.**  At a nonnegative stored scale, the
joint trace-class/intrinsic certificate is exactly derivative-order positivity plus
successor-aperture sign duality at every depth, prime, and nonnegative scale. -/
theorem
    xiPositiveDerivativeOrder_traceClassIntrinsicDimensionCertificate_iff_positive_and_every_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    XiPositiveDerivativeOrderTraceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t ↔
      (∀ j, order j ≠ 0) ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiDerivativeOrderSuccessorAperture order)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiPositiveDerivativeOrderTraceClassGaussianCertificate
          order sourcePrime curvaturePrime m t :=
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_traceClassIntrinsicDimensionCertificate
        order sourcePrime curvaturePrime intrinsicPrime m t ht).symm
    _ ↔ _ :=
      xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_positive_and_every_curvatureSignDuality
        order sourcePrime curvaturePrime m t ht

/-- The old trace-class Gaussian interface therefore also forces the full successor-aperture
valuation universality phase, with no relation required among the stored and valuation primes. -/
theorem
    xiPositiveDerivativeOrder_successorApertureValuationUniversalityPhase_of_traceClassGaussianCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime curvaturePrime intrinsicPrime : Nat.Primes)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime curvaturePrime m t)
    (valuationCurvaturePrime operatorPrime valuationIntrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (xiDerivativeOrderSuccessorAperture order)
      valuationCurvaturePrime operatorPrime valuationIntrinsicPrime
      valuationCurvatureScale operatorScale :=
  ((xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_traceClassIntrinsicDimensionCertificate
    order sourcePrime curvaturePrime intrinsicPrime m t ht).1 hcertificate
  ).successorApertureValuationUniversalityPhase
    valuationCurvaturePrime operatorPrime valuationIntrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale

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
