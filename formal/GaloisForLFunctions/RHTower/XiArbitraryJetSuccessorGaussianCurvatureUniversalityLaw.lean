import GaloisForLFunctions.RHTower.XiArbitraryJetRealChannelCofiniteHilbertReconstruction
import GaloisForLFunctions.RHTower.XiMobiusDyadicGaussianCurvatureUniversalityLaw

/-!
# Arbitrary completed-Xi jets and successor-aperture Gaussian curvature

Arbitrary completed-Xi derivative dictionaries have exact complex, real-channel, and full
complex-coefficient cofinite reconstruction precisely when their derivative orders are distinct.
Transverse Xi aperture reconstruction has one additional condition: its integral labels must be
nonzero.

The canonical successor relabeling `n ↦ n + 1` preserves every derivative-order collision and
automatically excludes zero.  It therefore discharges the extra transverse hypothesis without an
assumption.  Combining the existing HTGeometry reconstruction classifications with the
HilbertMetric curvature law identifies collision-free arbitrary jets of rank at least two with a
universal exact-Hilbert, strict-curvature, concavity, and operator-nonnormality phase.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical positive aperture attached to a completed-Xi derivative order. -/
def xiDerivativeOrderSuccessorAperture
    {d : ℕ} (order : Fin d → ℕ) : Fin d → ℕ :=
  fun j => Nat.succ (order j)

/-- Successor relabeling preserves exactly the derivative-order collision relation. -/
theorem xiDerivativeOrderSuccessorAperture_injective_iff
    {d : ℕ} (order : Fin d → ℕ) :
    Function.Injective (xiDerivativeOrderSuccessorAperture order) ↔
      Function.Injective order := by
  constructor
  · intro hsuccessor i j hij
    apply hsuccessor
    simp [xiDerivativeOrderSuccessorAperture, hij]
  · intro horder i j hij
    apply horder
    exact Nat.succ.inj (by
      simpa only [xiDerivativeOrderSuccessorAperture] using hij)

/-- Every successor aperture is nonzero, with no hypothesis on the derivative-order dictionary. -/
theorem xiDerivativeOrderSuccessorAperture_ne_zero
    {d : ℕ} (order : Fin d → ℕ) (j : Fin d) :
    xiDerivativeOrderSuccessorAperture order j ≠ 0 :=
  Nat.succ_ne_zero _

/-- **Unconditional arbitrary-jet/transverse reconstruction connector.**  Cofinite exact
reconstruction of a completed-Xi derivative dictionary is exactly transverse prime-jet
reconstruction of its successor-aperture packet.  Successor relabeling discharges the transverse
nonzero-label condition. -/
theorem
    xiDerivativeOrderCofiniteHilbertReconstruction_iff_successorApertureCofiniteHilbertReconstruction
    {d : ℕ} (order : Fin d → ℕ) (m : ℕ) :
    CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ↔
      XiTransversePrimeJetApertureCofiniteHilbertReconstruction
        (xiDerivativeOrderSuccessorAperture order) m := by
  calc
    _ ↔ Function.Injective order :=
      xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order
    _ ↔ Function.Injective (xiDerivativeOrderSuccessorAperture order) ∧
          ∀ j, xiDerivativeOrderSuccessorAperture order j ≠ 0 := by
      constructor
      · intro horder
        exact ⟨(xiDerivativeOrderSuccessorAperture_injective_iff order).2 horder,
          xiDerivativeOrderSuccessorAperture_ne_zero order⟩
      · rintro ⟨hsuccessor, _⟩
        exact (xiDerivativeOrderSuccessorAperture_injective_iff order).1 hsuccessor
    _ ↔ _ :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        (xiDerivativeOrderSuccessorAperture order) m).symm

/-- **Arbitrary-jet/Gaussian-curvature connector.**  Cofinite reconstruction of the completed-Xi
derivative dictionary plus the sharp rank-two condition is exactly the Gaussian-curvature phase
of its successor-aperture packet at every metric prime and nonnegative scale. -/
theorem
    xiDerivativeOrderCofiniteHilbertReconstruction_and_two_le_iff_successorApertureGaussianCurvaturePhase
    {d : ℕ} (order : Fin d → ℕ) (m : ℕ) (p : Nat.Primes)
    (t : ℝ) (ht : 0 ≤ t) :
    (CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ∧
        2 ≤ d) ↔
      XiTransversePrimeJetApertureGaussianCurvaturePhase
        (xiDerivativeOrderSuccessorAperture order) m p t := by
  calc
    _ ↔
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
            (xiDerivativeOrderSuccessorAperture order) m ∧
          2 ≤ d :=
      and_congr
        (xiDerivativeOrderCofiniteHilbertReconstruction_iff_successorApertureCofiniteHilbertReconstruction
          order m)
        Iff.rfl
    _ ↔ _ :=
      (xiTransversePrimeJetApertureGaussianCurvaturePhase_iff_reconstruction_and_two_le
        (xiDerivativeOrderSuccessorAperture order) m p t ht).symm

/-- Minimal successor-aperture Gaussian certificate.  Its dyadic innovation field already forces
derivative-order injectivity, hence every complex and real-channel reconstruction interface;
those interfaces are exposed below as derived dot APIs. -/
structure XiDerivativeOrderSuccessorGaussianCurvatureCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  successorApertureExactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      (xiDerivativeOrderSuccessorAperture order)
      sourcePrime metricPrime m t

namespace XiDerivativeOrderSuccessorGaussianCurvatureCertificate

/-- Successor innovation positivity recovers injectivity of the original derivative orders. -/
theorem orderInjective
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t) :
    Function.Injective order :=
  (xiDerivativeOrderSuccessorAperture_injective_iff order).1
    hcertificate.successorApertureExactHilbertCurvature.injectiveAndNeZero.1

/-- Complex arbitrary-jet cofinite reconstruction is derived from collision freedom. -/
theorem complexCofiniteReconstruction
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t) :
    CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) :=
  (xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order).2
    hcertificate.orderInjective

/-- Real-channel arbitrary-jet cofinite reconstruction is derived from collision freedom. -/
theorem realChannelCofiniteReconstruction
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t) :
    XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order :=
  (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
    order).2 hcertificate.orderInjective

/-- Full complex-coefficient real-channel reconstruction is also derived. -/
theorem complexCoefficientRealChannelCofiniteReconstruction
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t) :
    XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction order :=
  (xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
    order).2 hcertificate.orderInjective

/-- The arbitrary-jet certificate inherits intrinsic Gaussian dimension at every prime. -/
theorem successorApertureIntrinsicDimensionCertificate
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      (xiDerivativeOrderSuccessorAperture order) intrinsicPrime :=
  hcertificate.successorApertureExactHilbertCurvature.intrinsicDimensionCertificate
    ht intrinsicPrime

/-- Arbitrary jets inherit full reconstruction sign duality at independently chosen parameters. -/
theorem successorApertureCurvatureSignDualityCertificate
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      (xiDerivativeOrderSuccessorAperture order)
      jetDepth valuationPrime valuationScale :=
  hcertificate.successorApertureExactHilbertCurvature.curvatureSignDualityCertificate
    ht jetDepth valuationPrime valuationScale hvaluationScale

/-- Arbitrary jets inherit the full cross-prime valuation universality chain. -/
theorem successorApertureValuationUniversalityPhase
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      (xiDerivativeOrderSuccessorAperture order)
      valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  hcertificate.successorApertureExactHilbertCurvature.valuationUniversalityPhase
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale

end XiDerivativeOrderSuccessorGaussianCurvatureCertificate

/-- **Arbitrary-jet successor-curvature universality.**  Distinct derivative orders and rank at
least two are equivalent to simultaneous complex, real-channel, and full complex-coefficient
cofinite recovery plus the complete successor-aperture exact-Hilbert Gaussian-curvature package. -/
theorem xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (Function.Injective order ∧ 2 ≤ d) ↔
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨horder, htwo⟩
    have hsuccessor :=
      (xiDerivativeOrderSuccessorAperture_injective_iff order).2 horder
    have hdyadic :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        (xiDerivativeOrderSuccessorAperture order)).2
          ⟨hsuccessor, xiDerivativeOrderSuccessorAperture_ne_zero order⟩
    exact {
      successorApertureExactHilbertCurvature :=
        (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
          (xiDerivativeOrderSuccessorAperture order)
          sourcePrime metricPrime m t ht).1 ⟨hdyadic, htwo⟩ }
  · intro hcertificate
    have hdyadicRank :=
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        (xiDerivativeOrderSuccessorAperture order)
        sourcePrime metricPrime m t ht).2
          hcertificate.successorApertureExactHilbertCurvature
    exact
      ⟨hcertificate.orderInjective,
        hdyadicRank.2⟩

/-- The original complex cofinite-reconstruction interface itself can be used as the complete
input to the curvature-enhanced arbitrary-jet certificate, apart from the sharp rank threshold. -/
theorem
    xiDerivativeOrderCofiniteHilbertReconstruction_and_two_le_iff_successorGaussianCurvatureCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order) ∧
        2 ≤ d) ↔
      XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t := by
  calc
    _ ↔ Function.Injective order ∧ 2 ≤ d :=
      and_congr
        (xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order)
        Iff.rfl
    _ ↔ _ :=
      xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
        order sourcePrime metricPrime m t ht

/-- **Universal arbitrary-jet curvature law.**  Collision-free derivative orders of rank at least
two are exactly those whose complete complex/real reconstruction and successor-aperture Gaussian
geometry hold for every source prime, metric prime, jet depth, and nonnegative scale. -/
theorem
    xiDerivativeOrder_injective_and_two_le_iff_every_successorGaussianCurvatureCertificate
    {d : ℕ} (order : Fin d → ℕ) :
    (Function.Injective order ∧ 2 ≤ d) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiDerivativeOrderSuccessorGaussianCurvatureCertificate
          order sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
        order sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
        order p p 0 0 le_rfl).2 hcertificate

/-- **Exact arbitrary-jet successor/sign-duality connector.**  One successor-curvature
certificate is exactly reconstruction sign duality for the successor aperture at any
independently chosen depth, prime, and nonnegative scale. -/
theorem
    xiDerivativeOrder_successorGaussianCurvatureCertificate_iff_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t ↔
      XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
        (xiDerivativeOrderSuccessorAperture order)
        jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
          (xiDerivativeOrderSuccessorAperture order)
          sourcePrime metricPrime m t := by
      constructor
      · exact fun hcertificate =>
          hcertificate.successorApertureExactHilbertCurvature
      · exact fun hcertificate =>
          ⟨hcertificate⟩
    _ ↔ _ :=
      xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_curvatureSignDuality
        (xiDerivativeOrderSuccessorAperture order)
        sourcePrime metricPrime m t ht
        jetDepth valuationPrime valuationScale hvaluationScale

/-- **Universal arbitrary-jet successor/sign-duality law.**  One successor-curvature
certificate at a nonnegative stored scale is exactly reconstruction sign duality for the
successor aperture at every target depth, prime, and nonnegative scale. -/
theorem
    xiDerivativeOrder_successorGaussianCurvatureCertificate_iff_every_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
        order sourcePrime metricPrime m t ↔
      ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
        (valuationScale : ℝ), 0 ≤ valuationScale →
          XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
            (xiDerivativeOrderSuccessorAperture order)
            jetDepth valuationPrime valuationScale := by
  calc
    _ ↔
        XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
          (xiDerivativeOrderSuccessorAperture order)
          sourcePrime metricPrime m t := by
      constructor
      · exact fun hcertificate =>
          hcertificate.successorApertureExactHilbertCurvature
      · exact fun hcertificate =>
          ⟨hcertificate⟩
    _ ↔ _ :=
      xiMobius_dyadicGaussianCurvatureExactHilbertCertificate_iff_every_curvatureSignDuality
        (xiDerivativeOrderSuccessorAperture order)
        sourcePrime metricPrime m t ht

end

end RHTower
