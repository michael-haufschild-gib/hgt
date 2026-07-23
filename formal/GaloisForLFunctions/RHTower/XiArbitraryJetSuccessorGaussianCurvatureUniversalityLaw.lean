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

/-- Complete complex/real arbitrary-jet reconstruction package together with the full
successor-aperture Möbius dyadic Gaussian geometry. -/
structure XiDerivativeOrderSuccessorGaussianCurvatureCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  complexCofiniteReconstruction :
    CofiniteEvaluationHilbertReconstruction (xiDerivativeOrderFamily order)
  realChannelCofiniteReconstruction :
    XiDerivativeOrderRealChannelCofiniteHilbertReconstruction order
  complexCoefficientRealChannelCofiniteReconstruction :
    XiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction order
  successorApertureExactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      (xiDerivativeOrderSuccessorAperture order)
      sourcePrime metricPrime m t

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
      complexCofiniteReconstruction :=
        (xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order).2 horder
      realChannelCofiniteReconstruction :=
        (xiDerivativeOrderRealChannelCofiniteHilbertReconstruction_iff_injective
          order).2 horder
      complexCoefficientRealChannelCofiniteReconstruction :=
        (xiDerivativeOrderComplexCoefficientRealChannelCofiniteHilbertReconstruction_iff_injective
          order).2 horder
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
      ⟨(xiDerivativeOrderCofiniteHilbertReconstruction_iff_injective order).1
          hcertificate.complexCofiniteReconstruction,
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

end

end RHTower
