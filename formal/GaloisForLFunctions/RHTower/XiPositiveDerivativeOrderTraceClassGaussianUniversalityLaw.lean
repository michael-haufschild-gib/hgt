import GaloisForLFunctions.RHTower.XiArbitraryJetSuccessorGaussianCurvatureUniversalityLaw
import GaloisForLFunctions.RHTower.XiApertureTraceClassGaussianCurvatureUniversalityLaw

/-!
# Positive Xi derivative orders, trace class, and Gaussian curvature

The canonical successor aperture sends derivative order `n` to `n + 1`.  Arbitrary completed-Xi
jet reconstruction needs only collision-free derivative orders, whereas the prime transport
becomes trace class exactly when every aperture is at least two and its canonical counterterm
vanishes.  Under successor relabeling, that extra threshold is exactly positivity of every
derivative order.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Minimal positive-order trace-class Gaussian certificate.  Successor trace-class curvature
already contains the exact-Hilbert field that forces every arbitrary-jet reconstruction. -/
structure XiPositiveDerivativeOrderTraceClassGaussianCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  traceClassCurvature :
    XiApertureTraceClassGaussianCurvatureCertificate
      (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
      sourcePrime metricPrime m t

namespace XiPositiveDerivativeOrderTraceClassGaussianCertificate

/-- The shared successor exact-Hilbert field derives the arbitrary-jet curvature certificate. -/
theorem arbitraryJetCurvature
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t) :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
      order sourcePrime metricPrime m t :=
  { successorApertureExactHilbertCurvature :=
      hcertificate.traceClassCurvature.exactHilbertCurvature }

/-- Trace-class successor geometry unconditionally forces distinct derivative orders. -/
theorem orderInjective
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t) :
    Function.Injective order :=
  hcertificate.arbitraryJetCurvature.orderInjective

/-- The successor aperture threshold is exactly positivity of every derivative order. -/
theorem orderPositive
    {d : ℕ} {order : Fin d → ℕ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t) :
    ∀ j, order j ≠ 0 := by
  intro j
  apply Nat.one_le_iff_ne_zero.mp
  exact Nat.le_of_succ_le_succ (by
    simpa [xiDerivativeOrderSuccessorAperture] using
      (hcertificate.traceClassCurvature.apertureThresholdAndZeroCounterterm j).1)

end XiPositiveDerivativeOrderTraceClassGaussianCertificate

/-- **Positive derivative-order trace-class Gaussian universality law.**  Distinct positive
derivative orders and rank at least two are exactly simultaneous complex/real arbitrary-jet
reconstruction and successor-aperture trace-class transport with zero counterterm, exact Hilbert
recovery, global Gaussian concavity, strict curvature, and operator nonnormality. -/
theorem xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧ 2 ≤ d) ↔
      XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨⟨hinjective, hpositive⟩, hrank⟩
    refine {
      traceClassCurvature :=
        (xiAperture_traceClassGaussianCurvatureCertificate_iff
          (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
          sourcePrime metricPrime m t ht).1 ?_ }
    refine ⟨⟨(xiDerivativeOrderSuccessorAperture_injective_iff order).2 hinjective,
      ?_⟩, hrank⟩
    intro j
    refine ⟨?_, rfl⟩
    have hone : 1 ≤ order j := Nat.one_le_iff_ne_zero.mpr (hpositive j)
    simpa [xiDerivativeOrderSuccessorAperture] using Nat.succ_le_succ hone
  · intro hcertificate
    have harbitrary :=
      (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
        order sourcePrime metricPrime m t ht).2
          hcertificate.arbitraryJetCurvature
    exact ⟨⟨harbitrary.1, hcertificate.orderPositive⟩, harbitrary.2⟩

/-- **Universal positive derivative-order trace-class curvature law.**  The same elementary
positive collision-free rank-two stratum controls the joint certificate uniformly in both primes,
jet depth, and every nonnegative Gaussian scale. -/
theorem
    xiPositiveDerivativeOrder_injective_and_rank_two_iff_every_traceClassGaussianCertificate
    {d : ℕ} (order : Fin d → ℕ) :
    ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧ 2 ≤ d) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiPositiveDerivativeOrderTraceClassGaussianCertificate
          order sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
        order sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
        order p p 0 0 le_rfl).2 hcertificate

/-- **Exact trace-class/sign-duality factorization.**  Positive-order trace-class Gaussian
geometry at one source target is exactly positivity of every derivative order together with
successor-aperture reconstruction sign duality at any independently chosen target. -/
theorem
    xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_positive_and_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t ↔
      (∀ j, order j ≠ 0) ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          (xiDerivativeOrderSuccessorAperture order)
          jetDepth valuationPrime valuationScale := by
  calc
    _ ↔ ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧
          2 ≤ d) :=
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
        order sourcePrime metricPrime m t ht).symm
    _ ↔ (∀ j, order j ≠ 0) ∧
          (Function.Injective order ∧ 2 ≤ d) := by
      constructor
      · rintro ⟨⟨hinjective, hpositive⟩, htwo⟩
        exact ⟨hpositive, hinjective, htwo⟩
      · rintro ⟨hpositive, hinjective, htwo⟩
        exact ⟨⟨hinjective, hpositive⟩, htwo⟩
    _ ↔
        (∀ j, order j ≠ 0) ∧
          XiDerivativeOrderSuccessorGaussianCurvatureCertificate
            order sourcePrime metricPrime m t :=
      and_congr Iff.rfl
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
          order sourcePrime metricPrime m t ht)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff_curvatureSignDuality
          order sourcePrime metricPrime m t ht
          jetDepth valuationPrime valuationScale hvaluationScale)

/-- **Universal trace-class/sign-duality factorization.**  A positive-order trace-class
Gaussian certificate at one nonnegative stored scale is exactly derivative-order positivity
together with successor-aperture sign duality at every depth, prime, and nonnegative scale. -/
theorem
    xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff_positive_and_every_curvatureSignDuality
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiPositiveDerivativeOrderTraceClassGaussianCertificate
        order sourcePrime metricPrime m t ↔
      (∀ j, order j ≠ 0) ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              (xiDerivativeOrderSuccessorAperture order)
              jetDepth valuationPrime valuationScale := by
  calc
    _ ↔ ((Function.Injective order ∧ ∀ j, order j ≠ 0) ∧
          2 ≤ d) :=
      (xiPositiveDerivativeOrder_traceClassGaussianCertificate_iff
        order sourcePrime metricPrime m t ht).symm
    _ ↔ (∀ j, order j ≠ 0) ∧
          (Function.Injective order ∧ 2 ≤ d) := by
      constructor
      · rintro ⟨⟨hinjective, hpositive⟩, htwo⟩
        exact ⟨hpositive, hinjective, htwo⟩
      · rintro ⟨hpositive, hinjective, htwo⟩
        exact ⟨⟨hinjective, hpositive⟩, htwo⟩
    _ ↔
        (∀ j, order j ≠ 0) ∧
          XiDerivativeOrderSuccessorGaussianCurvatureCertificate
            order sourcePrime metricPrime m t :=
      and_congr Iff.rfl
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
          order sourcePrime metricPrime m t ht)
    _ ↔ _ :=
      and_congr Iff.rfl
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff_every_curvatureSignDuality
          order sourcePrime metricPrime m t ht)

end

end RHTower
