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

/-- Joint arbitrary-Xi-jet reconstruction and successor-aperture trace-class Gaussian geometry. -/
structure XiPositiveDerivativeOrderTraceClassGaussianCertificate
    {d : ℕ} (order : Fin d → ℕ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  arbitraryJetCurvature :
    XiDerivativeOrderSuccessorGaussianCurvatureCertificate
      order sourcePrime metricPrime m t
  traceClassCurvature :
    XiApertureTraceClassGaussianCurvatureCertificate
      (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
      sourcePrime metricPrime m t

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
      arbitraryJetCurvature :=
        (xiDerivativeOrder_successorGaussianCurvatureCertificate_iff
          order sourcePrime metricPrime m t ht).1 ⟨hinjective, hrank⟩
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
    have htrace :=
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        (xiDerivativeOrderSuccessorAperture order) (fun _ ↦ 0)
        sourcePrime metricPrime m t ht).2
          hcertificate.traceClassCurvature
    refine ⟨⟨harbitrary.1, ?_⟩, harbitrary.2⟩
    intro j
    have htwo := (htrace.1.2 j).1
    apply Nat.one_le_iff_ne_zero.mp
    exact Nat.le_of_succ_le_succ (by
      simpa [xiDerivativeOrderSuccessorAperture] using htwo)

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

end

end RHTower
