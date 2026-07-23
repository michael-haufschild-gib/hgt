import GaloisForLFunctions.RHTower.XiApertureCountertermPhaseUniversalityLaw
import GaloisForLFunctions.RHTower.XiMobiusDyadicGaussianCurvatureUniversalityLaw

/-!
# Xi aperture trace-class Gaussian-curvature universality

Existing aperture transport results classify the channelwise trace-class phase and its unique
prime-harmonic counterterm: exact recovery plus summable gain forces every integral aperture to
be at least two, and then every canonical counterterm is zero.  Existing Möbius dyadic results
classify the same exact-recovery background, while HilbertMetric supplies its sharp rank-two
Gaussian-curvature law.

This file combines those results without introducing new analytic hypotheses.  It identifies
simultaneous trace-class transport, zero counterterm, exact Hilbert recovery, global Gaussian
concavity, strict curvature, and operator nonnormality with the elementary collision-free,
depth-at-least-two, packet-rank-at-least-two stratum.  The certificate is uniform in source prime,
metric prime, jet depth, and nonnegative metric scale.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Minimal joint trace-class/curvature certificate.  The elementary aperture threshold and zero
counterterm, together with exact-Hilbert curvature, derive both analytic summability interfaces. -/
structure XiApertureTraceClassGaussianCurvatureCertificate
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  exactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      shift sourcePrime metricPrime m t
  apertureThresholdAndZeroCounterterm :
    ∀ j, 2 ≤ shift j ∧ c j = 0

namespace XiApertureTraceClassGaussianCurvatureCertificate

/-- Existing reconstruction/trace-class classification derives both summability interfaces. -/
theorem traceClassAndCountertermPhase
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
      (∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))) ∧
      (∀ j, Summable (fun p : Nat.Primes ↦
        xiAperturePrimeFusedResponseGainSq (shift j) p -
          (if shift j = 1 then 1 else 0) -
          c j * xiTransversePrimeApertureDiskNode 1 p)) :=
  (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_and_countertermPhase_iff
    shift m c).2
      ⟨hcertificate.exactHilbertCurvature.injectiveAndNeZero.1,
        hcertificate.apertureThresholdAndZeroCounterterm⟩

/-- Channelwise trace-class gain is a derived compatibility API. -/
theorem traceClassGain
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t) :
    ∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j)) :=
  hcertificate.traceClassAndCountertermPhase.2.1

/-- Canonically renormalized channelwise summability is also derived. -/
theorem canonicalCountertermPhase
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t) :
    ∀ j, Summable (fun p : Nat.Primes ↦
      xiAperturePrimeFusedResponseGainSq (shift j) p -
        (if shift j = 1 then 1 else 0) -
        c j * xiTransversePrimeApertureDiskNode 1 p) :=
  hcertificate.traceClassAndCountertermPhase.2.2

/-- Trace-class curvature inherits intrinsic Gaussian dimension at every prime. -/
theorem intrinsicDimensionCertificate
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (intrinsicPrime : Nat.Primes) :
    XiTransversePrimeValuationGaussianIntrinsicDimensionCertificate
      shift intrinsicPrime :=
  hcertificate.exactHilbertCurvature.intrinsicDimensionCertificate ht intrinsicPrime

/-- Trace-class curvature inherits reconstruction sign duality at arbitrary parameters. -/
theorem curvatureSignDualityCertificate
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t)
    (ht : 0 ≤ t) (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
      shift jetDepth valuationPrime valuationScale :=
  hcertificate.exactHilbertCurvature.curvatureSignDualityCertificate
    ht jetDepth valuationPrime valuationScale hvaluationScale

/-- Trace-class curvature inherits the full cross-prime valuation universality chain. -/
theorem valuationUniversalityPhase
    {N : ℕ} {shift : Fin N → ℕ} {c : Fin N → ℝ}
    {sourcePrime metricPrime : Nat.Primes} {m : ℕ} {t : ℝ}
    (hcertificate :
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t)
    (valuationCurvaturePrime operatorPrime intrinsicPrime : Nat.Primes)
    (valuationCurvatureScale operatorScale : ℝ)
    (hvaluationCurvatureScale : 0 ≤ valuationCurvatureScale)
    (hoperatorScale : 0 ≤ operatorScale) :
    XiTransversePrimeValuationGaussianCurvatureIntrinsicDifferentialUniversalityPhase
      shift valuationCurvaturePrime operatorPrime intrinsicPrime
      valuationCurvatureScale operatorScale :=
  hcertificate.exactHilbertCurvature.valuationUniversalityPhase
    valuationCurvaturePrime operatorPrime intrinsicPrime
    valuationCurvatureScale operatorScale
    hvaluationCurvatureScale hoperatorScale

end XiApertureTraceClassGaussianCurvatureCertificate

/-- **Trace-class reconstruction/curvature discharge.**  The existing exact-recovery,
trace-class-gain, and counterterm packet phase needs only the sharp packet-rank condition to
produce the complete Möbius dyadic Gaussian-curvature certificate. -/
theorem
    xiTransversePrimeJetAperture_traceClassCounterterm_and_two_le_iff_gaussianCurvatureCertificate
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        (∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))) ∧
        (∀ j, Summable (fun p : Nat.Primes ↦
          xiAperturePrimeFusedResponseGainSq (shift j) p -
            (if shift j = 1 then 1 else 0) -
            c j * xiTransversePrimeApertureDiskNode 1 p))) ∧
      2 ≤ N) ↔
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t := by
  constructor
  · rintro ⟨⟨hreconstruction, hgain, hcounterterm⟩, htwo⟩
    have hcondition :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift m).1 hreconstruction
    have hdyadic :=
      (xiMobiusIntegralApertureDyadicInnovationGram_posDef_iff_injective_ne_zero
        shift).2 hcondition
    have hapertureThresholdAndZeroCounterterm :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_and_countertermPhase_iff
        shift m c).1 ⟨hreconstruction, hgain, hcounterterm⟩
    exact {
      exactHilbertCurvature :=
        (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
          shift sourcePrime metricPrime m t ht).1 ⟨hdyadic, htwo⟩
      apertureThresholdAndZeroCounterterm :=
        hapertureThresholdAndZeroCounterterm.2 }
  · intro hcertificate
    have hdyadicRank :=
      (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
        shift sourcePrime metricPrime m t ht).2
          hcertificate.exactHilbertCurvature
    exact ⟨⟨hcertificate.exactHilbertCurvature.cofinitePrimeJetExactRecovery,
      hcertificate.traceClassGain, hcertificate.canonicalCountertermPhase⟩,
      hdyadicRank.2⟩

/-- **Exact trace-class/counterterm/curvature classification.**  The full analytic and metric
certificate is equivalent to collision-free aperture labels, every aperture lying beyond the
unit non-trace-class boundary with zero counterterm, and packet rank at least two. -/
theorem xiAperture_traceClassGaussianCurvatureCertificate_iff
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    ((Function.Injective shift ∧
        ∀ j, 2 ≤ shift j ∧ c j = 0) ∧
      2 ≤ N) ↔
      XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t := by
  calc
    _ ↔
        (XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
          (∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))) ∧
          (∀ j, Summable (fun p : Nat.Primes ↦
            xiAperturePrimeFusedResponseGainSq (shift j) p -
              (if shift j = 1 then 1 else 0) -
              c j * xiTransversePrimeApertureDiskNode 1 p))) ∧
        2 ≤ N :=
      and_congr
        (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_and_countertermPhase_iff
          shift m c).symm
        Iff.rfl
    _ ↔ _ :=
      xiTransversePrimeJetAperture_traceClassCounterterm_and_two_le_iff_gaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t ht

/-- **Exact trace-class/sign-duality factorization.**  The trace-class curvature certificate is
exactly its channelwise aperture threshold and zero counterterm together with reconstruction sign
duality at any independently chosen depth, valuation prime, and nonnegative scale. -/
theorem
    xiAperture_traceClassGaussianCurvatureCertificate_iff_threshold_and_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (jetDepth : ℕ) (valuationPrime : Nat.Primes)
    (valuationScale : ℝ) (hvaluationScale : 0 ≤ valuationScale) :
    XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t ↔
      (∀ j, 2 ≤ shift j ∧ c j = 0) ∧
        XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
          shift jetDepth valuationPrime valuationScale := by
  constructor
  · intro hcertificate
    have hcondition :=
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        shift c sourcePrime metricPrime m t ht).2 hcertificate
    have hne : ∀ j, shift j ≠ 0 := by
      intro j hzero
      have htwo : 2 ≤ shift j := (hcondition.1.2 j).1
      omega
    have hreconstruction :
        XiTransversePrimeJetApertureCofiniteHilbertReconstruction
          shift jetDepth :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift jetDepth).2 ⟨hcondition.1.1, hne⟩
    exact
      ⟨hcondition.1.2,
        (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
          shift jetDepth valuationPrime valuationScale hvaluationScale).1
            ⟨hreconstruction, hcondition.2⟩⟩
  · rintro ⟨hthreshold, hsignDuality⟩
    have hphase :=
      (xiTransversePrimeValuationGaussianCurvatureSignDualityCertificate_iff
        shift jetDepth valuationPrime valuationScale hvaluationScale).2
          hsignDuality
    have hinjective :=
      ((xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero
        shift jetDepth).1 hphase.1).1
    exact
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        shift c sourcePrime metricPrime m t ht).1
          ⟨⟨hinjective, hthreshold⟩, hphase.2⟩

/-- **Universal trace-class/sign-duality factorization.**  One trace-class curvature certificate
is exactly its threshold/zero-counterterm data together with reconstruction sign duality at every
depth, valuation prime, and nonnegative scale. -/
theorem
    xiAperture_traceClassGaussianCurvatureCertificate_iff_threshold_and_every_curvatureSignDuality
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    XiApertureTraceClassGaussianCurvatureCertificate
        shift c sourcePrime metricPrime m t ↔
      (∀ j, 2 ≤ shift j ∧ c j = 0) ∧
        ∀ (jetDepth : ℕ) (valuationPrime : Nat.Primes)
          (valuationScale : ℝ), 0 ≤ valuationScale →
            XiTransversePrimeValuationGaussianCurvatureSignDualityCertificate
              shift jetDepth valuationPrime valuationScale := by
  constructor
  · intro hcertificate
    have hcondition :=
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        shift c sourcePrime metricPrime m t ht).2 hcertificate
    refine ⟨hcondition.1.2, ?_⟩
    intro jetDepth valuationPrime valuationScale hvaluationScale
    exact
      (xiAperture_traceClassGaussianCurvatureCertificate_iff_threshold_and_curvatureSignDuality
        shift c sourcePrime metricPrime m t ht
        jetDepth valuationPrime valuationScale hvaluationScale).1 hcertificate |>.2
  · rintro ⟨hthreshold, hall⟩
    let valuationPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
    exact
      (xiAperture_traceClassGaussianCurvatureCertificate_iff_threshold_and_curvatureSignDuality
        shift c sourcePrime metricPrime m t ht
        m valuationPrime 0 le_rfl).2
          ⟨hthreshold, hall m valuationPrime 0 le_rfl⟩

/-- **Universal trace-class Gaussian-curvature law.**  The elementary collision-free,
depth-at-least-two, rank-at-least-two stratum is exactly the phase in which the full transport,
counterterm, reconstruction, and curvature certificate holds at every pair of primes, every jet
depth, and every nonnegative metric scale. -/
theorem
    xiAperture_injective_two_le_zeroCounterterm_and_rank_two_iff_every_gaussianCurvatureCertificate
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ) :
    ((Function.Injective shift ∧
        ∀ j, 2 ≤ shift j ∧ c j = 0) ∧
      2 ≤ N) ↔
      ∀ (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ), 0 ≤ t →
        XiApertureTraceClassGaussianCurvatureCertificate
          shift c sourcePrime metricPrime m t := by
  constructor
  · intro h sourcePrime metricPrime m t ht
    exact
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        shift c sourcePrime metricPrime m t ht).1 h
  · intro hall
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hcertificate := hall p p 0 0 le_rfl
    exact
      (xiAperture_traceClassGaussianCurvatureCertificate_iff
        shift c p p 0 0 le_rfl).2 hcertificate

end

end RHTower
