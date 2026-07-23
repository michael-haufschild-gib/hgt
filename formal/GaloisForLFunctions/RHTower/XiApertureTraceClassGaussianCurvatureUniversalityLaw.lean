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

/-- Joint channelwise trace-class/counterterm phase and the complete Möbius dyadic Gaussian
curvature exact-Hilbert package. -/
structure XiApertureTraceClassGaussianCurvatureCertificate
    {N : ℕ} (shift : Fin N → ℕ) (c : Fin N → ℝ)
    (sourcePrime metricPrime : Nat.Primes) (m : ℕ) (t : ℝ) : Prop where
  exactHilbertCurvature :
    XiMobiusDyadicGaussianCurvatureExactHilbertCertificate
      shift sourcePrime metricPrime m t
  traceClassGain :
    ∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))
  canonicalCountertermPhase :
    ∀ j, Summable (fun p : Nat.Primes ↦
      xiAperturePrimeFusedResponseGainSq (shift j) p -
        (if shift j = 1 then 1 else 0) -
        c j * xiTransversePrimeApertureDiskNode 1 p)

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
    exact {
      exactHilbertCurvature :=
        (xiMobiusIntegralAperture_dyadicGaussianCurvatureExactHilbertCertificate_iff
          shift sourcePrime metricPrime m t ht).1 ⟨hdyadic, htwo⟩
      traceClassGain := hgain
      canonicalCountertermPhase := hcounterterm }
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
