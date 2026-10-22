import GaloisForLFunctions.RHTower.Deninger.DeningerEntropyProductionThermodynamicLimitUniversalityLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerGaussianLefschetzHeatContourUniversalityLaw
import GaloisForLFunctions.RHTower.XiWholeCorpusPositivePhaseUniversalityLaw

/-!
# Deninger entropy/Gaussian heat-contour universality

Finite Hermitian KMS entropy-production convergence to the Deninger divisor resolvent forces RH.
That forced RH, in turn, supplies the complete eighteen-family Xi phase and arbitrarily accurate
Deninger Gaussian contour reconstruction of the complete Xi heat trace at every complex heat time
in the open right half-plane.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Joint thermodynamic-passivity and complex-time heat-contour certificate. -/
structure DeningerEntropyGaussianHeatContourCertificate
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ) : Prop where
  sourceLimit :
    ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))
  sourceUpperAntiHerglotz : ContinuedPrimeArchUpperAntiHerglotz
  deningerUpperAntiHerglotz : DeningerDivisorUpperAntiHerglotz
  oneCauchyGate : ContinuedPrimeArchUpperCauchyDiagonalNonnegative
  riemannHypothesis : RiemannHypothesis
  wholeCorpusPositivePhase :
    ∀ {Lrect : ℝ}, 0 < Lrect →
      ∀ {N : ℕ}, (∀ n : ℕ, N ≤ n →
        1 ≤ n ∧ Lrect ≤ Real.log n / 2) →
      ∀ {eta Lsmooth : ℝ}, 0 < eta → eta < Lsmooth - eta →
      ∀ (P : ℕ → XiSeparatedContinuedCauchyPacket),
        IsRectangularSeparatedSourceSection Lrect P →
      ∀ {D : ℕ → ℕ}, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      ∀ {degreeSet : Set ℕ}, degreeSet.Infinite →
      ∀ (prime : Nat.Primes) {q : ℕ}, q ≠ 0 →
        XiWholeCorpusPositivePhaseUniversalCertificate
          Lrect N eta Lsmooth P D degreeSet prime q
  gaussianHeatContours :
    ∀ {τ : ℂ}, 0 < τ.re → ∀ {epsilon : ℝ}, 0 < epsilon →
      ∃ z₁ z₂ : ℂ,
        z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
        let C := (2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => xiGaussianComplexTestC τ z *
            deningerDivisorRelativeResolventTrace z) z₁ z₂
        dist C (xiGaussianHeatTraceC τ) < epsilon ∧
          ‖C‖ < xiGaussianHeatTraceReal τ.re + epsilon

/--
**Deninger entropy/Gaussian heat-contour universality law.**

Every finite Hermitian KMS thermodynamic realization of the Deninger divisor resolvent forces the
complete passivity/RH certificate and, uniformly over all positive-real-part complex heat times,
arbitrarily accurate norm-controlled Deninger contour reconstruction of the Xi heat trace.
-/
theorem deningerEntropy_gaussianHeatContourUniversality
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b))
    (hconvDeninger : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (deningerDivisorRelativeResolventTrace z))) :
    DeningerEntropyGaussianHeatContourCertificate
      d β energy amplitude := by
  obtain ⟨hsourceLimit, hsource, hdeninger, hcauchy, hRH⟩ :=
    deninger_entropyProductionThermodynamicLimitUniversality
      d β energy amplitude hHermitian hconvDeninger
  exact
    { sourceLimit := hsourceLimit
      sourceUpperAntiHerglotz := hsource
      deningerUpperAntiHerglotz := hdeninger
      oneCauchyGate := hcauchy
      riemannHypothesis := hRH
      wholeCorpusPositivePhase :=
        fun {Lrect} hLrect {N} hN {eta Lsmooth} heta hwindow P hP
            {D} hD {degreeSet} hdegreeSet prime {q} hq =>
          (riemannHypothesis_iff_wholeCorpusPositivePhaseUniversalCertificate
            hLrect hN heta hwindow P hP hD hdegreeSet prime hq).mp hRH
      gaussianHeatContours := fun {τ} hτ {epsilon} hepsilon =>
        deninger_gaussianLefschetz_heatContourUniversality
          hRH hτ hepsilon }

end

end RHTower
