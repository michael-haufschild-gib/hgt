import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# Passive-response value producers for the prime--archimedean anti-Herglotz gate

This file directly connects finite Kubo/Lehmann response values to the existing source-side
anti-Herglotz criterion for RH.  A fixed nonnegative spectral representation supplies the sign
immediately.  More physically, a pointwise thermodynamic limit of canonical finite KMS/Wightman
responses retains the closed upper-half-plane sign even while its finite Hilbert-space dimensions
grow.

The remaining input is a source-value comparison or convergence theorem, not a positivity or
passivity hypothesis.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A source-value representation by one finite passive response supplies the anti-Herglotz gate. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  rw [hvalue z hzpos hzhalf hzeta]
  exact HTGeometry.finitePassiveResponse_im_nonpos
    intensity frequency hintensity hzpos

/-- The same passive source representation directly supplies the one-Cauchy divided-difference
gate used by the Weil and Hedenmalm consumers. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mpr
    (continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
      intensity frequency hintensity hvalue)

/-- A finite passive-response realization of the continued source proves RH. -/
theorem riemannHypothesis_of_finitePassiveResponse
    {α : Type*} [Fintype α]
    (intensity frequency : α → ℝ)
    (hintensity : ∀ a, 0 ≤ intensity a)
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finitePassiveResponse intensity frequency z) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finitePassiveResponse
      intensity frequency hintensity hvalue)

/-- Pointwise convergence of canonical finite KMS responses transfers passivity to the continued
prime--archimedean source.  The finite Hilbert-space dimension may grow with `N`. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hlim := hconv z hzpos hzhalf hzeta
  have himlim : Tendsto
      (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
        (HTGeometry.finiteKMSWightmanTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z).im)
      atTop (nhds (continuedPrimeArchSourceRelativeTrace z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  exact isClosed_Iic.mem_of_tendsto himlim
    (Filter.Eventually.of_forall fun N ↦
      HTGeometry.finiteKMSWightmanTransitionPassiveResponse_im_nonpos
        (β N) (energy N) (amplitude N) hzpos)

/-- Pointwise convergence of energy-weighted KMS fluctuation--dissipation responses transfers the
same anti-Herglotz sign to the continued prime--archimedean source.  The FDT sign law discharges the
nonnegative-intensity hypothesis from `β N ≥ 0`. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSDissipativeResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hβ : ∀ N, 0 ≤ β N)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSDissipativeTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hlim := hconv z hzpos hzhalf hzeta
  have himlim : Tendsto
      (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
        (HTGeometry.finiteKMSDissipativeTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z).im)
      atTop (nhds (continuedPrimeArchSourceRelativeTrace z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  exact isClosed_Iic.mem_of_tendsto himlim
    (Filter.Eventually.of_forall fun N ↦
      HTGeometry.finiteKMSDissipativeTransitionPassiveResponse_im_nonpos
        (β N) (energy N) (amplitude N) (hβ N) hzpos)

/-- The pointwise thermodynamic KMS limit also supplies the source one-Cauchy gate. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mpr
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
      d β energy amplitude hconv)

/-- **Thermodynamic passive-response RH capstone.**  Canonical KMS positivity is structural; the
only remaining input is pointwise convergence of the source-defined responses to the continued
prime--archimedean trace on its natural upper-half-strip domain. -/
theorem riemannHypothesis_of_finiteKMSWightmanResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSWightmanResponse_tendsto
      d β energy amplitude hconv)

/-- **Fluctuation--dissipation RH capstone.**  If source-defined finite KMS dissipative responses
converge pointwise to the continued prime--archimedean relative trace, their structural passivity
proves RH.  The convergence statement remains the source-facing obligation. -/
theorem riemannHypothesis_of_finiteKMSDissipativeResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hβ : ∀ N, 0 ≤ β N)
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSDissipativeTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSDissipativeResponse_tendsto
      d β energy amplitude hβ hconv)

end

end RHTower
