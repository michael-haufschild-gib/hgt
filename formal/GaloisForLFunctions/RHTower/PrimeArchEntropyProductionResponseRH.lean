import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityHolonomy
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# Entropy-production response values for the prime--archimedean gate

The finite KMS dissipative bridge requires nonnegative inverse temperature in order to make its
energy-weighted intensity nonnegative. The thermodynamic entropy-production intensity absorbs the
factor of inverse temperature and is nonnegative at every temperature. Consequently, a source
representation or pointwise thermodynamic limit by these canonical entropy-production responses
supplies the existing anti-Herglotz and one-Cauchy RH gates without a `β ≥ 0` hypothesis.

The source-facing value comparison remains explicit. No physical positivity assumption is used as
a substitute for identifying the prime--archimedean source.
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- One finite Hermitian KMS entropy-production representation supplies the anti-Herglotz gate at
arbitrary inverse temperature. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (hvalue : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        continuedPrimeArchSourceRelativeTrace z =
          HTGeometry.finiteTransitionPassiveResponse
            (finiteKMSEntropyProductionTransitionIntensity β energy amplitude)
            energy z) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  rw [hvalue z hzpos hzhalf hzeta]
  exact HTGeometry.finiteTransitionPassiveResponse_im_nonpos _ energy
    (finiteKMSEntropyProductionTransitionIntensity_nonneg
      β energy amplitude hHermitian) hzpos

/-- Pointwise limits of finite Hermitian KMS entropy-production responses retain the closed
anti-Herglotz sign. The dimensions and inverse temperatures may vary freely. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b))
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hlim := hconv z hzpos hzhalf hzeta
  have himlim : Tendsto
      (fun N ↦ (HTGeometry.finiteTransitionPassiveResponse
        (finiteKMSEntropyProductionTransitionIntensity
          (β N) (energy N) (amplitude N)) (energy N) z).im)
      atTop (nhds (continuedPrimeArchSourceRelativeTrace z).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  exact isClosed_Iic.mem_of_tendsto himlim
    (Filter.Eventually.of_forall fun N ↦
      HTGeometry.finiteTransitionPassiveResponse_im_nonpos _ (energy N)
        (finiteKMSEntropyProductionTransitionIntensity_nonneg
          (β N) (energy N) (amplitude N) (hHermitian N))
        hzpos)

/-- The same thermodynamic limit supplies the one-Cauchy divided-difference gate. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finiteKMSEntropyProductionResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b))
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mpr
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse_tendsto
      d β energy amplitude hHermitian hconv)

/-- **Entropy-production response RH capstone.** If source-defined finite Hermitian KMS
entropy-production responses converge pointwise to the continued prime--archimedean relative
trace, their structural nonnegativity proves RH without any temperature-sign hypothesis. -/
theorem riemannHypothesis_of_finiteKMSEntropyProductionResponse_tendsto
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b))
    (hconv : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse_tendsto
      d β energy amplitude hHermitian hconv)

end

end RHTower
