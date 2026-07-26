import GaloisForLFunctions.HTGeometry.FiniteFamilySynchronizedReporterBlindnessUniversalityLaw
import GaloisForLFunctions.HTGeometry.GammaDigammaJetFreeness
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness
import GaloisForLFunctions.RHTower.XiJetFreeness

/-!
# Gamma/digamma/zeta/Xi synchronized reporter blindness

After arbitrary source-dependent finite Gibbs dressings, one coefficient packet is simultaneously
nonzero for Gamma, digamma, Riemann zeta, and completed Xi and invisible to arbitrary
source-specific finite-dimensional reporters.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Four-source index: Gamma, digamma, Riemann zeta, and completed Xi. -/
abbrev GammaDigammaZetaXiSourceIndex := Bool × Bool

/-- Finite-Gibbs-dressed four-source family. -/
def gammaDigammaZetaXiFiniteGibbsDressedSource
    {A : Type*} [Fintype A]
    (energy : GammaDigammaZetaXiSourceIndex → A → ℝ) :
    GammaDigammaZetaXiSourceIndex → ℂ → ℂ
  | (false, false) =>
      Complex.Gamma +
        HTGeometry.finiteComplexGibbsPartition
          (energy (false, false))
  | (false, true) =>
      Complex.digamma +
        HTGeometry.finiteComplexGibbsPartition
          (energy (false, true))
  | (true, false) =>
      riemannZeta +
        HTGeometry.finiteComplexGibbsPartition
          (energy (true, false))
  | (true, true) =>
      xi +
        HTGeometry.finiteComplexGibbsPartition
          (energy (true, true))

/-- Every member of the four-source finite-Gibbs family retains infinite
constant-coefficient differential complexity. -/
theorem gammaDigammaZetaXiFiniteGibbsDressedSource_differentiallyTranscendental
    {A : Type*} [Fintype A]
    (energy : GammaDigammaZetaXiSourceIndex → A → ℝ) :
    ∀ i,
      HTGeometry.ConstantCoefficientDifferentiallyTranscendental
        (gammaDigammaZetaXiFiniteGibbsDressedSource energy i) := by
  rintro ⟨a, b⟩
  cases a <;> cases b
  · exact gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      (energy (false, false))
  · exact digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      (energy (false, true))
  · exact riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      (energy (true, false))
  · exact xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental
      (energy (true, true))

/-- **Gamma/digamma/zeta/Xi synchronized reporter-blindness universality.**

One coefficient vector simultaneously gives a genuine nonzero derivative packet for all four
finite-Gibbs-dressed arithmetic sources and lies in every corresponding reporter kernel. -/
theorem gammaDigammaZetaXi_synchronizedReporterBlindnessUniversality
    {A Y : Type*} [Fintype A]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (energy : GammaDigammaZetaXiSourceIndex → A → ℝ)
    (report :
      GammaDigammaZetaXiSourceIndex → (ℂ → ℂ) →ₗ[ℂ] Y) :
    ∃ c : Fin
        (Module.finrank ℂ (GammaDigammaZetaXiSourceIndex → Y) + 1) → ℂ,
      (∃ j, c j ≠ 0) ∧
      ∀ i,
        HTGeometry.finiteDerivativeReporterPacket c
            (gammaDigammaZetaXiFiniteGibbsDressedSource energy i) ≠ 0 ∧
          report i
            (HTGeometry.finiteDerivativeReporterPacket c
              (gammaDigammaZetaXiFiniteGibbsDressedSource energy i)) = 0 :=
  HTGeometry.exists_common_nonzero_finiteDerivativeReporterPacket_ker
    (gammaDigammaZetaXiFiniteGibbsDressedSource energy)
    (gammaDigammaZetaXiFiniteGibbsDressedSource_differentiallyTranscendental energy)
    report

end

end RHTower
