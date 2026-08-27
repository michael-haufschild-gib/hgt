import GaloisForLFunctions.RHTower.FZZCigarPunctureDilationCompletenessEndpoint
import GaloisForLFunctions.RHTower.FinitePrimeCommutingDilationNoPointSpectrum
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# Standard-L² no-go for FZZ puncture dilation completeness

The FZZ puncture endpoint calls a critical-line divisor zero a real-energy horizon-dilation mode.
This file tests the strongest literal Hilbert-space interpretation: a nonzero point eigenvector of
the standard self-adjoint dilation generator on scalar `L²(ℝ)`.

That interpretation is unconditionally impossible. The standard generator has empty point
spectrum, whereas a nontrivial Riemann-zeta zero exists unconditionally. Hence completeness by
ordinary `L²` dilation eigenmodes is false, even though the divisor-only endpoint remains exactly
RH-strength.

The positive survivor is sharp: any viable FZZ puncture occurrence theorem must use generalized
eigenstates or resonances, a singular boundary/domain extension, or a genuinely different
interacting operator. Ordinary normalizable point modes of the standard dilation generator are
not available.

`[NEW] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Literal normalizable FZZ puncture mode for the standard horizon-dilation generator. -/
def fzzPunctureL2DilationEigenmode (E : ℝ) : Prop :=
  ∃ f : dilationGenerator.domain,
    (f : FinitePrimeDilationL2) ≠ 0 ∧
      dilationGenerator f = (E : ℂ) • (f : FinitePrimeDilationL2)

/-- Standard horizon dilation admits no nonzero normalizable point mode at any real energy. -/
theorem not_fzzPunctureL2DilationEigenmode (E : ℝ) :
    ¬ fzzPunctureL2DilationEigenmode E := by
  rintro ⟨f, hf, heig⟩
  exact hf (finitePrimeCommutingDilationHamiltonian_has_no_eigenvector
    ∅ (fun _ => 0) (E : ℂ) f heig)

/-- The exact operator-theoretic boundary: standard dilation is self-adjoint but has no point
spectrum. -/
theorem fzzPunctureStandardDilation_selfAdjoint_and_no_pointSpectrum :
    IsSelfAdjoint dilationGenerator ∧
      ∀ (E : ℝ) (f : dilationGenerator.domain),
        dilationGenerator f = (E : ℂ) • (f : FinitePrimeDilationL2) →
          (f : FinitePrimeDilationL2) = 0 := by
  refine ⟨dilationGenerator_isSelfAdjoint, ?_⟩
  intro E f heig
  exact finitePrimeCommutingDilationHamiltonian_has_no_eigenvector
    ∅ (fun _ => 0) (E : ℂ) f heig

/-- Literal point-spectrum strengthening of the divisor-only FZZ completeness endpoint. -/
def FZZPunctureL2DilationComplete : Prop :=
  ∀ ρ : ℂ,
    fzzCigarContinuumMellinDivisor ρ = 0 →
    (¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) →
    ∃ E : ℝ,
      ρ = fzzPunctureHorizonDilationSpectralParameter E ∧
        fzzPunctureL2DilationEigenmode E

/-- Ordinary normalizable dilation modes cannot complete the FZZ puncture divisor. -/
theorem not_FZZPunctureL2DilationComplete :
    ¬ FZZPunctureL2DilationComplete := by
  intro hcomplete
  obtain ⟨ρ, hre0, _, hz⟩ := exists_riemannZeta_zero_mem_openStrip
  have hnontriv : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num [Complex.mul_re] at hre
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨E, _, hmode⟩ := hcomplete ρ hz hnontriv
  exact not_fzzPunctureL2DilationEigenmode E hmode

end

end RHTower
