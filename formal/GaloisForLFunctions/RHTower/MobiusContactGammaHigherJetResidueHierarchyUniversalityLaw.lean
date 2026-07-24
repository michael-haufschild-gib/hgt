import GaloisForLFunctions.HTGeometry.GammaFactorialExponentialEnvelopeEscape
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma higher-jet residue hierarchy universality

The finite Möbius contact defect generates every currently proved higher-jet transverse scale of
the Gamma factorial microscope. Second-jet and projective-curvature residues occur at the
contact-harmonic scale, Schwarzian residue at its square, and logarithmic and
exponential-reciprocal discriminants at squared contact-factorial scale. Their exact reciprocal
profiles are nonzero away from the microscope origin.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Möbius-contact scale used by the higher-jet factorial layer. -/
def mobiusContactGammaHigherJetFactorialScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

/-- Harmonic refinement of the Möbius-contact higher-jet scale. -/
def mobiusContactGammaHigherJetHarmonicScale (n : ℕ) : ℂ :=
  mobiusContactGammaHigherJetFactorialScale n * (harmonic n : ℂ)

theorem mobiusContactGammaHigherJetFactorialScale_eq (n : ℕ) :
    mobiusContactGammaHigherJetFactorialScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactGammaHigherJetFactorialScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

theorem mobiusContactGammaHigherJetHarmonicScale_eq (n : ℕ) :
    mobiusContactGammaHigherJetHarmonicScale n =
      GaloisForLFunctions.gammaHarmonicMicroscopeScale n := by
  rw [mobiusContactGammaHigherJetHarmonicScale,
    mobiusContactGammaHigherJetFactorialScale_eq,
    GaloisForLFunctions.gammaHarmonicMicroscopeScale]

/-- **Möbius-contact Gamma higher-jet residue hierarchy universality law.** At every nonzero
microscope point, the contact defect and its harmonic refinement normalize all proved second- and
third-jet hypersurface escapes to their exact nonzero profiles. -/
theorem mobiusContactGammaHigherJet_completeResidueHierarchyUniversality :
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n)
        atTop (𝓝 (6 / x ^ 2)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialSecondJetProjectiveDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n)
        atTop (𝓝 (2 / x ^ 3)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialThirdJetProjectiveDefect n x /
          mobiusContactGammaHigherJetHarmonicScale n ^ 2)
        atTop (𝓝 (-6 / x ^ 4)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialLogCurvatureDiscriminant n x /
          mobiusContactGammaHigherJetFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4)) ∧
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialExponentialEnvelopeDefect n x /
          mobiusContactGammaHigherJetFactorialScale n ^ 2)
        atTop (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10)) := by
  intro x hx
  exact ⟨by
      simpa only [mobiusContactGammaHigherJetHarmonicScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx),
    by
      simpa only [mobiusContactGammaHigherJetHarmonicScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale hx),
    by
      simpa only [mobiusContactGammaHigherJetHarmonicScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq hx),
    by
      simpa only [mobiusContactGammaHigherJetFactorialScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq hx),
    by
      simpa only [mobiusContactGammaHigherJetFactorialScale_eq] using
        (GaloisForLFunctions.tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq hx)⟩

end

end GaloisForLFunctions.RHTower
