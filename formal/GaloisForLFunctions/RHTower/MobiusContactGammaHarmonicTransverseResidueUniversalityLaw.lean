import GaloisForLFunctions.HTGeometry.GammaFactorialMovingHarmonicResidue
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma harmonic transverse-residue universality

The finite Möbius contact-charge defect is Gamma's exact reciprocal-factorial microscope scale.
Refining that charge by the harmonic pole parameter reveals the first nonzero direction beyond the
collapsed Riccati first-jet boundary. At each fixed pole the residue is contact charge times
digamma; its canonical pole-depth normalization tends to `-2`; and at every nonzero moving
microscope point the normalized defect tends to `-2/x`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Möbius-contact factorial scale refined by the divergent harmonic pole parameter. -/
def mobiusContactGammaHarmonicMicroscopeScale (n : ℕ) : ℂ :=
  ((-2 - mobiusGammaContactPartialCharge n) / 2) * (harmonic n : ℂ)

/-- Contact-harmonic and intrinsic Gamma harmonic microscope scales coincide exactly. -/
theorem mobiusContactGammaHarmonicMicroscopeScale_eq (n : ℕ) :
    mobiusContactGammaHarmonicMicroscopeScale n =
      GaloisForLFunctions.gammaHarmonicMicroscopeScale n := by
  rw [mobiusContactGammaHarmonicMicroscopeScale,
    GaloisForLFunctions.gammaHarmonicMicroscopeScale,
    GaloisForLFunctions.RHTower.mobiusContactGammaFactorialScale_eq]

/-- At pole `-n`, the exact transverse Riccati residue is the contact defect times the positive
integer digamma value. -/
theorem tendsto_gammaFactorialFirstJetDefect_mobiusContact_poleResidue
    (n : ℕ) :
    Tendsto (fun x : ℂ =>
        x * GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
      (𝓝[≠] 0)
      (𝓝 (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
        Complex.digamma ((n : ℂ) + 1))) := by
  simpa only [GaloisForLFunctions.RHTower.mobiusContactGammaFactorialScale_eq] using
    (GaloisForLFunctions.tendsto_gammaFactorialFirstJetDefect_pole_residue n)

/-- Dividing fixed-pole residues by the contact-harmonic scale leaves the universal nonzero
direction `-2`. -/
theorem tendsto_normalized_gammaFactorialFirstJetDefect_mobiusContact_poleResidue :
    Tendsto (fun n : ℕ =>
      (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
        Complex.digamma ((n : ℂ) + 1)) /
          mobiusContactGammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2)) := by
  simpa only [GaloisForLFunctions.RHTower.mobiusContactGammaFactorialScale_eq,
    mobiusContactGammaHarmonicMicroscopeScale_eq] using
    GaloisForLFunctions.tendsto_normalized_gammaFactorialFirstJetDefect_pole_residue

/-- At every nonzero moving microscope point, the contact-harmonic-normalized Riccati defect tends
to the universal reciprocal direction `-2/x`. -/
theorem tendsto_gammaFactorialFirstJetDefect_div_mobiusContactHarmonicScale
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
        mobiusContactGammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2 / x)) := by
  simpa only [mobiusContactGammaHarmonicMicroscopeScale_eq] using
    (GaloisForLFunctions.tendsto_gammaFactorialFirstJetDefect_div_harmonicScale hx)

/-- **Möbius-contact Gamma harmonic transverse-residue universality law.** The same arithmetic
contact defect controls exact local pole residue, canonical global pole-depth normalization, and
the full nonzero moving-microscope transverse profile. -/
theorem mobiusContactGammaHarmonic_completeTransverseResidueUniversality :
    (∀ n : ℕ,
      Tendsto (fun x : ℂ =>
          x * GaloisForLFunctions.gammaFactorialFirstJetDefect n x)
        (𝓝[≠] 0)
        (𝓝 (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
          Complex.digamma ((n : ℂ) + 1)))) ∧
    Tendsto (fun n : ℕ =>
      (-2 * ((-2 - mobiusGammaContactPartialCharge n) / 2) *
        Complex.digamma ((n : ℂ) + 1)) /
          mobiusContactGammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2)) ∧
    ∀ x : ℂ, x ≠ 0 →
      Tendsto (fun n : ℕ =>
        GaloisForLFunctions.gammaFactorialFirstJetDefect n x /
          mobiusContactGammaHarmonicMicroscopeScale n)
        atTop (𝓝 (-2 / x)) := by
  exact ⟨tendsto_gammaFactorialFirstJetDefect_mobiusContact_poleResidue,
    tendsto_normalized_gammaFactorialFirstJetDefect_mobiusContact_poleResidue,
    fun x hx =>
      tendsto_gammaFactorialFirstJetDefect_div_mobiusContactHarmonicScale hx⟩

end

end GaloisForLFunctions.RHTower
