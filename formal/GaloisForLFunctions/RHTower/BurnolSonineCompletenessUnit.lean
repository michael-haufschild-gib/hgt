import GaloisForLFunctions.RHTower.BurnolCompletenessUnit
import GaloisForLFunctions.RHTower.SoninExtendedApertureChain

/-!
# The critical aperture inside the Sonine space

`K_a ⊆ L_a`, so the Krein-free Proposition 6.1 of `BurnolCompletenessUnit` restricts at once to
the Sonine space at **every** aperture `a ≥ 1`, the critical value `a = 1` included.  This is the
completeness half of Burnol's Theorem 6.3 for the systems `Y^1` and `Z^1`.

## Main results

* `eq_zero_of_zeta_dvd_soninCarrier_one_le`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Proposition 6.1 inside `K_b` for every `b ≥ 1`.**  A Sonine vector whose continued Mellin
transform is divisible by `ζ` at every nontrivial zero vanishes. -/
theorem eq_zero_of_zeta_dvd_soninCarrier_one_le {b : ℝ} (hb : 1 ≤ b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace) (hg : g ∈ centralSoninCarrier b)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 := by
  have := centralSoninCarrier_le_centralSoninExtendedCarrier b hg
  exact eq_zero_of_zeta_dvd_extendedMellin_one_le hb hev hc hd hdvd

end

end RHTower
