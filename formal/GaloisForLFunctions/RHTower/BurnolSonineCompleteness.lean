import GaloisForLFunctions.RHTower.BurnolCompletenessOmit
import GaloisForLFunctions.RHTower.SoninExtendedApertureChain

/-!
# The same statements inside the Sonine space `K_a`

`K_a ⊆ L_a` (`centralSoninCarrier_le_centralSoninExtendedCarrier`), so the completeness results for
the extended space restrict at once to the Sonine space: for `a > 1` the evaluators attached to the
nontrivial zeros span `K_a`, and they still do after omitting arbitrarily finitely many of them.
This is Burnol's Proposition 6.6 (and the `K_a` half of Proposition 6.1).

## Main results

* `eq_zero_of_zeta_dvd_soninCarrier` — Proposition 6.1 for `K_a`, `a > 1`.
* `eq_zero_of_zeta_dvd_off_finite_soninCarrier` — **Proposition 6.6** for `a > 1`.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Proposition 6.1 inside `K_a`.** -/
theorem eq_zero_of_zeta_dvd_soninCarrier {b : ℝ} (hb : 1 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace) (hg : g ∈ centralSoninCarrier b)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 :=
  eq_zero_of_zeta_dvd_extendedMellin hb hev
    (centralSoninCarrier_le_centralSoninExtendedCarrier b hg) hc hd hdvd

/-- **Burnol's Proposition 6.6 for `a > 1`.**  The evaluators still span `K_a` after omitting
arbitrarily finitely many of them. -/
theorem eq_zero_of_zeta_dvd_off_finite_soninCarrier {b : ℝ} (hb : 1 < b) {g : SoninL2} {c d : ℂ}
    (hev : g ∈ evenSubspace) (hg : g ∈ centralSoninCarrier b)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary g : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (g : ℝ → ℂ) t = d)
    {R : Finset ℂ}
    (hRzero : ∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation b c d g) ρ) :
    g = 0 :=
  eq_zero_of_zeta_dvd_off_finite hb hev
    (centralSoninCarrier_le_centralSoninExtendedCarrier b hg) hc hd hRzero hdvd

end

end RHTower
