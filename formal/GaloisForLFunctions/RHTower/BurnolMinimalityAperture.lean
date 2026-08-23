import GaloisForLFunctions.RHTower.BurnolMinimalitySystem
import GaloisForLFunctions.RHTower.MellinApertureIndependence

/-!
# Minimality below the critical aperture

Burnol's Proposition 6.4, minimality half.  The extended Sonine spaces *decrease* in the aperture,
so the dual vector built at aperture `1` in `BurnolMinimalitySystem` already lives in every `L_a`
with `a ≤ 1`, with the same two band constants and — by `MellinApertureIndependence` — with the
same continued Mellin transform.  Minimality therefore travels all the way down the chain.

Together with `BurnolCoPoissonNotComplete.exists_nonzero_zeta_dvd_of_aperture_lt_one` (the
evaluators are *not* complete for `a < 1`) this is Proposition 6.4.

## Main results

* `exists_minimality_witness_aperture`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Proposition 6.4, minimality half** (and Theorem 6.3's minimality at `a = 1`). -/
theorem exists_minimality_witness_aperture {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {k : ℕ}
    (hk : (k : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    ∃ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace ∧ v ∈ centralSoninExtendedCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) ∧
      (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
        meromorphicOrderAt riemannZeta ρ'
          ≤ meromorphicOrderAt (extendedMellinContinuation a c d v) ρ') ∧
      meromorphicOrderAt (extendedMellinContinuation a c d v) ρ = ((k : ℤ) : WithTop ℤ) := by
  obtain ⟨v, c, d, hev, hmem1, hc1, hd1, hother, hself⟩ := exists_minimality_witness h0 h1 hk
  have hsub : centralInterval a ⊆ centralInterval 1 := by
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    exact ⟨by linarith, by linarith⟩
  have hca : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c := by
    filter_upwards [hc1] with x hx hmem
    exact hx (hsub hmem)
  have hda : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d := by
    filter_upwards [hd1] with t ht hmem
    exact ht (hsub hmem)
  have hmema : v ∈ centralSoninExtendedCarrier a :=
    centralSoninExtendedCarrier_antitone ha1 hmem1
  have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hloc : ∀ z : ℂ, 0 < z.re → z.re < 1 →
      extendedMellinContinuation a c d v =ᶠ[𝓝 z] extendedMellinContinuation 1 c d v := by
    intro z hz0 hz1
    filter_upwards [hstrip.mem_nhds (⟨hz0, hz1⟩ : z ∈ {w : ℂ | 0 < w.re ∧ w.re < 1})] with w hw
    exact extendedMellinContinuation_aperture_eq ha ha1 hev hca hda hc1 hd1 hw.1 hw.2
  refine ⟨v, c, d, hev, hmema, hca, hda, ?_, ?_⟩
  · intro ρ' hρ'0 hρ'1 hρ'ne
    rw [meromorphicOrderAt_congr
      ((hloc ρ' hρ'0 hρ'1).filter_mono nhdsWithin_le_nhds)]
    exact hother ρ' hρ'0 hρ'1 hρ'ne
  · rw [meromorphicOrderAt_congr ((hloc ρ h0 h1).filter_mono nhdsWithin_le_nhds)]
    exact hself

end

end RHTower
