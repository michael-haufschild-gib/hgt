import GaloisForLFunctions.RHTower.BurnolSonineMinimality
import GaloisForLFunctions.RHTower.BurnolSonineCompletenessUnit
import GaloisForLFunctions.RHTower.BurnolSonineCompleteness

/-!
# Burnol's Theorem 3.2, the aperture picture inside the Sonine space

The evaluator system `Z^a_{ρ,k}` attached to the nontrivial zeros of `ζ`:

* is **complete** in `K_a` for every `a ≥ 1`;
* stays complete for `a > 1` after omitting arbitrarily finitely many of its members — so it is
  **not minimal** there;
* is **not complete** in `K_a` for `a < 1`;
* is **minimal** in `K_a` for `a < 1`.

All four are recorded below in the jet dictionary; the `a < 1` halves come from the extended-space
statements at a slightly larger aperture through `exists_soninCarrier_of_extended`.

## Main results

* `IsSonineDatum`
* `burnol_theorem_three_two`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A vector of the Sonine space `K_a`, with both aperture constants zero. -/
def IsSonineDatum (a : ℝ) (v : SoninL2) : Prop :=
  v ∈ evenSubspace ∧ v ∈ centralSoninCarrier a ∧
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = 0) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = 0)

/-- **Burnol's Theorem 3.2.**  The aperture threshold of the Sonine evaluator system is again `1`,
and above it the system is not even minimal. -/
theorem burnol_theorem_three_two :
    (∀ a : ℝ, 1 ≤ a → ∀ v : SoninL2, IsSonineDatum a v →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 v) ρ) → v = 0) ∧
    (∀ a : ℝ, 1 < a → ∀ R : Finset ℂ,
      (∀ ρ ∈ R, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) → ∀ v : SoninL2, IsSonineDatum a v →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ ∉ R →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 v) ρ) → v = 0) ∧
    (∀ a : ℝ, 0 < a → a < 1 → ∃ v : SoninL2, v ≠ 0 ∧ IsSonineDatum a v ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 v) ρ) ∧
    (∀ a : ℝ, 0 < a → a < 1 → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → ∀ k : ℕ,
      (k : ℕ∞) < analyticOrderAt riemannZeta ρ →
      ∃ v : SoninL2, v ≠ 0 ∧ IsSonineDatum a v ∧
        (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
          meromorphicOrderAt riemannZeta ρ'
            ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 v) ρ') ∧
        meromorphicOrderAt (extendedMellinContinuation a 0 0 v) ρ = ((k : ℤ) : WithTop ℤ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha v hdat hann
    exact eq_zero_of_zeta_dvd_soninCarrier_one_le ha hdat.1 hdat.2.1 hdat.2.2.1 hdat.2.2.2 hann
  · intro a ha R hR v hdat hann
    exact eq_zero_of_zeta_dvd_off_finite_soninCarrier ha hdat.1 hdat.2.1 hdat.2.2.1 hdat.2.2.2
      hR hann
  · intro a ha ha1
    obtain ⟨V, hVne, hVev, hVK, hVfour, hVphys, hann⟩ := exists_nonzero_soninCarrier_zeta_dvd ha ha1
    exact ⟨V, hVne, ⟨hVev, hVK, hVfour, hVphys⟩, hann⟩
  · intro a ha ha1 ρ h0 h1 k hk
    obtain ⟨V, hVne, hVev, hVK, hVfour, hVphys, hother, hself⟩ :=
      exists_soninCarrier_minimality_witness ha ha1 h0 h1 hk
    exact ⟨V, hVne, ⟨hVev, hVK, hVfour, hVphys⟩, hother, hself⟩

end

end RHTower
