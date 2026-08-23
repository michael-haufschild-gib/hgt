import GaloisForLFunctions.RHTower.SoninCarrierFromExtended
import GaloisForLFunctions.RHTower.BurnolMinimalityAperture
import GaloisForLFunctions.RHTower.BurnolCoPoissonNotComplete
import GaloisForLFunctions.RHTower.BurnolTheoremSevenOne

/-!
# The evaluator system inside the Sonine space below aperture one

Burnol's Theorem 6.7: for `a < 1` the evaluators `Z^a_{ρ,k}` attached to the nontrivial zeros are
minimal in `K_a`.  Together with the co-Poisson vectors they are also not complete there.

Both follow from the corresponding statements in the *extended* space at a slightly larger aperture
`a < a' < 1`, transported by `exists_soninCarrier_of_extended`: two dilation shifts turn a vector of
`L_{a'}` into a vector of `K_a` with the very same Mellin jets on the open critical strip.

## Main results

* `exists_soninCarrier_minimality_witness` — **Theorem 6.7**
* `exists_nonzero_soninCarrier_zeta_dvd` — the `K_a` half of Proposition 6.4 for `a < 1`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem ne_zero_of_order_ne_top {a : ℝ} (ha : 0 < a) {V : SoninL2} {c d : ℂ}
    (hev : V ∈ evenSubspace)
    (hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (V : ℝ → ℂ) t = d)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hfin : meromorphicOrderAt (extendedMellinContinuation a c d V) ρ ≠ ⊤) : V ≠ 0 := by
  intro h0
  exact hfin (meromorphicOrderAt_eq_top_of_eq_zero ha hev hc hd h0 hρ0 hρ1)

/-- **Burnol's Theorem 6.7.**  Below aperture one the evaluators are minimal in the Sonine
space: for every nontrivial zero `ρ` and every jet index `k < m_ρ` there is a vector of `K_a`
orthogonal to all the other evaluators and not to `Z^a_{ρ,k}`. -/
theorem exists_soninCarrier_minimality_witness {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {k : ℕ}
    (hk : (k : ℕ∞) < analyticOrderAt riemannZeta ρ) :
    ∃ V : SoninL2, V ≠ 0 ∧ V ∈ evenSubspace ∧ V ∈ centralSoninCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (V : ℝ → ℂ) t = 0) ∧
      (∀ ρ' : ℂ, 0 < ρ'.re → ρ'.re < 1 → ρ' ≠ ρ →
        meromorphicOrderAt riemannZeta ρ'
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 V) ρ') ∧
      meromorphicOrderAt (extendedMellinContinuation a 0 0 V) ρ = ((k : ℤ) : WithTop ℤ) := by
  set a' : ℝ := (a + 1) / 2 with ha'def
  have ha'0 : 0 < a' := by rw [ha'def]; linarith
  have haa' : a < a' := by rw [ha'def]; linarith
  have ha'1 : a' ≤ 1 := by rw [ha'def]; linarith
  obtain ⟨v, c, d, hev, hmem, hc, hd, hother, hself⟩ :=
    exists_minimality_witness_aperture ha'0 ha'1 h0 h1 hk
  obtain ⟨V, hVev, hVK, hVfour, hVphys, hordeq⟩ :=
    exists_soninCarrier_of_extended ha'0 ha haa' hev hmem hc hd
  have hordρ : meromorphicOrderAt (extendedMellinContinuation a 0 0 V) ρ
      = ((k : ℤ) : WithTop ℤ) := by
    rw [hordeq ρ h0 h1, hself]
  have hVne : V ≠ 0 := by
    refine ne_zero_of_order_ne_top ha hVev hVfour hVphys h0 h1 ?_
    rw [hordρ]
    exact WithTop.coe_ne_top
  refine ⟨V, hVne, hVev, hVK, hVfour, hVphys, ?_, hordρ⟩
  intro ρ' hρ'0 hρ'1 hne
  rw [hordeq ρ' hρ'0 hρ'1]
  exact hother ρ' hρ'0 hρ'1 hne

/-- **The `K_a` half of Proposition 6.4 for `a < 1`.**  Below aperture one the evaluators are not
complete in the Sonine space either. -/
theorem exists_nonzero_soninCarrier_zeta_dvd {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ V : SoninL2, V ≠ 0 ∧ V ∈ evenSubspace ∧ V ∈ centralSoninCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary V : SoninL2) : ℝ → ℂ) x = 0) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (V : ℝ → ℂ) t = 0) ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        meromorphicOrderAt riemannZeta ρ
          ≤ meromorphicOrderAt (extendedMellinContinuation a 0 0 V) ρ := by
  set a' : ℝ := (a + 1) / 2 with ha'def
  have ha'0 : 0 < a' := by rw [ha'def]; linarith
  have haa' : a < a' := by rw [ha'def]; linarith
  have ha'1 : a' < 1 := by rw [ha'def]; linarith
  obtain ⟨v, c, d, hvne, hev, hmem, hc, hd, hann⟩ :=
    exists_nonzero_zeta_dvd_of_aperture_lt_one ha'0 ha'1
  obtain ⟨V, hVev, hVK, hVfour, hVphys, hordeq⟩ :=
    exists_soninCarrier_of_extended ha'0 ha haa' hev hmem hc hd
  have hVne : V ≠ 0 := by
    have hz1 : (0 : ℝ) < (((3 / 4 : ℝ) : ℂ)).re := by simp
    have hz2 : (((3 / 4 : ℝ) : ℂ)).re < 1 := by simp; norm_num
    refine ne_zero_of_order_ne_top ha hVev hVfour hVphys hz1 hz2 ?_
    rw [hordeq ((3 / 4 : ℝ) : ℂ) hz1 hz2]
    exact meromorphicOrderAt_extendedMellin_ne_top ha'0 hev hc hd hvne hz1 hz2
  refine ⟨V, hVne, hVev, hVK, hVfour, hVphys, ?_⟩
  intro ρ hζ hρ0 hρ1
  rw [hordeq ρ hρ0 hρ1]
  exact hann ρ hζ hρ0 hρ1

end

end RHTower
