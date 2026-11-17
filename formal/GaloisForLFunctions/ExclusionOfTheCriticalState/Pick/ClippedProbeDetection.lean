import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ClippedProbeIndex
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCertificates

/-!
# Complete scalar detection of negative probe directions

For a fixed probe combination the confinement mass is nonnegative. The clipped
scalar inequality is violated at some positive cutoff exactly when the confined
Weil energy is negative. Consequently these one-dimensional certificates detect
every failure of positivity of an actual finite probe matrix.
-/

open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry HilbertMetric.Clipped
noncomputable section

/-- No negative direction of the actual finite probe form escapes scalar clipping. -/
theorem probe_direction_clipped_iff {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) (x : Fin N → ℂ) :
    (∃ c : ℝ, 0 < c ∧ (hermQuad (probeGram p) x) ^ 2 <
      quadratic c (hermQuad (probeConfinementBlock R p) x) -
        2 * c * hermQuad (confinedProbeGram R p) x) ↔
      hermQuad (confinedProbeGram R p) x < 0 := by
  have hP : 0 ≤ hermQuad (probeConfinementBlock R p) x :=
    (probeConfinementBlock_posSemidef hR hp).re_dotProduct_nonneg x
  have hsum : confinedProbeGram R p = probeGram p + probeConfinementBlock R p :=
    confinedProbeGram_eq R hp
  have hb : hermQuad (probeGram p) x =
      hermQuad (confinedProbeGram R p) x - hermQuad (probeConfinementBlock R p) x := by
    rw [hsum]
    simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    ring
  rw [hb]
  exact scalar_negative_certificate_iff hP

/-- The scalar certificates are complete for finite probe positivity, not only sufficient. -/
theorem confinedProbeGram_not_posSemidef_iff_clipped {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    ¬ (confinedProbeGram R p).PosSemidef ↔
      ∃ (x : Fin N → ℂ) (c : ℝ), 0 < c ∧ (hermQuad (probeGram p) x) ^ 2 <
        quadratic c (hermQuad (probeConfinementBlock R p) x) -
          2 * c * hermQuad (confinedProbeGram R p) x := by
  have hK := confinedProbeGram_isHermitian hR hp
  constructor
  · intro hn
    have hex : ∃ x : Fin N → ℂ, hermQuad (confinedProbeGram R p) x < 0 := by
      by_contra h
      push_neg at h
      apply hn
      rw [hK.posSemidef_iff_eigenvalues_nonneg]
      intro i
      rw [hK.eigenvalues_eq]
      exact h _
    obtain ⟨x, hx⟩ := hex
    obtain ⟨c, hc, he⟩ := (probe_direction_clipped_iff hR hp x).mpr hx
    exact ⟨x, c, hc, he⟩
  · rintro ⟨x, c, hc, he⟩ hpos
    have hneg := (probe_direction_clipped_iff hR hp x).mp ⟨c, hc, he⟩
    exact (not_lt_of_ge (hpos.re_dotProduct_nonneg x)) hneg

#print axioms probe_direction_clipped_iff
#print axioms confinedProbeGram_not_posSemidef_iff_clipped

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
