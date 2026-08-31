import GaloisForLFunctions.HTGeometry.DensityDichotomy

/-!
# Closing the coverage gap of the density dichotomy

The wall branch handles an exceptional set of density below one half, and the thin branch as first
stated handled `G₂` of density below one half — leaving the two thresholds meeting exactly at `1/2`
and covering nothing in between with certainty.

Widening the window from `[r, 2r]` to `[r, K r]` removes the gap: the thin branch then tolerates any
density below `1 − 1/K`, so as `K` grows it covers every density below one, while the wall covers
everything above one half.  Since the spread bound only degrades by the factor `K`, which is a
constant, the conclusion `ν(r) = O(r)` is unaffected.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

/-- **The thin branch at an arbitrary dilation.**  Widening the window from `[r, 2r]` to `[r, K r]`
lets the thin branch tolerate any density below `1 − 1/K`, hence — as `K` grows — any density below
one. -/
theorem exists_mem_of_small_complement_dilate {G₁ G₂ B : Set ℝ} {M t₀ eps r K : ℝ}
    (hcov : ∀ x, x ∉ B → x ∈ G₁ ∨ x ∈ G₂)
    (hB : volume B ≤ ENNReal.ofReal M) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hG₂ : volume (G₂ ∩ Icc t₀ (K * r)) ≤ ENNReal.ofReal (eps * (K * r)))
    (ht₀ : t₀ ≤ r) (hr : 0 < r) (hK : 1 < K)
    (hsmall : eps * (K * r) + M < (K - 1) * r) :
    ∃ x ∈ Icc r (K * r), x ∈ G₁ := by
  by_contra hcon
  push Not at hcon
  have hKr : r ≤ K * r := by nlinarith [hr, hK]
  have hsub : Icc r (K * r) ⊆ B ∪ (G₂ ∩ Icc t₀ (K * r)) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · rcases hcov x hxB with hg1 | hg2
      · exact absurd hg1 (hcon x hx)
      · exact Or.inr ⟨hg2, ⟨le_trans ht₀ hx.1, hx.2⟩⟩
  have hvol : volume (Icc r (K * r)) ≤ volume B + volume (G₂ ∩ Icc t₀ (K * r)) :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have hle : volume (Icc r (K * r)) ≤ ENNReal.ofReal M + ENNReal.ofReal (eps * (K * r)) :=
    le_trans hvol (add_le_add hB hG₂)
  rw [Real.volume_Icc, ← ENNReal.ofReal_add hM (by positivity)] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hexp : K * r - r = (K - 1) * r := by ring
  rw [hexp] at hreal
  linarith [hreal, hsmall]

end GaloisForLFunctions.HTGeometry
