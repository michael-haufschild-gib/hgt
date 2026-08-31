import Mathlib

/-!
# The thin branch of a density dichotomy

Given a cover "off a set `B` of measure at most `M`, every point lies in `G₁` or `G₂`", suppose `G₂`
occupies at most `ε·2r` of `[t₀, 2r]`.  Then `[r, 2r]`, which has measure `r`, cannot be covered by
`B` together with that part of `G₂` as soon as `ε·2r + M < r`, so it contains a point of `G₁`.

This is the half of the dichotomy that does *not* go through the growth wall: when the branch with
Newton exponent above one has density zero, the other branch is available in every dyadic window,
and monotonicity of the central index spreads the bound it carries to all radii.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal

/-- **The density dichotomy's second branch.**  If off a set `B` of measure at most `M` every point
lies in `G₁` or `G₂`, and `G₂` is thin on `[t₀, 2r]`, then `[r, 2r]` contains a point of `G₁`. -/
theorem exists_mem_of_small_complement {G₁ G₂ B : Set ℝ} {M t₀ eps r : ℝ}
    (hcov : ∀ x, x ∉ B → x ∈ G₁ ∨ x ∈ G₂)
    (hB : volume B ≤ ENNReal.ofReal M) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hG₂ : volume (G₂ ∩ Icc t₀ (2 * r)) ≤ ENNReal.ofReal (eps * (2 * r)))
    (ht₀ : t₀ ≤ r) (hr : 0 < r) (hsmall : eps * (2 * r) + M < r) :
    ∃ x ∈ Icc r (2 * r), x ∈ G₁ := by
  by_contra hcon
  push Not at hcon
  have hsub : Icc r (2 * r) ⊆ B ∪ (G₂ ∩ Icc t₀ (2 * r)) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · rcases hcov x hxB with hg1 | hg2
      · exact absurd hg1 (hcon x hx)
      · exact Or.inr ⟨hg2, ⟨le_trans ht₀ hx.1, hx.2⟩⟩
  have hvol : volume (Icc r (2 * r)) ≤ volume B + volume (G₂ ∩ Icc t₀ (2 * r)) :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have hle : volume (Icc r (2 * r)) ≤ ENNReal.ofReal M + ENNReal.ofReal (eps * (2 * r)) :=
    le_trans hvol (add_le_add hB hG₂)
  rw [Real.volume_Icc, ← ENNReal.ofReal_add hM (by positivity)] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  linarith [hreal, hsmall]

end GaloisForLFunctions.HTGeometry
