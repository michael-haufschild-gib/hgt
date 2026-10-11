import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Danskin's bound for a perturbed maximum

Let `X` be a compact set, `q` and `b₀` continuous on `X`, `m₀` an upper bound of `q` on `X`, and `β`
an upper bound of `b₀` on the set where `q = m₀`.

**Theorem** (`exists_perturbed_max_le`). For every `ε > 0` there is `κ > 0` such that for all
`0 < δ < κ` and every function `b` uniformly `ε/2`-close to `b₀` on `X`,

`q x + δ b x ≤ m₀ + δ (β + ε)` on `X`.

This is the upper half of Danskin's theorem. The right derivative at `0` of `δ ↦ max_X (q + δ b_δ)`
is at most `max_{argmax q} b₀`; the lower half is immediate from evaluation at a maximizer.

**Proof.** The set `K = {x ∈ X : b₀ x ≥ β + ε/2}` is compact and misses the maximum set of `q`, so
`q ≤ m₀ − g` on `K` for some `g > 0`. On `K` the gap `g` absorbs `δ b` for small `δ`. Off `K` the
closeness gives `b < β + ε`.
-/

namespace GaloisForLFunctions.HTGeometry.Danskin

open Set

/-- **Danskin's upper bound.** -/
theorem exists_perturbed_max_le {α : Type*} [TopologicalSpace α] [T2Space α] {X : Set α}
    (hX : IsCompact X) {q b₀ : α → ℝ} (hq : ContinuousOn q X) (hb : ContinuousOn b₀ X)
    {m₀ β ε : ℝ} (hε : 0 < ε) (hmax : ∀ x ∈ X, q x ≤ m₀)
    (hβ : ∀ x ∈ X, q x = m₀ → b₀ x ≤ β) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → δ < κ → ∀ b : α → ℝ, (∀ x ∈ X, |b x - b₀ x| ≤ ε / 2) →
      ∀ x ∈ X, q x + δ * b x ≤ m₀ + δ * (β + ε) := by
  set K : Set α := X ∩ b₀ ⁻¹' Ici (β + ε / 2) with hK
  have hKc : IsCompact K :=
    hX.of_isClosed_subset (hb.preimage_isClosed_of_isClosed hX.isClosed isClosed_Ici)
      inter_subset_left
  -- off `K` the perturbation is below `β + ε`
  have hoff : ∀ δ : ℝ, 0 < δ → ∀ b : α → ℝ, (∀ x ∈ X, |b x - b₀ x| ≤ ε / 2) →
      ∀ x ∈ X, x ∉ K → q x + δ * b x ≤ m₀ + δ * (β + ε) := by
    intro δ hδ b hb x hx hxK
    have h1 : b₀ x < β + ε / 2 := by
      by_contra h
      exact hxK ⟨hx, le_of_not_gt h⟩
    have h2 := (abs_le.mp (hb x hx)).2
    have h3 : δ * b x ≤ δ * (β + ε) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    linarith [hmax x hx]
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun δ hδ _ b hb x hx => hoff δ hδ b hb x hx ?_⟩
    rw [hK0]; exact notMem_empty x
  obtain ⟨x₁, hx₁K, hx₁max⟩ := hKc.exists_isMaxOn hKne (hq.mono inter_subset_left)
  have hgap : q x₁ < m₀ := by
    rcases (hmax x₁ hx₁K.1).lt_or_eq with h | h
    · exact h
    · have := hβ x₁ hx₁K.1 h
      have h' : β + ε / 2 ≤ b₀ x₁ := hx₁K.2
      linarith
  obtain ⟨x₂, hx₂X, hx₂max⟩ := hX.exists_isMaxOn ⟨x₁, hx₁K.1⟩ hb
  set B : ℝ := b₀ x₂ with hB
  set g : ℝ := m₀ - q x₁ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set D : ℝ := |B| + |β| + 1 with hD
  have hD0 : 0 < D := by positivity
  refine ⟨g / D, div_pos hg0 hD0, fun δ hδ hδκ b hb x hx => ?_⟩
  by_cases hxK : x ∈ K
  · have hq1 : q x ≤ m₀ - g := by
      have := hx₁max hxK
      simp only [mem_setOf_eq] at this
      rw [hg]; linarith
    have hb1 : b x ≤ B + ε / 2 := by
      have h2 := (abs_le.mp (hb x hx)).2
      have h3 : b₀ x ≤ B := hx₂max hx
      linarith
    have hδD : δ * D < g := by
      rwa [lt_div_iff₀ hD0] at hδκ
    have hBβ : B + ε / 2 - (β + ε) ≤ D := by
      rw [hD]
      have := le_abs_self B
      have := neg_abs_le β
      linarith
    have h4 : δ * (B + ε / 2 - (β + ε)) ≤ δ * D := mul_le_mul_of_nonneg_left hBβ hδ.le
    have h5 : δ * b x ≤ δ * (B + ε / 2) := mul_le_mul_of_nonneg_left hb1 hδ.le
    nlinarith
  · exact hoff δ hδ b hb x hx hxK

end GaloisForLFunctions.HTGeometry.Danskin
