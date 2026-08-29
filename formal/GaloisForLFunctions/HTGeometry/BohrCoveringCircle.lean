import GaloisForLFunctions.HTGeometry.ModularDiskChart

/-!
# Bohr's circle-covering theorem

**Bohr (1923), generalising Landau (1922).**  Fix `0 < ρ < 1`.  There is a constant `C(ρ) > 0` with
the following property: if `φ` is holomorphic on the unit disc, `φ 0 = 0`, and `‖φ‖` reaches `1`
somewhere on `‖z‖ ≤ ρ`, then some circle `|w| = t` with `t ≥ C(ρ)` is entirely covered by the values
of `φ`.

The proof is the two-omitted-values argument: if the circles of radius `t` and `t/2` both miss a
value `w₁`, `w₂` of `φ`, then `(φ − w₂)/(w₁ − w₂)` omits `0` and `1` and its value at the origin
lies in the *fixed compact* set

```text
K = {w : 1/3 ≤ ‖w‖ ≤ 1 and ‖w − 1‖ ≥ 2/3} ⊆ ℂ∖{0,1},
```

so `exists_bound_of_omitting_compact_base` bounds it on `‖z‖ ≤ ρ` by a constant `M` depending only
on `ρ`; unwinding gives `‖φ‖ ≤ t(1/2 + 3M/2)` there, which contradicts `‖φ‖ = 1` once `t` is small.

This is the covering theorem behind Pólya's composition-growth inequality
`M(r, g ∘ h) ≥ M(c·M(r/2, h), g)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Complex Metric Set

noncomputable section

/-- The fixed compact base set of the two-omitted-values normalisation. -/
def bohrBase : Set ℂ := {w : ℂ | 1 / 3 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 ∧ 2 / 3 ≤ ‖w - 1‖}

theorem isCompact_bohrBase : IsCompact bohrBase := by
  have hclosed : IsClosed bohrBase := by
    have h1 : IsClosed {w : ℂ | 1 / 3 ≤ ‖w‖} := isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {w : ℂ | ‖w‖ ≤ 1} := isClosed_le continuous_norm continuous_const
    have h3 : IsClosed {w : ℂ | 2 / 3 ≤ ‖w - 1‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have : bohrBase = {w : ℂ | 1 / 3 ≤ ‖w‖} ∩ ({w : ℂ | ‖w‖ ≤ 1} ∩ {w : ℂ | 2 / 3 ≤ ‖w - 1‖}) := by
      ext w; simp [bohrBase]
    rw [this]
    exact h1.inter (h2.inter h3)
  have hbdd : bohrBase ⊆ closedBall (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    exact hw.2.1
  exact (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed hbdd

theorem bohrBase_ne_zero : ∀ v ∈ bohrBase, v ≠ 0 := by
  intro v hv h
  have h1 : (1 : ℝ) / 3 ≤ ‖v‖ := hv.1
  rw [h, norm_zero] at h1
  linarith

theorem bohrBase_ne_one : ∀ v ∈ bohrBase, v ≠ 1 := by
  intro v hv h
  have h3 : (2 : ℝ) / 3 ≤ ‖v - 1‖ := hv.2.2
  rw [h, sub_self, norm_zero] at h3
  linarith

/-- **Bohr's circle-covering theorem.**  A normalised holomorphic disc map covers a whole circle of
radius bounded below by a constant depending only on `ρ`. -/
theorem exists_covered_circle {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball (0 : ℂ) 1) → φ 0 = 0 →
      (∃ z₁ : ℂ, ‖z₁‖ ≤ ρ ∧ 1 ≤ ‖φ z₁‖) →
      ∃ t : ℝ, C ≤ t ∧ ∀ w : ℂ, ‖w‖ = t → ∃ z : ℂ, ‖z‖ < 1 ∧ φ z = w := by
  classical
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'def
  have hρ'0 : 0 ≤ ρ' := by rw [hρ'def]; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ'def]; linarith
  have hρρ' : ρ < ρ' := by rw [hρ'def]; linarith
  obtain ⟨M, hM⟩ :=
    exists_bound_of_omitting_compact_base isCompact_bohrBase bohrBase_ne_zero bohrBase_ne_one
      hρ'0 hρ'1
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMM' : M ≤ M' := le_max_left _ _
  set C₀ : ℝ := 1 / (3 / 2 + (3 / 2) * M') with hC₀def
  have hden : 0 < 3 / 2 + (3 / 2) * M' := by positivity
  have hC₀0 : 0 < C₀ := by rw [hC₀def]; positivity
  refine ⟨C₀ / 2, by positivity, fun φ hφ hφ0 ⟨z₁, hz₁, hz₁val⟩ => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨w₁, hw₁n, hw₁⟩ := hcon C₀ (by linarith)
  obtain ⟨w₂, hw₂n, hw₂⟩ := hcon (C₀ / 2) (le_refl _)
  -- the normalised omitting function
  have hne : w₁ - w₂ ≠ 0 := by
    intro h
    have : w₁ = w₂ := by linear_combination h
    rw [this, hw₂n] at hw₁n
    linarith
  set ψ : ℂ → ℂ := fun z => (φ z - w₂) / (w₁ - w₂) with hψdef
  have hψdiff : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := by
    exact (hφ.sub_const w₂).div_const _
  have hψomit : ∀ z ∈ ball (0 : ℂ) 1, ψ z ≠ 0 ∧ ψ z ≠ 1 := by
    intro z hz
    have hzn : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
    constructor
    · intro h
      rw [hψdef] at h
      have : φ z = w₂ := by
        field_simp at h
        linear_combination h
      exact hw₂ z hzn this
    · intro h
      rw [hψdef] at h
      have : φ z = w₁ := by
        field_simp at h
        linear_combination h
      exact hw₁ z hzn this
  -- the base value lies in the fixed compact set
  have hlow : C₀ / 2 ≤ ‖w₁ - w₂‖ := by
    have := norm_sub_norm_le w₁ w₂
    rw [hw₁n, hw₂n] at this
    linarith
  have hhigh : ‖w₁ - w₂‖ ≤ 3 * C₀ / 2 := by
    have := norm_sub_le w₁ w₂
    rw [hw₁n, hw₂n] at this
    linarith
  have hnormpos : 0 < ‖w₁ - w₂‖ := norm_pos_iff.mpr hne
  have hψ0 : ψ 0 ∈ bohrBase := by
    have hval : ψ 0 = -w₂ / (w₁ - w₂) := by
      simp only [hψdef, hφ0, zero_sub]
    have hn : ‖ψ 0‖ = (C₀ / 2) / ‖w₁ - w₂‖ := by
      rw [hval, norm_div, norm_neg, hw₂n]
    have hn1 : ‖ψ 0 - 1‖ = C₀ / ‖w₁ - w₂‖ := by
      have hsub : ψ 0 - 1 = -w₁ / (w₁ - w₂) := by
        rw [hval]
        field_simp
        ring
      rw [hsub, norm_div, norm_neg, hw₁n]
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, le_div_iff₀ hnormpos]
      linarith
    · rw [hn, div_le_one hnormpos]
      linarith
    · rw [hn1, le_div_iff₀ hnormpos]
      linarith
  -- Schottky bounds the normalised function
  have hz₁ball : z₁ ∈ ball (0 : ℂ) (ρ' * 1) := by
    rw [mem_ball, dist_zero_right, mul_one]
    linarith
  have hbound := hM ψ 0 1 one_pos hψdiff hψomit hψ0 z₁ hz₁ball
  -- unwind
  have hφz₁ : φ z₁ = w₂ + ψ z₁ * (w₁ - w₂) := by
    simp only [hψdef]
    field_simp
    ring
  have hfinal : ‖φ z₁‖ ≤ C₀ * (1 / 2 + (3 / 2) * M') := by
    rw [hφz₁]
    calc ‖w₂ + ψ z₁ * (w₁ - w₂)‖ ≤ ‖w₂‖ + ‖ψ z₁‖ * ‖w₁ - w₂‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul]
      _ ≤ C₀ / 2 + M' * (3 * C₀ / 2) := by
          refine add_le_add (le_of_eq hw₂n) ?_
          refine mul_le_mul (le_trans hbound hMM') hhigh (norm_nonneg _) hM'0
      _ = C₀ * (1 / 2 + (3 / 2) * M') := by ring
  have hlt : C₀ * (1 / 2 + (3 / 2) * M') < 1 := by
    rw [hC₀def, div_mul_eq_mul_div, div_lt_one hden]
    linarith
  linarith [hz₁val, hfinal, hlt]

end

end GaloisForLFunctions.HTGeometry
