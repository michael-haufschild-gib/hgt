import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.IntermediateValue

/-!
# Cosine and sine Gram pairs of two damped oscillations have different top eigenvalues

Let `δ > 0` and let `t₁ ≠ t₂` be frequencies with `t₁ + t₂ ≠ 0`. For phases `θ₁, θ₂` the Gram
matrices of `e^{−δu} cos(t_j u − θ_j)` and of `e^{−δu} sin(t_j u − θ_j)` on `(0, ∞)` are

`K_± = A ± C`,

with `A` built from the difference frequencies (its off-diagonal entry depends on `θ₁ − θ₂`) and `C`
from the sum frequencies. The diagonal of `C` is `κ_j (δ cos 2θ_j + t_j sin 2θ_j)` and its
off-diagonal entry is `κ (2δ cos(θ₁ + θ₂) + (t₁ + t₂) sin(θ₁ + θ₂))`. Shifting both phases by `π/2`
fixes `A` and negates `C`, so it exchanges `K_+` and `K_−`.

**Theorem** (`exists_topEig_sin_lt_topEig_cos`). For any real diagonal `a₁, a₂`, any difference
term `X(θ₁ − θ₂)`, any `κ` and any `κ₁, κ₂ ≠ 0`, some phases give
`λ_max(K_−) < λ_max(K_+)`. By the `π/2` exchange, other phases give the reverse inequality.

**Proof.** Choose `ψ₀` with `2δ cos ψ₀ + (t₁ + t₂) sin ψ₀ = 0`, so `C` is diagonal on the slice
`θ₁ + θ₂ = ψ₀`. On that slice the two diagonal entries of `C` differ by a function `e(ϑ)`,
`ϑ = θ₁ − θ₂`, with `e(ϑ + π) = −e(ϑ)`, hence a zero `ϑ₀`. There both diagonals equal some `c`, and
`λ_max(A + cI) − λ_max(A − cI) = 2c`. If `c = 0`, both sum-frequency entries vanish at `ψ₀ ± ϑ₀`, and
together with the choice of `ψ₀` this forces `(t₁ − t₂) cos ψ₀ sin ϑ₀ = 0`, then `sin ψ₀ = 0`, then
`δ cos ψ₀ = 0`, contradicting `cos ψ₀ > 0`.

This is the two-top case of the parity comparison for an off-line configuration whose top layer
carries two quartets: `K_+` and `K_−` are the boundary Gram matrices of the even and the odd sector,
and the phases `t_j a` run densely through the torus when `t₁, t₂` are rationally independent.
-/

namespace GaloisForLFunctions.HTGeometry.DampedCosineSineGram

open Real Set

noncomputable section

/-- The largest eigenvalue `(p + q)/2 + √(((p − q)/2)² + r²)` of `[[p, r], [r, q]]`. -/
def topEig (p q r : ℝ) : ℝ := (p + q) / 2 + √(((p - q) / 2) ^ 2 + r ^ 2)

/-- Shifting both diagonal entries by `±c` moves the top eigenvalue by `±c`. -/
theorem topEig_add_sub_topEig_sub (a₁ a₂ c r : ℝ) :
    topEig (a₁ + c) (a₂ + c) r - topEig (a₁ - c) (a₂ - c) r = 2 * c := by
  unfold topEig
  rw [show a₁ + c - (a₂ + c) = a₁ - c - (a₂ - c) by ring]
  ring

/-- The diagonal sum-frequency entry `κ (δ cos 2θ + t sin 2θ)`. -/
def diagEntry (κ δ t θ : ℝ) : ℝ := κ * (δ * cos (2 * θ) + t * sin (2 * θ))

/-- The off-diagonal sum-frequency entry `κ (2δ cos ψ + T sin ψ)`. -/
def crossEntry (κ δ T ψ : ℝ) : ℝ := κ * (2 * δ * cos ψ + T * sin ψ)

theorem diagEntry_add_pi_div_two (κ δ t θ : ℝ) :
    diagEntry κ δ t (θ + π / 2) = -diagEntry κ δ t θ := by
  unfold diagEntry
  rw [show 2 * (θ + π / 2) = 2 * θ + π by ring, cos_add_pi, sin_add_pi]
  ring

theorem diagEntry_sub_pi_div_two (κ δ t θ : ℝ) :
    diagEntry κ δ t (θ - π / 2) = -diagEntry κ δ t θ := by
  unfold diagEntry
  rw [show 2 * (θ - π / 2) = 2 * θ - π by ring, cos_sub_pi, sin_sub_pi]
  ring

theorem crossEntry_add_pi (κ δ T ψ : ℝ) : crossEntry κ δ T (ψ + π) = -crossEntry κ δ T ψ := by
  unfold crossEntry
  rw [cos_add_pi, sin_add_pi]
  ring

/-- A phase `ψ₀` with `cos ψ₀ > 0` on which the off-diagonal sum-frequency entry vanishes. -/
theorem exists_crossEntry_root {δ T : ℝ} (hT : T ≠ 0) :
    ∃ ψ₀ : ℝ, 0 < cos ψ₀ ∧ 2 * δ * cos ψ₀ + T * sin ψ₀ = 0 := by
  refine ⟨arctan (-(2 * δ) / T), cos_arctan_pos _, ?_⟩
  rw [cos_arctan, sin_arctan]
  field_simp
  ring

/-- **No common root.** The two diagonal sum-frequency entries and the off-diagonal one cannot
vanish together on the slice `θ₁ + θ₂ = ψ₀` when `cos ψ₀ > 0`. -/
theorem false_of_three_roots {δ t₁ t₂ ψ ϑ : ℝ} (hδ : 0 < δ) (ht : t₁ ≠ t₂) (hc : 0 < cos ψ)
    (h₀ : 2 * δ * cos ψ + (t₁ + t₂) * sin ψ = 0)
    (h₁ : δ * cos (ψ + ϑ) + t₁ * sin (ψ + ϑ) = 0)
    (h₂ : δ * cos (ψ - ϑ) + t₂ * sin (ψ - ϑ) = 0) : False := by
  rw [cos_add, sin_add] at h₁
  rw [cos_sub, sin_sub] at h₂
  have hsum : (t₁ - t₂) * cos ψ * sin ϑ = 0 := by
    have : cos ϑ * (2 * δ * cos ψ + (t₁ + t₂) * sin ψ) + (t₁ - t₂) * cos ψ * sin ϑ = 0 := by
      linear_combination h₁ + h₂
    rw [h₀, mul_zero, zero_add] at this
    exact this
  have hsq : sin ϑ = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (sub_eq_zero.mp h') ht
      · exact absurd h' hc.ne'
    · exact h
  have hcq : cos ϑ ^ 2 = 1 := by nlinarith [sin_sq_add_cos_sq ϑ]
  have hdiff : (t₁ - t₂) * sin ψ * cos ϑ = 0 := by
    have : -(2 * δ) * sin ψ * sin ϑ + (t₁ - t₂) * sin ψ * cos ϑ +
        (t₁ + t₂) * cos ψ * sin ϑ = 0 := by
      linear_combination h₁ - h₂
    rw [hsq] at this
    linarith
  have hsp : sin ψ = 0 := by
    rcases mul_eq_zero.mp hdiff with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (sub_eq_zero.mp h') ht
      · exact h'
    · rw [h] at hcq
      norm_num at hcq
  rw [hsp, mul_zero, add_zero] at h₀
  have : 0 < 2 * δ * cos ψ := by positivity
  linarith

/-- **The cosine and sine Gram pairs separate.** For `δ > 0`, `t₁ ≠ t₂`, `t₁ + t₂ ≠ 0`,
`κ₁, κ₂ ≠ 0`, any real `κ, a₁, a₂` and any difference term `X`, some phases give a strictly larger
top eigenvalue to the cosine pair `A + C` than to the sine pair `A − C`. -/
theorem exists_topEig_sin_lt_topEig_cos {δ t₁ t₂ κ₁ κ₂ : ℝ} (κ a₁ a₂ : ℝ) (X : ℝ → ℝ)
    (hδ : 0 < δ) (ht : t₁ ≠ t₂) (hT : t₁ + t₂ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0) :
    ∃ θ₁ θ₂ : ℝ,
      topEig (a₁ - diagEntry κ₁ δ t₁ θ₁) (a₂ - diagEntry κ₂ δ t₂ θ₂)
          (X (θ₁ - θ₂) - crossEntry κ δ (t₁ + t₂) (θ₁ + θ₂)) <
        topEig (a₁ + diagEntry κ₁ δ t₁ θ₁) (a₂ + diagEntry κ₂ δ t₂ θ₂)
          (X (θ₁ - θ₂) + crossEntry κ δ (t₁ + t₂) (θ₁ + θ₂)) := by
  obtain ⟨ψ₀, hc, h₀⟩ := exists_crossEntry_root (δ := δ) hT
  set e : ℝ → ℝ := fun ϑ =>
    diagEntry κ₁ δ t₁ ((ψ₀ + ϑ) / 2) - diagEntry κ₂ δ t₂ ((ψ₀ - ϑ) / 2) with he
  have hcont : Continuous e := by
    simp only [he, diagEntry]
    fun_prop
  have hπ : e π = -e 0 := by
    simp only [he]
    rw [show (ψ₀ + π) / 2 = (ψ₀ + 0) / 2 + π / 2 by ring,
      show (ψ₀ - π) / 2 = (ψ₀ - 0) / 2 - π / 2 by ring, diagEntry_add_pi_div_two,
      diagEntry_sub_pi_div_two]
    ring
  obtain ⟨ϑ₀, -, hϑ₀⟩ : ∃ ϑ₀ ∈ uIcc 0 π, e ϑ₀ = 0 := by
    have hmem : (0 : ℝ) ∈ uIcc (e 0) (e π) := by
      rw [hπ, mem_uIcc]
      rcases le_total (e 0) 0 with h | h
      · exact Or.inl ⟨h, by linarith⟩
      · exact Or.inr ⟨by linarith, h⟩
    exact intermediate_value_uIcc hcont.continuousOn hmem
  set θ₁ := (ψ₀ + ϑ₀) / 2
  set θ₂ := (ψ₀ - ϑ₀) / 2
  set c := diagEntry κ₁ δ t₁ θ₁ with hcdef
  have hc₂ : diagEntry κ₂ δ t₂ θ₂ = c := by
    have : c - diagEntry κ₂ δ t₂ θ₂ = 0 := hϑ₀
    linarith
  have hsum : θ₁ + θ₂ = ψ₀ := by simp only [θ₁, θ₂]; ring
  have hY : crossEntry κ δ (t₁ + t₂) ψ₀ = 0 := by
    unfold crossEntry
    rw [h₀, mul_zero]
  rcases lt_trichotomy 0 c with hpos | hzero | hneg
  · refine ⟨θ₁, θ₂, ?_⟩
    rw [hc₂, hsum, hY, sub_zero, add_zero]
    have := topEig_add_sub_topEig_sub a₁ a₂ c (X (θ₁ - θ₂))
    linarith
  · exfalso
    have h₁ : δ * cos (ψ₀ + ϑ₀) + t₁ * sin (ψ₀ + ϑ₀) = 0 := by
      have : κ₁ * (δ * cos (2 * θ₁) + t₁ * sin (2 * θ₁)) = 0 := hzero.symm
      rw [show 2 * θ₁ = ψ₀ + ϑ₀ by simp only [θ₁]; ring] at this
      exact (mul_eq_zero.mp this).resolve_left hκ₁
    have h₂ : δ * cos (ψ₀ - ϑ₀) + t₂ * sin (ψ₀ - ϑ₀) = 0 := by
      have : κ₂ * (δ * cos (2 * θ₂) + t₂ * sin (2 * θ₂)) = 0 := by
        show diagEntry κ₂ δ t₂ θ₂ = 0
        rw [hc₂, ← hzero]
      rw [show 2 * θ₂ = ψ₀ - ϑ₀ by simp only [θ₂]; ring] at this
      exact (mul_eq_zero.mp this).resolve_left hκ₂
    exact false_of_three_roots hδ ht hc h₀ h₁ h₂
  · refine ⟨θ₁ + π / 2, θ₂ + π / 2, ?_⟩
    rw [diagEntry_add_pi_div_two, diagEntry_add_pi_div_two, hc₂,
      show θ₁ + π / 2 - (θ₂ + π / 2) = θ₁ - θ₂ by ring,
      show θ₁ + π / 2 + (θ₂ + π / 2) = ψ₀ + π by rw [← hsum]; ring, crossEntry_add_pi, hY,
      neg_zero, sub_zero, add_zero, sub_neg_eq_add, sub_neg_eq_add, ← sub_eq_add_neg,
      ← sub_eq_add_neg]
    have := topEig_add_sub_topEig_sub a₁ a₂ c (X (θ₁ - θ₂))
    linarith

end

end GaloisForLFunctions.HTGeometry.DampedCosineSineGram
