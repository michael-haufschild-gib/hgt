import GaloisForLFunctions.RHTower.ZetaCriticalRowBound

/-!
# Good rows from count control on the grid

Combine `window_structure` (count control on the grid `t + 2jτ₂`, `|j| ≤ 6`, plus `h`-rigidity)
with `norm_critRow_le_of_window`. For every `n` with `|γ_n − t| ≤ τ₁`, the gap `g_n` lies in
`[g₋, g₊]`, where `E = e^{40τ₂/h}` and

* `g₊ = πτ₁E / ((1 − δ)τ₁ℓ/2 − (1 + δ)τ₁²ℓ/τ₂ − 2)` (sparse Lorentz sum);
* `g₋ = 2τ₁ / (E((1 + δ)τ₁ℓ + 1))` (dense count).

**Theorem** (`norm_critRow_le_of_countControl`). If `g₊` is non-resonant, then
`‖Ψ_n‖ ≤ critRowBound`, the good-row bound evaluated at the worst ends `g₋`, `g₊`.
-/

noncomputable section

open Complex Finset

namespace RHTower

/-- The upper gap bound `g₊`. -/
def critGapUpper (τ₁ τ₂ ℓ δ E : ℝ) : ℝ :=
  Real.pi * τ₁ * E / ((1 - δ) * (τ₁ * ℓ / 2) - (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ - 2)

/-- The lower gap bound `g₋`. -/
def critGapLower (τ₁ ℓ δ E : ℝ) : ℝ := 2 * τ₁ / (E * ((1 + δ) * (τ₁ * ℓ) + 1))

/-- The good-row bound at the worst gaps. -/
def critRowBound (θ c τ₂ ℓ δ E gl gu : ℝ) : ℝ :=
  16 / (c ^ 2 * gl * τ₂) + (θ + 2 * c) * (E - 1) * (2 * τ₂ * E / gl + 3) * (τ₂ * E + gu) +
    (2 * τ₂ * E / gl + 3) * ((τ₂ * E + gu) * E) ^ 2 / 4 +
    8 / (c ^ 2 * τ₂ ^ 2) * (3 * ((1 + δ) * (τ₂ * ℓ / 2)))

/-- **Good rows.** -/
theorem norm_critRow_le_of_countControl {t τ₁ τ₂ ℓ δ h θ c : ℝ} {B : Finset ℕ} {n : ℕ}
    (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂1 : τ₂ ≤ 1) (hh : 0 < h) (ht : 13 * τ₂ < t)
    (hδ : 0 ≤ δ) (hℓ : 0 ≤ ℓ)
    (hnum : (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ < (1 - δ) * (τ₁ * ℓ / 2))
    (hC : ∀ j : ℤ, |j| ≤ 6 →
      CountControl τ₁ ℓ δ (t + 2 * j * τ₂) ∧ CountControl τ₂ ℓ δ (t + 2 * j * τ₂))
    (hrig : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * τ₂ → RigidAt h k)
    (hB : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * τ₂ → k ∈ B)
    (hc : 0 < c) (hcθ : c ≤ θ) (hE : Real.exp (40 * τ₂ / h) ≤ 6 / 5)
    (hD5 : 0 < (1 - δ) * (τ₁ * ℓ / 2) - (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ - 2)
    (hgτ : critGapUpper τ₁ τ₂ ℓ δ (Real.exp (40 * τ₂ / h)) ≤ τ₂)
    (hθg : θ * critGapUpper τ₁ τ₂ ℓ δ (Real.exp (40 * τ₂ / h)) / (2 * Real.pi) ≤ 1 / 2)
    (hcg : c * critGapUpper τ₁ τ₂ ℓ δ (Real.exp (40 * τ₂ / h)) / (2 * Real.pi) ≤ 1 / 2)
    (hn : |xiOrderedPositiveOrdinate n - t| ≤ τ₁) :
    ‖critRow θ c B n‖ ≤ critRowBound θ c τ₂ ℓ δ (Real.exp (40 * τ₂ / h))
      (critGapLower τ₁ ℓ δ (Real.exp (40 * τ₂ / h)))
      (critGapUpper τ₁ τ₂ ℓ δ (Real.exp (40 * τ₂ / h))) := by
  set E := Real.exp (40 * τ₂ / h) with hEdef
  set γ := xiOrderedPositiveOrdinate with hγ
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hE0 : 0 < E := by linarith
  have hθ : 0 < θ := hc.trans_le hcθ
  obtain ⟨-, hratio, ⟨a, b, -, ha1, ha2, hb1, hb2⟩, hup, hlo⟩ :=
    window_structure hτ₁ hτ₁₂ hτ₂1 hh ht hnum hC hrig
  have hnw : |γ n - t| ≤ 8 * τ₂ := hn.trans (by linarith)
  set g := ordinateGap n with hgdef
  have hg : 0 < g := by
    have := (hrig n hnw).1
    simp only [hgdef, ordinateGap]; linarith
  set D5 := (1 - δ) * (τ₁ * ℓ / 2) - (1 + δ) * τ₁ ^ 2 * ℓ / τ₂ - 2 with hD5def
  have hgup : g ≤ critGapUpper τ₁ τ₂ ℓ δ E := by
    have h1 := hup n hnw
    unfold critGapUpper
    rw [← hD5def, le_div_iff₀ hD5]
    rw [le_div_iff₀ hg] at h1
    linarith
  set Q := (1 + δ) * (τ₁ * ℓ) + 1 with hQ
  have hQ0 : 0 < Q := by positivity
  have hglo : critGapLower τ₁ ℓ δ E ≤ g := by
    have h1 := hlo n hnw
    unfold critGapLower
    rw [← hQ, div_le_iff₀ (by positivity)]
    have h2 : 2 * τ₁ / (g * E) ≤ Q := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have hglo0 : 0 < critGapLower τ₁ ℓ δ E := by unfold critGapLower; positivity
  have hB' : Finset.Icc a b ⊆ B := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    apply hB
    have h1 := xiOrderedPositiveOrdinate_monotone hk.1
    have h2 := xiOrderedPositiveOrdinate_monotone hk.2
    rw [abs_le]; constructor <;> linarith
  have hΛ : narrowMass τ₂ t ≤ (1 + δ) * (τ₂ * ℓ / 2) := by
    have := (hC 0 (by norm_num)).2.2
    simpa using this
  have hrow := norm_critRow_le_of_window (B := B) hτ₁ hτ₁₂ hτ₂1 hc hcθ (by positivity) hE
    hratio ha1 ha2 hb1 hb2 hB' hn hg (hgup.trans hgτ)
    ((by gcongr : θ * g / (2 * Real.pi) ≤ θ * critGapUpper τ₁ τ₂ ℓ δ E / (2 * Real.pi)).trans hθg)
    ((by gcongr : c * g / (2 * Real.pi) ≤ c * critGapUpper τ₁ τ₂ ℓ δ E / (2 * Real.pi)).trans hcg)
    hΛ
  refine hrow.trans ?_
  unfold critRowBound
  have hE1' : 0 ≤ E - 1 := by linarith
  gcongr

end RHTower
