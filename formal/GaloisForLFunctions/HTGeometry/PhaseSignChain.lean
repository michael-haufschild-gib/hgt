import Mathlib

/-!
# Sign chains from a phase increase

Levinson's counting step is: a continuous polar phase that advances by `nπ` along a segment forces
`n` sign changes of the real part.  The clean form needs no complex numbers — only that the real
part is `ρ·cos φ` with `ρ > 0`.

The chain is built from **first hitting times** of the levels `(m₀+i)π`, which are strictly
increasing because the phase takes a different value at each of them, and `cos` alternates in sign
between consecutive integer multiples of `π` while never vanishing there.  No monotonicity of the
phase is assumed.
-/

open Set


noncomputable section

namespace RHTower

/-- The first time in `[a, b]` at which a continuous phase reaches the level `c`. -/
def firstHit (φ : ℝ → ℝ) (a b c : ℝ) : ℝ := sInf (Icc a b ∩ φ ⁻¹' Ici c)

variable {a b : ℝ} {φ : ℝ → ℝ}

theorem firstHit_mem (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    {c : ℝ} (hhigh : c ≤ φ b) :
    firstHit φ a b c ∈ Icc a b ∩ φ ⁻¹' Ici c := by
  set S : Set ℝ := Icc a b ∩ φ ⁻¹' Ici c with hS
  have hbmem : b ∈ S := ⟨⟨hab, le_rfl⟩, hhigh⟩
  have hne : S.Nonempty := ⟨b, hbmem⟩
  have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hclosed : IsClosed S :=
    hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  exact hclosed.csInf_mem hne hbdd

theorem firstHit_phase (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    {c : ℝ} (hlow : φ a ≤ c) (hhigh : c ≤ φ b) :
    φ (firstHit φ a b c) = c := by
  set S : Set ℝ := Icc a b ∩ φ ⁻¹' Ici c with hS
  have hmem := firstHit_mem hab hφ hhigh
  set x := firstHit φ a b c with hx
  have hbdd : BddBelow S := ⟨a, fun y hy => hy.1.1⟩
  refine le_antisymm ?_ hmem.2
  by_contra hcon
  rw [not_le] at hcon
  have hxa : a < x := by
    rcases eq_or_lt_of_le hmem.1.1 with h | h
    · exfalso; rw [← h] at hcon; linarith
    · exact h
  have hcontx : ContinuousWithinAt φ (Icc a b) x := hφ x hmem.1
  rw [Metric.continuousWithinAt_iff] at hcontx
  obtain ⟨δ, hδ, hball⟩ := hcontx (φ x - c) (by linarith)
  set y := max a (x - δ / 2) with hy
  have hya : a ≤ y := le_max_left _ _
  have hyx : y < x := by
    rcases max_cases a (x - δ / 2) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hy, h1]; exact hxa
    · rw [hy, h1]; linarith
  have hyb : y ≤ b := le_trans hyx.le hmem.1.2
  have hdist : dist y x < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    rcases max_cases a (x - δ / 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hy, h1]; linarith
    · rw [hy, h1]; linarith
  have hφy := hball ⟨hya, hyb⟩ hdist
  rw [Real.dist_eq] at hφy
  have hgt : c < φ y := by
    have := abs_lt.mp hφy
    linarith [this.1]
  have hyS : y ∈ S := ⟨⟨hya, hyb⟩, le_of_lt hgt⟩
  exact absurd (csInf_le hbdd hyS) (not_le.mpr hyx)

theorem firstHit_mono (hab : a ≤ b) {c c' : ℝ} (hcc : c ≤ c')
    (hhigh : c' ≤ φ b) :
    firstHit φ a b c ≤ firstHit φ a b c' := by
  refine csInf_le_csInf ⟨a, fun y hy => hy.1.1⟩ ⟨b, ⟨⟨hab, le_rfl⟩, hhigh⟩⟩ ?_
  intro y hy
  exact ⟨hy.1, le_trans hcc hy.2⟩

/-- **A phase increase of `nπ` forces `n` sign changes of `ρ·cos φ`.**  First-hitting times of the
levels `(m₀+i)π` are strictly increasing, and `cos` alternates in sign between consecutive integer
multiples of `π` while never vanishing there. -/
theorem exists_sign_chain_of_phase_increase {φ ρ : ℝ → ℝ} {m₀ : ℤ} {n : ℕ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) (hρ : ∀ τ ∈ Icc a b, 0 < ρ τ)
    (hlow : φ a ≤ (m₀ : ℝ) * Real.pi)
    (hhigh : ((m₀ : ℝ) + (n : ℝ)) * Real.pi ≤ φ b) :
    ∃ g : ℕ → ℝ, (∀ i ≤ n, g i ∈ Icc a b) ∧ (∀ i < n, g i < g (i + 1)) ∧
      (∀ i < n,
        (ρ (g i) * Real.cos (φ (g i))) * (ρ (g (i + 1)) * Real.cos (φ (g (i + 1)))) < 0) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set c : ℕ → ℝ := fun i => ((m₀ + (i : ℤ) : ℤ) : ℝ) * Real.pi with hc
  have hccast : ∀ i : ℕ, c i = ((m₀ : ℝ) + (i : ℝ)) * Real.pi := by
    intro i; rw [hc]; push_cast; ring
  have hcmono : ∀ i j : ℕ, i ≤ j → c i ≤ c j := by
    intro i j hij
    rw [hccast, hccast]
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith
  have hhigh_i : ∀ i ≤ n, c i ≤ φ b := by
    intro i hi
    refine le_trans (hcmono i n hi) ?_
    rw [hccast]
    exact hhigh
  have hlow_i : ∀ i : ℕ, φ a ≤ c i := by
    intro i
    refine le_trans hlow ?_
    rw [hccast]
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith
  set g : ℕ → ℝ := fun i => firstHit φ a b (c i) with hg
  have hgmem : ∀ i ≤ n, g i ∈ Icc a b := fun i hi =>
    (firstHit_mem hab hφ (hhigh_i i hi)).1
  have hgphase : ∀ i ≤ n, φ (g i) = c i := fun i hi =>
    firstHit_phase hab hφ (hlow_i i) (hhigh_i i hi)
  refine ⟨g, hgmem, ?_, ?_⟩
  · intro i hi
    have hle : g i ≤ g (i + 1) :=
      firstHit_mono hab (hcmono i (i + 1) (by omega)) (hhigh_i (i + 1) (by omega))
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      have h1 : φ (g i) = c i := hgphase i (by omega)
      have h2 : φ (g (i + 1)) = c (i + 1) := hgphase (i + 1) (by omega)
      rw [heq, h2] at h1
      rw [hccast, hccast] at h1
      push_cast at h1
      nlinarith
    · exact hlt
  · intro i hi
    have h1 : φ (g i) = c i := hgphase i (by omega)
    have h2 : φ (g (i + 1)) = c (i + 1) := hgphase (i + 1) (by omega)
    have hstep : c (i + 1) = c i + Real.pi := by
      rw [hccast, hccast]; push_cast; ring
    have hcos : Real.cos (c (i + 1)) = -Real.cos (c i) := by
      rw [hstep, Real.cos_add_pi]
    have hsq : Real.cos (c i) ^ (2 : ℕ) = 1 := by
      have hsin : Real.sin (c i) = 0 := by
        rw [hc]; exact Real.sin_int_mul_pi _
      have := Real.sin_sq_add_cos_sq (c i)
      rw [hsin] at this
      nlinarith
    have hρ1 : 0 < ρ (g i) := hρ _ (hgmem i (by omega))
    have hρ2 : 0 < ρ (g (i + 1)) := hρ _ (hgmem (i + 1) (by omega))
    rw [h1, h2, hcos]
    nlinarith [hsq, hρ1, hρ2, mul_pos hρ1 hρ2]

end RHTower

end
