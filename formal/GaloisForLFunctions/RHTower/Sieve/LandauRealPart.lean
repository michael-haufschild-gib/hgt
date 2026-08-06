import GaloisForLFunctions.RHTower.Sieve.LandauLemma

/-!
# Landau's lemma in real-part form

The terms `m_ρ/(z - ρ)` retained by Landau's lemma have nonnegative real part at every point to the
right of `ρ`, because

```text
Re (z - ρ)⁻¹ = (Re z - Re ρ) / |z - ρ|².
```

So any subfamily of them may be discarded, and

```text
-Re (f'/f)(z)  ≤  16 log M / R  -  ∑_{ρ ∈ S} m_ρ Re (z - ρ)⁻¹
```

for every `S` contained in the retained zeros.  Taking `S` empty gives the bound with no zero at
all; taking `S` a single zero is the step that produces a zero-free region.
-/

namespace RHTower.Sieve

open Metric Complex

/-- To the right of the pole, the reciprocal has nonnegative real part. -/
theorem re_inv_sub_nonneg {z ρ : ℂ} (hre : ρ.re ≤ z.re) : 0 ≤ ((z - ρ)⁻¹).re := by
  rw [Complex.inv_re, Complex.sub_re]
  have hnn : 0 ≤ Complex.normSq (z - ρ) := Complex.normSq_nonneg _
  have : 0 ≤ z.re - ρ.re := by linarith
  positivity

/-- The real part of a retained Landau term. -/
theorem re_natCast_div (n : ℕ) (w : ℂ) : ((n : ℂ) / w).re = (n : ℝ) * (w⁻¹).re := by
  rw [div_eq_mul_inv]
  simp [Complex.mul_re]

/-- **Landau's lemma, real-part form.**  Any subfamily of the retained zeros may be kept; the rest
is discarded at no cost. -/
theorem neg_re_logDeriv_le {f : ℂ → ℂ} {c : ℂ} {R R₀ M : ℝ}
    (hR : 0 < R) (hRR₀ : R < R₀) (hM : 1 < M)
    (hf : AnalyticOnNhd ℂ f (ball c R₀)) (hfc : f c ≠ 0)
    (hbound : ∀ w ∈ ball c R₀, ‖f w‖ ≤ M * ‖f c‖) :
    ∃ (Z₁ : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z₁, ‖ρ - c‖ ≤ R / 2) ∧ (∀ ρ ∈ Z₁, f ρ = 0) ∧
      (∀ w : ℂ, ‖w - c‖ ≤ R / 2 → f w = 0 → w ∈ Z₁) ∧ (∀ ρ ∈ Z₁, 1 ≤ m ρ) ∧
      (∀ z : ℂ, ‖z - c‖ ≤ R / 8 → f z ≠ 0 → (∀ ρ ∈ Z₁, ρ.re ≤ z.re) → ∀ S ⊆ Z₁,
        -(logDeriv f z).re
          ≤ 16 * Real.log M / R - ∑ ρ ∈ S, (m ρ : ℝ) * ((z - ρ)⁻¹).re) := by
  obtain ⟨Z₁, m, hZ₁, hzero, hmem, hmult, hbnd0⟩ :=
    landau_logDeriv hR hRR₀ hM hf hfc hbound
  refine ⟨Z₁, m, hZ₁, hzero, hmem, hmult, ?_⟩
  intro z hz hfz hre S hS
  have hbnd := hbnd0 z hz hfz
  set T₁ : ℂ := ∑ ρ ∈ Z₁, (m ρ : ℂ) / (z - ρ) with hTdef
  have hreT : T₁.re = ∑ ρ ∈ Z₁, (m ρ : ℝ) * ((z - ρ)⁻¹).re := by
    rw [hTdef, Complex.re_sum]
    exact Finset.sum_congr rfl fun ρ _ => re_natCast_div _ _
  have hnn : ∀ ρ ∈ Z₁, 0 ≤ (m ρ : ℝ) * ((z - ρ)⁻¹).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_inv_sub_nonneg (hre ρ hρ))
  have hsub : ∑ ρ ∈ S, (m ρ : ℝ) * ((z - ρ)⁻¹).re
      ≤ ∑ ρ ∈ Z₁, (m ρ : ℝ) * ((z - ρ)⁻¹).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun ρ hρ _ => hnn ρ hρ
  have hdiff : -(logDeriv f z - T₁).re ≤ ‖logDeriv f z - T₁‖ := by
    have := Complex.abs_re_le_norm (logDeriv f z - T₁)
    have h2 := abs_le.mp this
    linarith [h2.1]
  have hsplit : (logDeriv f z).re = T₁.re + (logDeriv f z - T₁).re := by
    rw [Complex.sub_re]
    ring
  have hbnd' : ‖logDeriv f z - T₁‖ ≤ 16 * Real.log M / R := hbnd
  rw [hsplit, hreT]
  linarith

end RHTower.Sieve
