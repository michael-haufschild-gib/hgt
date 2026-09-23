import GaloisForLFunctions.RHTower.Sieve.ChebyshevBoxSubstitution

/-!
# The contour data exists

Everything the box estimate needs about `ζ` below height `9` is a single pair `(δ₀, M₀)`, and the
compatibility `A/log⁹T ≤ δ₀` holds for all large `T`.  Collecting them:

    ∃ T₀ δ₀ M₀,  the box is zero-free below height 9, the regular part is bounded there,
                 and every height `T ≥ T₀` fits inside the box.

None of these constants depends on the cutoff, so they are fixed once and reused at every `N`.
-/

namespace RHTower.Sieve

open Complex Filter RHTower

/-- Every large truncation height fits inside a fixed box. -/
theorem exists_height_fit {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ T₀ : ℝ, 9 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → zetaLowerA / Real.log T ^ (9 : ℕ) ≤ δ₀ := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlog : Tendsto (fun T : ℝ => Real.log T ^ (9 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop (zetaLowerA / δ₀))
  refine ⟨max 9 T₁, le_max_left _ _, fun T hT => ?_⟩
  have h9 : (9 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hge := hT₁ T (le_trans (le_max_right _ _) hT)
  have hlogT : 2 < Real.log T := by
    have hexp2 := exp_two_lt_eight
    have h1 : Real.log (Real.exp 2) < Real.log T :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hpow : (0 : ℝ) < Real.log T ^ (9 : ℕ) := by positivity
  rw [div_le_iff₀ hpow]
  rw [div_le_iff₀ hδ₀] at hge
  linarith

/-- **The contour data exists.**  A single `(δ₀, M₀)` serves the zero-free box and the bound on the
regular part below height `9`, and every height beyond `T₀` fits. -/
theorem exists_chebyshev_contour_data :
    ∃ (T₀ δ₀ M₀ : ℝ), 9 ≤ T₀ ∧ 0 < δ₀ ∧ 0 ≤ M₀ ∧
      (∀ T : ℝ, T₀ ≤ T → zetaLowerA / Real.log T ^ (9 : ℕ) ≤ δ₀) ∧
      (∀ c d : ℝ, 1 - δ₀ ≤ c → c ≤ 1 → 1 ≤ d →
        ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0) ∧
      (∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M₀) := by
  obtain ⟨δ₀, hδ₀, M₀, hM₀, hzf, hbox⟩ := exists_low_data
  obtain ⟨T₀, hT₀, hfit⟩ := exists_height_fit hδ₀
  exact ⟨T₀, δ₀, M₀, hT₀, hδ₀, hM₀, hfit, hzf, hbox⟩

end RHTower.Sieve
