import GaloisForLFunctions.RHTower.Sieve.HalaszPerronAssembly
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin

/-!
# The Perron kernel constant, explicit in the cutoff data

`Sieve/HalaszPerronAssembly.exists_norm_tsum_mul_smoothWeight_le` leaves the quadratic-decay
constant of the Mellin kernel existentially quantified, so the assembled Halász bound cannot be
optimised in the cutoff `N`, the smoothing width `H` or the abscissa `σ`.  The two-scale Mellin
estimate `HTGeometry/SmoothWeightSharpMellin.exists_mellin_smoothWeight_two_scale_bounds` supplies
the missing information: with one absolute constant `C₁`,

```text
   |y|²·‖W(σ+iy)‖ ≤ C₁·((N+H)/H)·(N+H)^σ ,      ‖W(σ+iy)‖ ≤ (N+H)^σ/σ ,
```

and combining the two regimes gives the quadratic-decay bound with

```text
   C = (N+H)^σ·(1/σ + C₁·(N+H)/H) ,
```

explicit in every parameter apart from one absolute constant.  This is what turns the assembled
Halász bound into a statement that can be optimised over `T`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

noncomputable section

/-- The quadratic-decay constant of the Perron kernel, explicit in the cutoff data. -/
def perronKernelConst (C₁ σ N H : ℝ) : ℝ :=
  (N + H) ^ σ * (1 / σ + C₁ * ((N + H) / H))

theorem perronKernelConst_nonneg {C₁ σ N H : ℝ} (hC₁ : 0 ≤ C₁) (hN : 0 < N) (hH : 0 < H)
    (hσ : 0 < σ) : 0 ≤ perronKernelConst C₁ σ N H := by
  have hNH : (0 : ℝ) < N + H := by linarith
  have hpow : (0 : ℝ) < (N + H) ^ σ := Real.rpow_pos_of_pos hNH σ
  have h1 : (0 : ℝ) ≤ 1 / σ := by positivity
  have h2 : (0 : ℝ) ≤ C₁ * ((N + H) / H) := by positivity
  rw [perronKernelConst]
  positivity

/-- **The Perron kernel decays quadratically, with an explicit constant.** -/
theorem exists_perronKernel_bound_explicit :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (σ N H : ℝ), 0 < N → 0 < H → 0 < σ → ∀ y : ℝ,
      ‖perronKernel σ N H y‖ ≤ perronKernelConst C₁ σ N H * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hb⟩ := exists_mellin_smoothWeight_two_scale_bounds
  refine ⟨C₁, hC₁, ?_⟩
  intro σ N H hN hH hσ y
  have hsre : (((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re = σ := by
    rw [re_ofReal_add_mul_I]
  have hsim : (((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).im = y := by
    simp
  have htriv : ‖perronKernel σ N H y‖ ≤ (N + H) ^ σ / σ := norm_perronKernel_le hN.le hH hσ y
  have h2 := (hb N H hN hH (((σ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
    (by rw [hsre]; exact hσ)).2
  rw [hsim, hsre] at h2
  have h2' : y ^ 2 * ‖perronKernel σ N H y‖ ≤ C₁ * ((N + H) / H) * (N + H) ^ σ := by
    refine le_trans (le_of_eq ?_) h2
    rw [sq_abs]
    rfl
  have hK0 : (0 : ℝ) ≤ ‖perronKernel σ N H y‖ := norm_nonneg _
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hmain : ‖perronKernel σ N H y‖ * (1 + y ^ 2) ≤ perronKernelConst C₁ σ N H := by
    rw [perronKernelConst]
    have hexpand : (N + H) ^ σ * (1 / σ + C₁ * ((N + H) / H))
        = (N + H) ^ σ / σ + C₁ * ((N + H) / H) * (N + H) ^ σ := by
      field_simp
    rw [hexpand]
    nlinarith [htriv, h2', hK0]
  calc ‖perronKernel σ N H y‖
      = ‖perronKernel σ N H y‖ * (1 + y ^ 2) * (1 + y ^ 2)⁻¹ := by field_simp
    _ ≤ perronKernelConst C₁ σ N H * (1 + y ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hmain (by positivity)

/-- **The assembled Halász bound for the smoothed sum, with every constant explicit.**  The only
quantity not written out is one absolute constant coming from the derivatives of the smooth
transition. -/
theorem exists_norm_tsum_mul_smoothWeight_le_explicitConst :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) →
      (∀ n, ‖f n‖ ≤ 1) → f 0 = 0 →
      ∀ (σ : ℝ), 1 < σ → ∀ (z : ℕ), 2 ≤ z → ∀ (δ : ℝ), 0 ≤ δ → 0 < logSqWeight z →
      ∀ (N H : ℝ), 0 < N → 0 < H → ∀ (T : ℝ), 0 ≤ T →
        (2 * Real.pi) *
            ‖∑' n : ℕ, f n *
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖ ≤
          ((N + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
                Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) * (2 * T)
              + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
                ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
                  (2 * Real.sqrt (2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight z))))
            + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
                (perronKernelConst C₁ σ N H * (Real.pi - 2 * Real.arctan T)) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_perronKernel_bound_explicit
  refine ⟨C₁, hC₁, ?_⟩
  intro f hf1 hmul hbdd hf0 σ hσ z hz2 δ hδ hWz N H hN hH T hT
  exact norm_tsum_mul_smoothWeight_le_of_kernelBound hf1 hmul hbdd hf0 hσ hz2 hδ hWz hN hH hT
    (perronKernelConst_nonneg (by linarith) hN hH (by linarith))
    (hb σ N H hN hH (by linarith))

end

end RHTower.Sieve
