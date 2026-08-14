import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound

/-!
# Uniform exponential decay of `Γ` on a vertical strip

On the line `Re z = 1 + m` the modulus of `Γ` is known exactly up to constants: it is
`|t|^{m+1/2} e^{-π|t|/2}` up to bounded factors.  The Gauss-product ratio inequality

```text
‖Γ(a + iτ)‖ · Γ(b) ≤ Γ(a) · ‖Γ(b + iτ)‖   (0 < a ≤ b)
```

transports that decay leftwards to every abscissa below, at the cost of the real ratio
`Γ(a)/Γ(b)`, which is bounded on a compact abscissa range.  The result is one constant and one
exponent serving the whole strip `1 ≤ Re z ≤ M`:

```text
‖Γ(σ + it)‖ ≤ C |t|^N e^{-π|t|/2} .
```

Uniformity in the abscissa is what a contour shift needs: the horizontal sides of a rectangle
sweep across the whole strip at a fixed height.
-/

open Complex Filter Set

namespace GaloisForLFunctions.HTGeometry

/-- The real Gamma function is bounded on a compact abscissa range inside the right half line. -/
theorem exists_bound_Real_Gamma_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, a ≤ σ → σ ≤ b → Real.Gamma σ ≤ C := by
  have hcont : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt.continuousWithinAt
    intro hcon
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hcon] at hxpos
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ hσa hσb => ?_⟩
  have h := hC σ ⟨hσa, hσb⟩
  have habs : Real.Gamma σ ≤ ‖Real.Gamma σ‖ := le_abs_self _
  exact habs.trans (h.trans (le_max_left _ _))

/-- **Uniform exponential decay of `Γ` on a vertical strip.**  One constant and one polynomial
exponent serve every abscissa in `[a, M]`, for every positive `a`. -/
theorem exists_bound_norm_Gamma_vertical_strip {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ M → 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  classical
  obtain ⟨Cγ, hCγ0, hCγ⟩ := exists_bound_Real_Gamma_Icc (a := a) (b := M) ha
  set m : ℕ := ⌈M⌉₊ with hm
  have hMm : M ≤ 1 + (m : ℝ) := by
    have := Nat.le_ceil M
    rw [← hm] at this
    linarith
  set K : ℝ := Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) with hK
  have hposden : (0 : ℝ) < 1 - Real.exp (-2) := by
    have : Real.exp (-2) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hΓb : (0 : ℝ) < Real.Gamma (1 + (m : ℝ)) := Real.Gamma_pos_of_pos (by positivity)
  refine ⟨Cγ * K * (2 + (m : ℝ)) ^ m / Real.Gamma (1 + (m : ℝ)), m + 1, by positivity, ?_⟩
  intro σ t hσ1 hσM ht
  have htpos : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have hσpos : (0 : ℝ) < σ := lt_of_lt_of_le ha hσ1
  have hab : σ ≤ 1 + (m : ℝ) := le_trans hσM hMm
  -- transport the decay from the line `Re z = 1 + m`
  have hratio := HTGeometry.norm_Gamma_mul_Gamma_le (a := σ) (b := 1 + (m : ℝ)) hσpos hab t
  have hshape : (((1 + (m : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I
      = 1 + (t : ℂ) * Complex.I + (m : ℂ) := by push_cast; ring
  rw [hshape] at hratio
  obtain ⟨-, hhigh⟩ := norm_Gamma_one_add_nat_bounds m ht
  -- the square root factor is at most `K |t|`
  have hsqrt : Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2))) ≤ K * |t| := by
    have hrw : 2 * Real.pi * |t| / (1 - Real.exp (-2))
        = (2 * Real.pi / (1 - Real.exp (-2))) * |t| := by
      field_simp
    rw [hrw, Real.sqrt_mul (by positivity), hK]
    have hle : Real.sqrt |t| ≤ |t| := by
      nlinarith [Real.sq_sqrt (le_of_lt htpos), Real.sqrt_nonneg |t|, ht]
    exact mul_le_mul_of_nonneg_left hle hK0
  have hexp0 : (0 : ℝ) < Real.exp (-(Real.pi * |t| / 2)) := Real.exp_pos _
  have hpow : ((2 + (m : ℝ)) * |t|) ^ m = (2 + (m : ℝ)) ^ m * |t| ^ m := mul_pow _ _ _
  have hhigh' : ‖Complex.Gamma (1 + (t : ℂ) * Complex.I + (m : ℂ))‖
      ≤ K * (2 + (m : ℝ)) ^ m * |t| ^ (m + 1) * Real.exp (-(Real.pi * |t| / 2)) := by
    refine hhigh.trans ?_
    rw [hpow]
    have hstep : Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2)))
        * ((2 + (m : ℝ)) ^ m * |t| ^ m)
        ≤ (K * |t|) * ((2 + (m : ℝ)) ^ m * |t| ^ m) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    calc Real.sqrt (2 * Real.pi * |t| / (1 - Real.exp (-2)))
          * ((2 + (m : ℝ)) ^ m * |t| ^ m) * Real.exp (-(Real.pi * |t| / 2))
        ≤ (K * |t|) * ((2 + (m : ℝ)) ^ m * |t| ^ m) * Real.exp (-(Real.pi * |t| / 2)) :=
          mul_le_mul_of_nonneg_right hstep (le_of_lt hexp0)
      _ = K * (2 + (m : ℝ)) ^ m * |t| ^ (m + 1) * Real.exp (-(Real.pi * |t| / 2)) := by
          rw [pow_succ]; ring
  -- assemble
  have hΓσ : Real.Gamma σ ≤ Cγ := hCγ σ hσ1 hσM
  have hkey : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * Real.Gamma (1 + (m : ℝ))
      ≤ Cγ * (K * (2 + (m : ℝ)) ^ m * |t| ^ (m + 1) * Real.exp (-(Real.pi * |t| / 2))) := by
    refine hratio.trans ?_
    exact mul_le_mul hΓσ hhigh' (norm_nonneg _) hCγ0
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hΓb]
  refine hkey.trans (le_of_eq ?_)
  ring

end GaloisForLFunctions.HTGeometry
