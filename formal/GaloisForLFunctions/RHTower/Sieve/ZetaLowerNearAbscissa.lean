import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality
import GaloisForLFunctions.RHTower.Sieve.ZetaLandauWide

/-!
# A lower bound for `ζ` just right of the abscissa

At `σ₁ = 1 + 1/log²|γ|` the reciprocal estimate gives

```text
-log‖ζ(σ₁ + iγ)‖ ≤ (3/4) log(1 + log²|γ|) + (1/4) log‖ζ(σ₁ + 2iγ)‖,
```

and the second term is `O(log log|γ|)` once the *logarithmic* growth bound is used at the doubled
height rather than the crude linear one.  Hence

```text
‖ζ(σ₁ + iγ)‖ ≫ (log|γ|)^(-7/4).
```

Starting from `σ₁ - 1 = log^{-2}` rather than `log^{-1}` is what makes the segment transport able to
cross the abscissa: the travel budget `log log|γ| / log²|γ|` exceeds `σ₁ - 1`.
-/

namespace RHTower.Sieve

open Complex

/-- The reciprocal estimate with an arbitrary bound at the doubled height. -/
theorem neg_log_norm_riemannZeta_le_of_bound {σ t B : ℝ} (hσ1 : 1 < σ)
    (hB : ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ B) :
    -Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log B := by
  have hz1 : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz1pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hz1
  have hzσ : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hzσpos : (0 : ℝ) < ‖riemannZeta (σ : ℂ)‖ := norm_pos_iff.mpr hzσ
  have hz2 : riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz2pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hz2
  have hinv := ZetaInvBound1 (σ := σ) (t := t) hσ1
  have hlog := Real.log_le_log (by positivity) hinv
  rw [Real.log_div one_ne_zero (ne_of_gt hz1pos), Real.log_one, zero_sub,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hzσpos,
    Real.log_rpow hz2pos] at hlog
  refine le_trans hlog ?_
  have hA : Real.log ‖riemannZeta (σ : ℂ)‖ ≤ Real.log (1 + 1 / (σ - 1)) :=
    log_norm_riemannZeta_real_le hσ1
  have hBlog : Real.log ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ Real.log B :=
    Real.log_le_log hz2pos hB
  linarith

/-- **The lower bound just right of the abscissa.**  At `σ₁ = 1 + log^{-2}|γ|` the reciprocal of
`ζ` is at most a fixed power of `log|γ|`. -/
theorem exists_neg_log_zeta_upper :
    ∃ C T : ℝ, 4 ≤ T ∧ ∀ γ : ℝ, T ≤ |γ| →
      -Real.log ‖riemannZeta ((((1 + 1 / Real.log |γ| ^ 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)‖
        ≤ 7 / 4 * Real.log (Real.log |γ|) + C := by
  obtain ⟨A, hA, C₀, hC₀, hup⟩ := ZetaUpperBnd
  refine ⟨3 / 4 * Real.log 2 + 1 / 4 * Real.log (2 * C₀), 4, le_rfl, ?_⟩
  intro γ hγ
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hL1 := one_le_log_abs hγ
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  set L : ℝ := Real.log |γ| with hLdef
  set σ₁ : ℝ := 1 + 1 / L ^ 2 with hσdef
  have hσ1 : 1 < σ₁ := by
    rw [hσdef]
    have : (0 : ℝ) < 1 / L ^ 2 := by positivity
    linarith
  have hσ2 : σ₁ ≤ 2 := by
    rw [hσdef]
    have : (1 : ℝ) / L ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hL1]
    linarith
  -- the bound at the doubled height
  have habs2 : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
  have hlog2γ : Real.log |2 * γ| ≤ 2 * L := by
    rw [habs2]
    have h2 := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hγ0)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    rw [h2, hLdef]
    linarith
  have hlog2γpos : (0 : ℝ) < Real.log |2 * γ| := by
    rw [habs2]
    refine Real.log_pos ?_
    linarith
  have hbnd := hup σ₁ (2 * γ) (by rw [habs2]; linarith)
    ⟨by
      have : (0 : ℝ) < A / Real.log |2 * γ| := div_pos hA.1 hlog2γpos
      linarith, hσ2⟩
  have hcast : ((2 * γ : ℝ) : ℂ) = 2 * (γ : ℂ) := by push_cast; ring
  rw [hcast] at hbnd
  have hBpos : (0 : ℝ) < C₀ * Real.log |2 * γ| := by positivity
  have hkey := neg_log_norm_riemannZeta_le_of_bound (σ := σ₁) (t := γ) hσ1 hbnd
  refine le_trans hkey ?_
  -- the two logarithms
  have hfirst : Real.log (1 + 1 / (σ₁ - 1)) ≤ Real.log 2 + 2 * Real.log L := by
    have hval : (1 : ℝ) + 1 / (σ₁ - 1) = 1 + L ^ 2 := by
      rw [hσdef]
      have : (1 : ℝ) + 1 / L ^ 2 - 1 = 1 / L ^ 2 := by ring
      rw [this, one_div_one_div]
    rw [hval]
    have hle : (1 : ℝ) + L ^ 2 ≤ 2 * L ^ 2 := by nlinarith [hL1]
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < 1 + L ^ 2) hle
    have h2 : Real.log (2 * L ^ 2) = Real.log 2 + 2 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith
  have hsecond : Real.log (C₀ * Real.log |2 * γ|) ≤ Real.log (2 * C₀) + Real.log L := by
    have hle : C₀ * Real.log |2 * γ| ≤ (2 * C₀) * L := by nlinarith [hlog2γ, hC₀]
    have h1 := Real.log_le_log hBpos hle
    have h2 : Real.log ((2 * C₀) * L) = Real.log (2 * C₀) + Real.log L :=
      Real.log_mul (by positivity) (by positivity)
    linarith [h1, h2]
  linarith

end RHTower.Sieve
