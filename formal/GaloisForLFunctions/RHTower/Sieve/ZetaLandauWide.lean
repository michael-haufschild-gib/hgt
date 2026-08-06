import GaloisForLFunctions.RHTower.Sieve.ZetaWideDisc

/-!
# Landau's lemma on the wide disc

With the growth bound `‖ζ‖ ≤ 91 + 40|γ|` on the disc of radius `11/10` around `9/8 + iγ` and the
reciprocal estimate at the centre, the Landau ratio satisfies `log M ≤ wideD · log|γ|` for an
absolute constant `wideD`.  Landau's lemma at radius `21/20` then bounds the logarithmic derivative
of `ζ`, minus its pole part, by `(320/21)·wideD·log|γ|` at every point within `21/160` of the
centre — which reaches `σ = 159/160`, inside the zero-free region.
-/

namespace RHTower.Sieve

open Metric Complex

/-- The absolute constant of the wide-disc Landau bound. -/
noncomputable def wideD : ℝ :=
  Real.log 131 + 3 / 4 * Real.log 9 + 1 / 4 * Real.log 11 + 5 / 4

theorem wideD_pos : 0 < wideD := by
  have h1 : (0 : ℝ) ≤ Real.log 131 := Real.log_nonneg (by norm_num)
  have h2 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h3 : (0 : ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
  rw [wideD]
  linarith

/-- At height at least `4` the logarithm is at least `1`. -/
theorem one_le_log_abs {γ : ℝ} (hγ : 4 ≤ |γ|) : (1 : ℝ) ≤ Real.log |γ| := by
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  rw [Real.le_log_iff_exp_le hγ0]
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  linarith

/-- The value at the centre is not zero. -/
theorem zeta_wide_centre_ne_zero (γ : ℝ) :
    riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by rw [wide_centre_re]; norm_num)

/-- **The Landau ratio on the wide disc.** -/
theorem log_wide_ratio_le {γ : ℝ} (hγ : 4 ≤ |γ|) :
    Real.log ((91 + 40 * |γ|)
        / ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖)
      ≤ wideD * Real.log |γ| := by
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hL1 := one_le_log_abs hγ
  have hpos : (0 : ℝ) < ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (zeta_wide_centre_ne_zero γ)
  rw [Real.log_div (by linarith) (ne_of_gt hpos)]
  have hnum : Real.log (91 + 40 * |γ|) ≤ Real.log 131 + Real.log |γ| := by
    have h1 : (91 : ℝ) + 40 * |γ| ≤ 131 * |γ| := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < 91 + 40 * |γ|) h1
    rwa [Real.log_mul (by norm_num) (ne_of_gt hγ0)] at h2
  have hden := neg_log_norm_riemannZeta_le (σ := 9 / 8) (t := γ) (by norm_num) (by norm_num)
    (by linarith)
  have hval : (1 : ℝ) + 1 / (9 / 8 - 1) = 9 := by norm_num
  rw [hval] at hden
  have hfour : Real.log (7 + 4 * |γ|) ≤ Real.log 11 + Real.log |γ| := by
    have h1 : (7 : ℝ) + 4 * |γ| ≤ 11 * |γ| := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < 7 + 4 * |γ|) h1
    rwa [Real.log_mul (by norm_num) (ne_of_gt hγ0)] at h2
  have hK : (0 : ℝ) ≤ Real.log 131 + 3 / 4 * Real.log 9 + 1 / 4 * Real.log 11 := by
    have h1 : (0 : ℝ) ≤ Real.log 131 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
    have h3 : (0 : ℝ) ≤ Real.log 11 := Real.log_nonneg (by norm_num)
    linarith
  rw [wideD]
  nlinarith [hden, hnum, hfour, hL1,
    mul_nonneg hK (by linarith : (0 : ℝ) ≤ Real.log |γ| - 1)]

/-- **Landau's data on the wide disc.** -/
theorem zeta_landau_wide {γ : ℝ} (hγ : 4 ≤ |γ|) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40) ∧
      (∀ ρ ∈ Z, riemannZeta ρ = 0) ∧
      (∀ w : ℂ, ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40 →
        riemannZeta w = 0 → w ∈ Z) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ∀ z : ℂ, ‖z - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 160 →
        riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖
          ≤ 320 / 21 * wideD * Real.log |γ| := by
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hfc := zeta_wide_centre_ne_zero γ
  have hpos : (0 : ℝ) < ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hfc
  have hM1 : (1 : ℝ) < (91 + 40 * |γ|)
      / ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := by
    rw [lt_div_iff₀ hpos, one_mul]
    have hcr := norm_riemannZeta_le_crude_of_re_ge
      (w := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)) (η := 1 / 40) (by norm_num)
      (by rw [wide_centre_re]; norm_num) (by rw [wide_centre_im]; linarith)
    have hn : ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 9 / 8 + |γ| := by
      refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
      rw [wide_centre_re, wide_centre_im]
      have : |(9 : ℝ) / 8| = 9 / 8 := abs_of_pos (by norm_num)
      rw [this]
    have hdiv : ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ / (1 / 40 : ℝ)
        = 40 * ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := by ring
    rw [hdiv] at hcr
    linarith
  have hbound : ∀ w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) (11 / 10 : ℝ),
      ‖riemannZeta w‖ ≤ ((91 + 40 * |γ|)
        / ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖)
        * ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := by
    intro w hw
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
    exact zeta_wide_disc_bound hγ hw
  obtain ⟨Z, m, hZdist, hZzero, hZmem, hZmult, hZkey⟩ :=
    landau_logDeriv (f := riemannZeta)
      (c := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)) (R := 21 / 20) (R₀ := 11 / 10)
      (by norm_num) (by norm_num) hM1 (zeta_analytic_wide hγ) hfc hbound
  refine ⟨Z, m, fun ρ hρ => by linarith [hZdist ρ hρ], hZzero,
    fun w hw hfw => hZmem w (by linarith) hfw, hZmult, fun z hz hfz => ?_⟩
  have hkey := hZkey z (by linarith) hfz
  have hrw : 16 * Real.log ((91 + 40 * |γ|)
      / ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖) / (21 / 20)
      = 320 / 21 * Real.log ((91 + 40 * |γ|)
        / ‖riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖) := by ring
  rw [hrw] at hkey
  have hlog := log_wide_ratio_le hγ
  linarith [hkey, hlog]

end RHTower.Sieve
