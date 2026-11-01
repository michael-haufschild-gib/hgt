import GaloisForLFunctions.ArithmeticHarmonicAnalysis.ZetaCriticalLineSubWeylBound
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.ZetaFiveSixthsSubconvexity
import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsProfiles

/-! # Four interpolation profiles from the sub-Weyl source bounds

The source points are `(1/2,33/200)`, `(11/18,1/9)`, `(5/7,1/14)`
and `(5/6,2/53)`. Phragmén–Lindelöf interpolates adjacent points and
the absolutely convergent edge at `1+η`.
-/

noncomputable section
open RHTower Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem zetaEntire_edge_of_line {σ μ C : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (_hC : 0 < C)
    (hb : ∀ t : ℝ, 8 ≤ t → ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ μ) :
    ∀ y : ℝ, 8 ≤ |y| →
      ‖zetaEntire ((σ : ℂ) + (y : ℂ) * I)‖ ≤ (2 * C) * |y| ^ (1 + μ) := by
  intro y hy
  have hy0 : 0 < |y| := by linarith only [hy]
  have hζ : ‖riemannZeta ((σ : ℂ) + (y : ℂ) * I)‖ ≤ C * |y| ^ μ := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy ⊢
      exact hb y hy
    · rw [abs_of_neg h] at hy ⊢
      have he : (σ : ℂ) + (y : ℂ) * I =
          starRingEnd ℂ ((σ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        push_cast
        ring
      rw [he, riemannZeta_conj, Complex.norm_conj]
      exact hb (-y) hy
  have hz1 : (σ : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re] at hr
    linarith only [hr, hσ1]
  have hn : ‖(σ : ℂ) + (y : ℂ) * I - 1‖ ≤ 2 * |y| := by
    have he : (σ : ℂ) + (y : ℂ) * I - 1 = ((σ - 1 : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast
      ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith only [hσ1] : σ - 1 ≤ 0)]
    linarith only [hσ, hy]
  rw [zetaEntire_eq hz1, norm_mul, Real.rpow_add hy0, Real.rpow_one]
  calc _ ≤ (2 * |y|) * (C * |y| ^ μ) :=
      mul_le_mul hn hζ (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The new critical-line edge, with an arbitrary positive power loss. -/
theorem exists_norm_zetaEntire_half_subWeyl_edge_le {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 8 ≤ |y| →
      ‖zetaEntire (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        M * |y| ^ (233 / 200 + η) := by
  obtain ⟨C, hC, hz⟩ := exists_norm_riemannZeta_half_le_subWeyl
  have hline : ∀ t : ℝ, 8 ≤ t →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C / η * t ^ (33 / 200 + η) := by
    intro t ht
    have ht0 : 0 < t := by linarith only [ht]
    have h := hz t ht
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring] at h
    refine h.trans ?_
    calc _ ≤ C * t ^ (33 / 200 : ℝ) * (t ^ η / η) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div ht0.le hη) (by positivity)
      _ = C / η * (t ^ (33 / 200 : ℝ) * t ^ η) := by ring
      _ = _ := by rw [← Real.rpow_add ht0]
  refine ⟨2 * (C / η), by positivity, fun y hy => ?_⟩
  simpa only [show (1 : ℝ) + (33 / 200 + η) = 233 / 200 + η by ring] using
    zetaEntire_edge_of_line (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (by positivity) hline y hy

/-- The new `5/6` edge, with an arbitrary positive power loss. -/
theorem exists_norm_zetaEntire_fiveSixths_edge_le {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 8 ≤ |y| →
      ‖zetaEntire (((5 / 6 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M * |y| ^ (55 / 53 + η) := by
  have hline : ∀ t : ℝ, 8 ≤ t →
      ‖riemannZeta (((5 / 6 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (10 ^ 7 / η) * t ^ (2 / 53 + η) := by
    intro t ht
    have ht0 : 0 < t := by linarith only [ht]
    have h := norm_riemannZeta_fiveSixths_le ht
    rw [show (5 / 6 : ℂ) = ((5 / 6 : ℝ) : ℂ) by push_cast; ring] at h
    refine h.trans ?_
    calc _ ≤ 10 ^ 7 * t ^ (2 / 53 : ℝ) * (t ^ η / η) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div ht0.le hη) (by positivity)
      _ = (10 ^ 7 / η) * (t ^ (2 / 53 : ℝ) * t ^ η) := by ring
      _ = _ := by rw [← Real.rpow_add ht0]
  refine ⟨2 * (10 ^ 7 / η), by positivity, fun y hy => ?_⟩
  simpa only [show (1 : ℝ) + (2 / 53 + η) = 55 / 53 + η by ring] using
    zetaEntire_edge_of_line (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num) (by positivity) hline y hy

/-- Interpolation from the sub-Weyl point to the `11/18` point. -/
theorem exists_norm_riemannZeta_le_subWeyl_profile_one {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 11 / 18 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * t ^ (33 / 200 + η - 97 / 200 * (σ - 1 / 2)) := by
  obtain ⟨A, hA, ha⟩ := exists_norm_zetaEntire_half_subWeyl_edge_le hη
  obtain ⟨B, hB, hb⟩ := exists_norm_zetaEntire_elevenEighteenths_edge_le hη
  obtain ⟨C, hC, hc⟩ := exists_norm_riemannZeta_le_interp (a := 1 / 2) (b := 11 / 18)
    (pa := 233 / 200 + η) (pb := 10 / 9 + η) (Ma := A) (Mb := B)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    hA.le hB.le ha hb
  refine ⟨C, hC, fun σ t h1 h2 ht => (hc σ t h1 h2 ht).trans_eq ?_⟩
  congr 2
  ring

/-- Interpolation from the `5/7` point to the `5/6` point. -/
theorem exists_norm_riemannZeta_le_subWeyl_profile_three {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 5 / 7 ≤ σ → σ ≤ 5 / 6 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * t ^ (1 / 14 + η - 15 / 53 * (σ - 5 / 7)) := by
  obtain ⟨B, hB, hb⟩ := exists_norm_zetaEntire_fiveSixths_edge_le hη
  obtain ⟨C, hC, hc⟩ := exists_norm_riemannZeta_le_interp (a := 5 / 7) (b := 5 / 6)
    (pa := 15 / 14 + η) (pb := 55 / 53 + η) (Ma := 20600 / η) (Mb := B)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    (by positivity) hB.le (fun y hy => norm_zetaEntire_fiveSevenths_edge_le hη hy) hb
  refine ⟨C, hC, fun σ t h1 h2 ht => (hc σ t h1 h2 ht).trans_eq ?_⟩
  congr 2
  ring

/-- Interpolation from the `5/6` point to absolute convergence. -/
theorem exists_norm_riemannZeta_le_subWeyl_profile_four {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 5 / 6 ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * t ^ ((2 / 53 + η) * (1 + η - σ) / (1 / 6 + η)) := by
  obtain ⟨A, hA, ha⟩ := exists_norm_zetaEntire_fiveSixths_edge_le hη
  obtain ⟨C, hC, hc⟩ := exists_norm_riemannZeta_le_interp (a := 5 / 6) (b := 1 + η)
    (pa := 55 / 53 + η) (pb := 1) (Ma := A) (Mb := 2 * (1 + 1 / η))
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith only [hη1])
    hA.le (by positivity) ha (fun y hy => norm_zetaEntire_right_edge_le_abs hη (by linarith) hy)
  refine ⟨C, hC, fun σ t h1 h2 ht => (hc σ t h1 h2 ht).trans_eq ?_⟩
  rw [show (1 + η - 5 / 6 : ℝ) = 1 / 6 + η by ring]
  congr 2
  have hd : (1 / 6 : ℝ) + η ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_le_subWeyl_profile_one
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_le_subWeyl_profile_three
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_le_subWeyl_profile_four
