import GaloisForLFunctions.RHTower.XiSliceHeatRateInteriorLindelof
import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsLineBound

/-!
# The three-piece Lindelöf profile through `μ(11/18) ≤ 1/9`

With `μ(1/2) ≤ 1/6`, `μ(11/18) ≤ 1/9` (`norm_riemannZeta_elevenEighteenths_le`) and
`μ(5/7) ≤ 1/14`, Phragmén–Lindelöf gives, for every `η > 0` and `t ≥ 8`:

* `σ ∈ [1/2, 11/18]`: `‖ζ(σ + it)‖ ≤ C t^{1/6 + η − (σ − 1/2)/2}` (`exists_norm_riemannZeta_le_profile_ee_one`);
* `σ ∈ [11/18, 5/7]`: `‖ζ(σ + it)‖ ≤ C t^{1/9 + η − (5/13)(σ − 11/18)}`
  (`exists_norm_riemannZeta_le_profile_ee_two`).

The edge bound on `Re s = 11/18` (`exists_norm_zetaEntire_elevenEighteenths_edge_le`) uses the new
line bound for `t ≥ 1024π` and the corpus first profile below it.
-/

open Complex

namespace RHTower

noncomputable section

/-- `‖ζ(11/18 + iu)‖ ≤ M u^{1/9 + η}` for all `u ≥ 8`. -/
theorem exists_norm_riemannZeta_elevenEighteenths_le {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℝ, 8 ≤ u →
      ‖riemannZeta (((11 / 18 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ M * u ^ (1 / 9 + η) := by
  obtain ⟨C₁, hC₁, hp₁⟩ := exists_norm_riemannZeta_le_profile_one (η := 1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨max (10 ^ 7 / η) (4000 * C₁), by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hpow1 : (1 : ℝ) ≤ u ^ (1 / 9 + η) := Real.one_le_rpow hu1 (by positivity)
  by_cases hbig : 1024 * Real.pi ≤ u
  · have h0 := norm_riemannZeta_elevenEighteenths_le hbig
    rw [show (11 / 18 : ℂ) = ((11 / 18 : ℝ) : ℂ) by push_cast; ring] at h0
    refine h0.trans ?_
    have hlog := Real.log_le_rpow_div hu0.le hη
    calc 10 ^ 7 * u ^ (1 / 9 : ℝ) * Real.log u ≤ 10 ^ 7 * u ^ (1 / 9 : ℝ) * (u ^ η / η) := by
          gcongr
      _ = 10 ^ 7 / η * (u ^ (1 / 9 : ℝ) * u ^ η) := by ring
      _ = 10 ^ 7 / η * u ^ (1 / 9 + η) := by rw [← Real.rpow_add hu0]
      _ ≤ max (10 ^ 7 / η) (4000 * C₁) * u ^ (1 / 9 + η) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hbig
    have h := hp₁ (11 / 18) u (by norm_num) (by norm_num) hu
    refine h.trans ?_
    have hexp : (1 / 6 + 1 / 2 - 4 / 9 * (11 / 18 - 1 / 2) : ℝ) ≤ 1 := by norm_num
    have hpi := Real.pi_lt_d2
    have hu4 : u ≤ 4000 := by linarith
    have h1 : u ^ (1 / 6 + 1 / 2 - 4 / 9 * (11 / 18 - 1 / 2) : ℝ) ≤ u ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1 hexp
    rw [Real.rpow_one] at h1
    calc C₁ * u ^ (1 / 6 + 1 / 2 - 4 / 9 * (11 / 18 - 1 / 2) : ℝ) ≤ C₁ * 4000 :=
          mul_le_mul_of_nonneg_left (h1.trans hu4) hC₁.le
      _ = 4000 * C₁ * 1 := by ring
      _ ≤ max (10 ^ 7 / η) (4000 * C₁) * u ^ (1 / 9 + η) :=
          mul_le_mul (le_max_right _ _) hpow1 (by norm_num) (by positivity)

/-- `‖(s − 1)ζ(s)‖ ≤ M |t|^{10/9 + η}` on `Re s = 11/18`, `|t| ≥ 8`. -/
theorem exists_norm_zetaEntire_elevenEighteenths_edge_le {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 8 ≤ |y| →
      ‖zetaEntire (((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M * |y| ^ (10 / 9 + η) := by
  obtain ⟨M, hM, key⟩ := exists_norm_riemannZeta_elevenEighteenths_le hη
  refine ⟨2 * M, by positivity, fun y hy => ?_⟩
  have hζ : ‖riemannZeta (((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M * |y| ^ (1 / 9 + η) := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy ⊢; exact key y hy
    · rw [abs_of_neg h] at hy ⊢
      have hc : ((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I
          = starRingEnd ℂ (((11 / 18 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        push_cast; ring
      rw [hc, riemannZeta_conj, Complex.norm_conj]
      exact key (-y) hy
  have hz1 : ((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; norm_num at this
  rw [zetaEntire_eq hz1, norm_mul]
  have hn : ‖((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I - 1‖ ≤ 2 * |y| := by
    have e : ((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I - 1 = ((-7 / 18 : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [e]; refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
    norm_num; linarith
  have hy0 : 0 < |y| := by linarith
  have hpow : |y| ^ (10 / 9 + η) = |y| * |y| ^ (1 / 9 + η) := by
    rw [show (10 / 9 : ℝ) + η = 1 + (1 / 9 + η) by ring, Real.rpow_add hy0, Real.rpow_one]
  calc ‖((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I - 1‖ * ‖riemannZeta (((11 / 18 : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * |y|) * (M * |y| ^ (1 / 9 + η)) := by gcongr
    _ = 2 * M * (|y| * |y| ^ (1 / 9 + η)) := by ring
    _ = 2 * M * |y| ^ (10 / 9 + η) := by rw [hpow]

/-- **Profile on `[1/2, 11/18]`.**  `‖ζ(σ + it)‖ ≤ C t^{1/6 + η − (σ − 1/2)/2}`, `t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_profile_ee_one {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 11 / 18 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (1 / 6 + η - (σ - 1 / 2) / 2) := by
  obtain ⟨M, hM, hedge⟩ := exists_norm_zetaEntire_elevenEighteenths_edge_le hη
  obtain ⟨C, hC, h⟩ := exists_norm_riemannZeta_le_interp (a := 1 / 2) (b := 11 / 18)
    (pa := 7 / 6 + η) (pb := 10 / 9 + η) (Ma := 8400 / η) (Mb := M)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    (by positivity) hM.le
    (fun y hy => by simpa using norm_zetaEntire_half_edge_le hη hy)
    (fun y hy => hedge y hy)
  refine ⟨C, hC, fun σ t h1 h2 ht => (h σ t h1 h2 ht).trans (le_of_eq ?_)⟩
  congr 2; ring

/-- **Profile on `[11/18, 5/7]`.**  `‖ζ(σ + it)‖ ≤ C t^{1/9 + η − (5/13)(σ − 11/18)}`, `t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_profile_ee_two {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 11 / 18 ≤ σ → σ ≤ 5 / 7 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * t ^ (1 / 9 + η - 5 / 13 * (σ - 11 / 18)) := by
  obtain ⟨M, hM, hedge⟩ := exists_norm_zetaEntire_elevenEighteenths_edge_le hη
  obtain ⟨C, hC, h⟩ := exists_norm_riemannZeta_le_interp (a := 11 / 18) (b := 5 / 7)
    (pa := 10 / 9 + η) (pb := 15 / 14 + η) (Ma := M) (Mb := 20600 / η)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    hM.le (by positivity)
    (fun y hy => hedge y hy)
    (fun y hy => norm_zetaEntire_fiveSevenths_edge_le hη hy)
  refine ⟨C, hC, fun σ t h1 h2 ht => (h σ t h1 h2 ht).trans (le_of_eq ?_)⟩
  congr 2; ring

end

end RHTower
