import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLowBox

/-!
# The regular part on the whole contour box

The contour box `|σ - 1| ≤ A/log⁹T`, `|t| ≤ T` is exactly the zero-free strip cut off at height `T`:
for `|t| ≤ T` the strip is *wider* than at height `T`, so the box sits inside it, and below height
`9` the compact-box bound takes over.  Hence on the whole box

    ‖zetaLogDerivReg(σ+it)‖ ≤ max M₀ ((2240/A)·log⁹T + 1/9),

and `ζ` has no zero there apart from the pole.

Choosing the right abscissa `d = 1 + A/log⁹T` rather than something larger is what keeps the top and
bottom edges inside the strip; the resulting Dirichlet-series constant `1/(d-1) = log⁹T/A` is only
polylogarithmic, so nothing is lost.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- The narrower strip at the truncation height sits inside the wider strip below it. -/
theorem strip_width_mono {T t : ℝ} (h9 : 9 ≤ |t|) (hle : |t| ≤ T) :
    zetaLowerA / Real.log T ^ (9 : ℕ) ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ) := by
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hlogle : Real.log |t| ≤ Real.log T :=
    Real.log_le_log (by linarith) hle
  have hpow : Real.log |t| ^ (9 : ℕ) ≤ Real.log T ^ (9 : ℕ) :=
    pow_le_pow_left₀ hL0.le hlogle 9
  exact div_le_div_of_nonneg_left zetaLowerA_pos.le (by positivity) hpow

/-- **`ζ` has no zero on the contour box.** -/
theorem riemannZeta_ne_zero_box {T δ₀ : ℝ} (hT : 9 ≤ T)
    (hfit : zetaLowerA / Real.log T ^ (9 : ℕ) ≤ δ₀)
    (hlowzf : ∀ c d : ℝ, 1 - δ₀ ≤ c → c ≤ 1 → 1 ≤ d →
      ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0)
    {s : ℂ} (hlo : 1 - zetaLowerA / Real.log T ^ (9 : ℕ) ≤ s.re)
    (hhi : s.re ≤ 1 + zetaLowerA / Real.log T ^ (9 : ℕ)) (him : |s.im| ≤ T) (hs : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hlogT : 2 < Real.log T := by
    have hexp2 := exp_two_lt_eight
    have h1 : Real.log (Real.exp 2) < Real.log T :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hquot : (0 : ℝ) < zetaLowerA / Real.log T ^ (9 : ℕ) := by positivity
  rcases le_or_gt (|s.im|) 9 with h9 | h9
  · have hc : (1 : ℝ) - δ₀ ≤ 1 - zetaLowerA / Real.log T ^ (9 : ℕ) := by linarith
    refine hlowzf (1 - zetaLowerA / Real.log T ^ (9 : ℕ)) (1 + zetaLowerA / Real.log T ^ (9 : ℕ))
      hc (by linarith) (by linarith) s ?_ hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith),
      Set.uIcc_of_le (by norm_num : (-9 : ℝ) ≤ 9)]
    exact ⟨⟨hlo, hhi⟩, (abs_le.1 h9).1, (abs_le.1 h9).2⟩
  · have hwid := strip_width_mono h9.le him
    have hseq : s = ((s.re : ℂ) + (s.im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [hseq]
    exact riemannZeta_ne_zero_strip h9.le (by linarith) (by linarith)

/-- **The regular part on the contour box.** -/
theorem norm_zetaLogDerivReg_box_le {T δ₀ M₀ : ℝ} (hT : 9 ≤ T)
    (hfit : zetaLowerA / Real.log T ^ (9 : ℕ) ≤ δ₀)
    (hlowbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M₀)
    {s : ℂ} (hlo : 1 - zetaLowerA / Real.log T ^ (9 : ℕ) ≤ s.re)
    (hhi : s.re ≤ 1 + zetaLowerA / Real.log T ^ (9 : ℕ)) (him : |s.im| ≤ T) :
    ‖zetaLogDerivReg s‖ ≤ max M₀ (2240 / zetaLowerA * Real.log T ^ (9 : ℕ) + 1 / 9) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hlogT : 2 < Real.log T := by
    have hexp2 := exp_two_lt_eight
    have h1 : Real.log (Real.exp 2) < Real.log T :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hLT0 : (0 : ℝ) < Real.log T := by linarith
  have hquot : (0 : ℝ) < zetaLowerA / Real.log T ^ (9 : ℕ) := by positivity
  have hquot1 : zetaLowerA / Real.log T ^ (9 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ Real.log T ^ (9 : ℕ) := one_le_pow₀ (by linarith)
    linarith
  rcases le_or_gt (|s.im|) 9 with h9 | h9
  · exact le_trans (hlowbox s (by linarith) (by linarith) h9) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hwid := strip_width_mono h9.le him
    have hseq : s = ((s.re : ℂ) + (s.im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hstrip : ‖zetaLogDerivReg ((s.re : ℂ) + (s.im : ℂ) * Complex.I)‖
        ≤ 2240 / zetaLowerA * Real.log |s.im| ^ (9 : ℕ) + 1 / 9 :=
      norm_zetaLogDerivReg_strip_le h9.le (by linarith) (by linarith)
    rw [hseq]
    refine le_trans hstrip ?_
    have hlogle : Real.log |s.im| ≤ Real.log T := Real.log_le_log (by linarith) him
    have hL0 : (0 : ℝ) ≤ Real.log |s.im| := by
      refine Real.log_nonneg ?_
      linarith
    have hpow : Real.log |s.im| ^ (9 : ℕ) ≤ Real.log T ^ (9 : ℕ) := pow_le_pow_left₀ hL0 hlogle 9
    have hcoef : (0 : ℝ) ≤ 2240 / zetaLowerA := by positivity
    nlinarith [hpow, hcoef]

/-- **The low-height data, jointly.**  One `δ` serving both the zero-free box and the bound. -/
theorem exists_low_data :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      (∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d →
        ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0) ∧
      (∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M) := by
  obtain ⟨δ₁, hδ₁, hzf⟩ := exists_zero_free_rect (T := (9 : ℝ)) (by norm_num)
  obtain ⟨δ₂, hδ₂, M, hM, hbox⟩ := exists_bound_zetaLogDerivReg_low_box 2 (by norm_num)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, M, hM, ?_, ?_⟩
  · exact fun c d hc hc1 hd => hzf c d (by
      have := min_le_left δ₁ δ₂
      linarith) hc1 hd
  · exact fun s hlo hhi him => hbox s (by
      have := min_le_right δ₁ δ₂
      linarith) hhi him

end RHTower.Sieve
