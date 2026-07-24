import GaloisForLFunctions.RHTower.ZetaLogDerivStripRange

/-!
# The master error bound for the smoothed Chebyshev sum

There exist a zero-free margin `δ₀` and a constant `M₀` such that for
all `x ≥ 1`, `1 < a ≤ 2`, and heights `T = 2πW ≥ 9` with
`a ≤ 1 + A/(2·log⁹T)`, taking `σ₀ = 1 − min δ₀ (A/(2·log⁹T))`:

`‖∑ Λ(n)(log(x/n))⁺ − x‖ ≤ tails + (2π)⁻¹·(edges)`,

with the tails `2·(8/(a−1)²)·x^a/(4π²W)`, the horizontal edges
`2·(2240/A)·log⁹T·x^a/T²·|a−σ₀|`, and the vertical edge
`M_edge·x^{σ₀}·π/σ₀` for
`M_edge = max (M₀ + (1−σ₀)⁻¹) ((2240/A)·log⁹T)`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- **The master Perron error bound** for the smoothed Chebyshev sum. -/
theorem exists_smoothed_chebyshev_error_bound :
    ∃ δ₀ M₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ 0 ≤ M₀ ∧
      ∀ x a W σ₀ Medge : ℝ, 1 ≤ x → 1 < a → a ≤ 2 →
        9 ≤ 2 * Real.pi * W →
        a ≤ 1 + zetaLowerA
          / (2 * Real.log (2 * Real.pi * W) ^ 9) →
        σ₀ = 1 - min δ₀ (zetaLowerA
          / (2 * Real.log (2 * Real.pi * W) ^ 9)) →
        Medge = max (M₀ + (1 - σ₀)⁻¹)
          (2240 / zetaLowerA * Real.log (2 * Real.pi * W) ^ 9) →
        ‖(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
            * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)) - (x : ℂ)‖
          ≤ 2 * (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2 * W))
            + (2 * Real.pi)⁻¹ * (Medge * x ^ σ₀ * (Real.pi / σ₀)
              + 2 * (2240 / zetaLowerA
                  * Real.log (2 * Real.pi * W) ^ 9
                * x ^ a / (2 * Real.pi * W) ^ 2 * |a - σ₀|)) := by
  obtain ⟨δ₀, M₀, hδ0, hδ8, hM0, hmargin, hlow⟩ :=
    exists_low_height_logDeriv_bound
  refine ⟨δ₀, M₀, hδ0, hδ8, hM0, ?_⟩
  intro x a W σ₀ Medge hx1 ha1 ha2 hT9 haA hσ₀def hMedge
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hW0 : (0 : ℝ) < W := by nlinarith
  have hT1 : (1 : ℝ) < 2 * Real.pi * W := by linarith
  have hlogT0 : (0 : ℝ) < Real.log (2 * Real.pi * W) :=
    Real.log_pos hT1
  have hlogT9 : (0 : ℝ) < Real.log (2 * Real.pi * W) ^ 9 := by
    positivity
  have hmin0 : (0 : ℝ) < min δ₀ (zetaLowerA
      / (2 * Real.log (2 * Real.pi * W) ^ 9)) :=
    lt_min hδ0 (by positivity)
  have hminδ : min δ₀ (zetaLowerA
      / (2 * Real.log (2 * Real.pi * W) ^ 9)) ≤ δ₀ := min_le_left _ _
  have hminA : min δ₀ (zetaLowerA
      / (2 * Real.log (2 * Real.pi * W) ^ 9))
      ≤ zetaLowerA / (2 * Real.log (2 * Real.pi * W) ^ 9) :=
    min_le_right _ _
  have hσ₀pos : (0 : ℝ) < σ₀ := by
    rw [hσ₀def]
    have : min δ₀ (zetaLowerA
        / (2 * Real.log (2 * Real.pi * W) ^ 9)) ≤ 1 / 8 :=
      le_trans hminδ hδ8
    linarith
  have hσ₀lt1 : σ₀ < 1 := by
    rw [hσ₀def]
    linarith
  have hσ₀δ : 1 - δ₀ ≤ σ₀ := by
    rw [hσ₀def]
    linarith
  have hσ₀A : 1 - zetaLowerA
      / (2 * Real.log (2 * Real.pi * W) ^ 9) ≤ σ₀ := by
    rw [hσ₀def]
    linarith
  have hσ₀a : σ₀ ≤ a := by linarith
  have h1σ₀ : 1 - σ₀ = min δ₀ (zetaLowerA
      / (2 * Real.log (2 * Real.pi * W) ^ 9)) := by
    rw [hσ₀def]
    ring
  -- the constant relation `16·A = C`
  have hAC : 16 * zetaLowerA = zetaZeroFreeC := by
    rw [zetaLowerA, zetaZeroFreeC]
    norm_num
  -- zero-freeness on the rectangle
  have hzf : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ a →
      |s.im| ≤ 2 * Real.pi * W → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s h1 h2 h3 h4
    rcases le_or_gt |s.im| 9 with h9 | h9
    · exact hmargin s (by linarith) h9 h4
    · rcases le_or_gt s.re 1 with hre1 | hre1
      · rw [← Complex.re_add_im s]
        apply riemannZeta_ne_zero_of_re_gt_one_sub
          (by linarith : 9 ≤ |s.im|)
        have hlogy0 : (0 : ℝ) < Real.log |s.im| :=
          Real.log_pos (by linarith)
        have hmono : Real.log |s.im| ≤ Real.log (2 * Real.pi * W) :=
          Real.log_le_log (by linarith) h3
        have hpow : Real.log |s.im| ^ 9
            ≤ Real.log (2 * Real.pi * W) ^ 9 :=
          pow_le_pow_left₀ hlogy0.le hmono 9
        have hkey : zetaLowerA
            / (2 * Real.log (2 * Real.pi * W) ^ 9)
            < zetaZeroFreeC / Real.log |s.im| ^ 9 := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos hlogy0 9, hpow, hA0]
        linarith [hσ₀A]
      · exact riemannZeta_ne_zero_of_one_le_re hre1.le
  -- the assembly identity
  have hasm := smoothed_chebyshev_contour_assembly hx0 ha1 ha2
    hσ₀pos hσ₀lt1 hW0 hzf
  -- abbreviate the five integrals
  set I1 : ℂ := ∫ w in Set.Iic (-W),
    - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
    * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) with hI1
  set I2 : ℂ := ∫ w in Set.Ioi W,
    - deriv riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / riemannZeta ((a : ℂ) + 2 * Real.pi * w * Complex.I)
    * ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I)
      / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) with hI2
  set Bv : ℂ := ∫ t in σ₀..a,
    - deriv riemannZeta ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
      / riemannZeta ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
    * ((x : ℂ) ^ ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I)
      / ((t : ℂ)
        + ((-(2 * Real.pi * W) : ℝ) : ℂ) * Complex.I) ^ 2) with hBv
  set Tv : ℂ := ∫ t in σ₀..a,
    - deriv riemannZeta ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
      / riemannZeta ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
    * ((x : ℂ) ^ ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I)
      / ((t : ℂ)
        + ((2 * Real.pi * W : ℝ) : ℂ) * Complex.I) ^ 2) with hTv
  set Lv : ℂ := ∫ y in (-(2 * Real.pi * W))..(2 * Real.pi * W),
    - deriv riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
      / riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
    * ((x : ℂ) ^ ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
      / ((σ₀ : ℂ) + (y : ℂ) * Complex.I) ^ 2) with hLv
  rw [hasm]
  have hcancel : (x : ℂ) + (I1 + I2)
      + (2 * Real.pi)⁻¹ • (Complex.I * (Bv - Tv) + Lv) - (x : ℂ)
      = (I1 + I2)
        + (2 * Real.pi)⁻¹ • (Complex.I * (Bv - Tv) + Lv) := by
    abel
  rw [hcancel]
  -- individual bounds
  have hIic := norm_integral_perron_tail_Iic hx0 ha1 ha2 hW0
  have hIoi := norm_integral_perron_tail_Ioi hx0 ha1 ha2 hW0
  have hMh0 : (0 : ℝ) ≤ 2240 / zetaLowerA
      * Real.log (2 * Real.pi * W) ^ 9 := by positivity
  have hMe0 : (0 : ℝ) ≤ Medge := by
    rw [hMedge]
    exact le_trans hMh0 (le_max_right _ _)
  -- horizontal-edge sups
  have hhsup : ∀ c : ℝ, |c| = 2 * Real.pi * W →
      ∀ t : ℝ, t ∈ Set.Ioc σ₀ a →
      ‖deriv riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)
        / riemannZeta ((t : ℂ) + (c : ℂ) * Complex.I)‖
      ≤ 2240 / zetaLowerA * Real.log (2 * Real.pi * W) ^ 9 := by
    intro c hc t ht
    apply norm_zeta_logDeriv_le_strip_range hT9
      (by rw [hc]; linarith) (by rw [hc])
    · linarith [ht.1.le, hσ₀A]
    · linarith [ht.2, haA]
  have hBb := norm_perron_horizontal_edge_le
    (c := -(2 * Real.pi * W)) hx1 hσ₀a
    (by intro h; nlinarith [neg_eq_zero.1 h]) hMh0
    (hhsup (-(2 * Real.pi * W))
      (by rw [abs_neg, abs_of_pos (by linarith)]))
  have hTb := norm_perron_horizontal_edge_le
    (c := 2 * Real.pi * W) hx1 hσ₀a
    (by positivity) hMh0
    (hhsup (2 * Real.pi * W) (abs_of_pos (by linarith)))
  -- left-edge sup
  have hlsup : ∀ y : ℝ, y ∈ Set.Ioc (-(2 * Real.pi * W))
      (2 * Real.pi * W) →
      ‖deriv riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Medge := by
    intro y hy
    have hyabs : |y| ≤ 2 * Real.pi * W :=
      abs_le.2 ⟨hy.1.le, hy.2⟩
    have hre : ((σ₀ : ℂ) + (y : ℂ) * Complex.I).re = σ₀ := by simp
    have him : ((σ₀ : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rcases le_or_gt |y| 9 with h9 | h9
    · have hb := hlow ((σ₀ : ℂ) + (y : ℂ) * Complex.I)
        (by rw [hre]; exact hσ₀δ) (by rw [hre]; exact hσ₀lt1)
        (by rw [him]; exact h9)
      rw [hre] at hb
      rw [hMedge]
      exact le_trans hb (le_max_left _ _)
    · have hApos : (0 : ℝ) < zetaLowerA
          / (2 * Real.log (2 * Real.pi * W) ^ 9) := by positivity
      have hb := norm_zeta_logDeriv_le_strip_range hT9 h9.le
        hyabs (σ := σ₀) (by linarith [hσ₀A])
        (by linarith [hσ₀lt1.le, hApos])
      rw [hMedge]
      exact le_trans hb (le_max_right _ _)
  have hLb := norm_perron_left_edge_le hx0 hσ₀pos
    (by linarith : (0 : ℝ) ≤ 2 * Real.pi * W) hMe0 hlsup
  -- assemble the norms
  have hsmul : ‖(2 * Real.pi)⁻¹ •
      (Complex.I * (Bv - Tv) + Lv)‖
      = (2 * Real.pi)⁻¹ * ‖Complex.I * (Bv - Tv) + Lv‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hedge : ‖Complex.I * (Bv - Tv) + Lv‖
      ≤ (‖Bv‖ + ‖Tv‖) + ‖Lv‖ := by
    calc ‖Complex.I * (Bv - Tv) + Lv‖
        ≤ ‖Complex.I * (Bv - Tv)‖ + ‖Lv‖ := norm_add_le _ _
      _ = ‖Bv - Tv‖ + ‖Lv‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ (‖Bv‖ + ‖Tv‖) + ‖Lv‖ := by
          have := norm_sub_le Bv Tv
          linarith
  have hBb2 : ‖Bv‖ ≤ 2240 / zetaLowerA
      * Real.log (2 * Real.pi * W) ^ 9
      * x ^ a / (2 * Real.pi * W) ^ 2 * |a - σ₀| := by
    calc ‖Bv‖ ≤ 2240 / zetaLowerA
          * Real.log (2 * Real.pi * W) ^ 9 * x ^ a
          / (-(2 * Real.pi * W)) ^ 2 * |a - σ₀| := hBb
      _ = 2240 / zetaLowerA * Real.log (2 * Real.pi * W) ^ 9
          * x ^ a / (2 * Real.pi * W) ^ 2 * |a - σ₀| := by
          rw [show (-(2 * Real.pi * W)) ^ 2 = (2 * Real.pi * W) ^ 2
            from by ring]
  calc ‖(I1 + I2)
        + (2 * Real.pi)⁻¹ • (Complex.I * (Bv - Tv) + Lv)‖
      ≤ ‖I1 + I2‖
        + ‖(2 * Real.pi)⁻¹ • (Complex.I * (Bv - Tv) + Lv)‖ :=
        norm_add_le _ _
    _ ≤ (‖I1‖ + ‖I2‖)
        + (2 * Real.pi)⁻¹ * ((‖Bv‖ + ‖Tv‖) + ‖Lv‖) := by
        rw [hsmul]
        exact add_le_add (norm_add_le _ _)
          (mul_le_mul_of_nonneg_left hedge (by positivity))
    _ ≤ 2 * (8 / (a - 1) ^ 2 * x ^ a / (4 * Real.pi ^ 2 * W))
        + (2 * Real.pi)⁻¹ * (Medge * x ^ σ₀ * (Real.pi / σ₀)
          + 2 * (2240 / zetaLowerA
              * Real.log (2 * Real.pi * W) ^ 9
            * x ^ a / (2 * Real.pi * W) ^ 2 * |a - σ₀|)) := by
        have h6 : (‖Bv‖ + ‖Tv‖) + ‖Lv‖
            ≤ Medge * x ^ σ₀ * (Real.pi / σ₀)
              + 2 * (2240 / zetaLowerA
                  * Real.log (2 * Real.pi * W) ^ 9
                * x ^ a / (2 * Real.pi * W) ^ 2 * |a - σ₀|) := by
          linarith [hBb2, hTb, hLb]
        have h7 : ‖I1‖ + ‖I2‖
            ≤ 2 * (8 / (a - 1) ^ 2 * x ^ a
              / (4 * Real.pi ^ 2 * W)) := by
          linarith [hIic, hIoi]
        have h8 := mul_le_mul_of_nonneg_left h6
          (by positivity : (0 : ℝ) ≤ (2 * Real.pi)⁻¹)
        linarith

end RHTower
