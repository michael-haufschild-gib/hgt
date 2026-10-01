import GaloisForLFunctions.RHTower.DegreeThreeHankelTwistSymbol
import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# Boundedness of the twist symbol on `Re w = 3/2`

On the line `w = 3/2 + it` the twist symbol reduces, via Gamma conjugation and `Γ(z + 1) = zΓ(z)`,
to `|Γ(z)|³ |z| / |Γ(z + 1/3)|³` with `z = 1/12 + it/6`. The sharp vertical Gamma ratio
`|Γ(1/12 + iy)| ≤ y^{-1/3} e^{2/y} |Γ(5/12 + iy)|` (`y ≥ 4`) bounds it by `2e²` for `|t| ≥ 24`,
and continuity covers `|t| ≤ 24`. Hence `κ = sup_t |v(3/2 + it)|` is finite.
-/

namespace RHTower.DegreeThreeHankel

open Complex

private lemma norm_Gamma_conj_eq (z : ℂ) : ‖Gamma ((starRingEnd ℂ) z)‖ = ‖Gamma z‖ := by
  rw [Gamma_conj, Complex.norm_conj]

/-- Norm of the twist symbol on `Re w = 3/2` as a Gamma ratio at `z = 1/12 + it/6`. -/
theorem norm_twistSymbol_three_halves (t : ℝ) :
    ‖twistSymbol (3 / 2 + t * I)‖ =
      ‖Gamma (1 / 12 + t / 6 * I)‖ ^ 3 * ‖(1 / 12 + t / 6 * I : ℂ)‖ /
        ‖Gamma (1 / 12 + t / 6 * I + 1 / 3)‖ ^ 3 := by
  set z : ℂ := 1 / 12 + t / 6 * I with hz
  have hzre : z.re = 1 / 12 := by rw [hz]; simp
  have a1 : (2 - (3 / 2 + t * I)) / 6 = (starRingEnd ℂ) z := by
    rw [hz]
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have a2 : (starRingEnd ℂ) z + 1 / 3 = (starRingEnd ℂ) (z + 1 / 3) := by
    simp only [map_add, map_div₀, map_one, map_ofNat]
  have a3 : (starRingEnd ℂ) z + 2 / 3 = (starRingEnd ℂ) (z + 2 / 3) := by
    simp only [map_add, map_div₀, map_ofNat]
  have b1 : (1 + (3 / 2 + t * I)) / 6 + 1 / 3 = z + 2 / 3 := by rw [hz]; ring
  have b2 : (1 + (3 / 2 + t * I)) / 6 + 2 / 3 = z + 1 := by rw [hz]; ring
  have b3 : (1 + (3 / 2 + t * I)) / 6 = z + 1 / 3 := by rw [hz]; ring
  have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; norm_num at hzre
  have g2 : Gamma (z + 2 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [add_re, hzre]; norm_num)
  have g1 : Gamma (z + 1 / 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [add_re, hzre]; norm_num)
  unfold twistSymbol
  rw [a1, a2, a3, b1, b2, b3, Gamma_add_one z hz0]
  simp only [norm_mul, norm_pow, norm_inv, norm_Gamma_conj_eq]
  have n2 : ‖Gamma (z + 2 / 3)‖ ≠ 0 := norm_ne_zero_iff.mpr g2
  have key : ‖Gamma (z + 2 / 3)‖ * ‖Gamma (z + 2 / 3)‖⁻¹ = 1 := mul_inv_cancel₀ n2
  linear_combination (‖Gamma z‖ ^ 3 * ‖z‖ * ‖Gamma (z + 1 / 3)‖⁻¹ ^ 3) * key

private lemma norm_Gamma_vertical_abs (x t : ℝ) :
    ‖Gamma ((x : ℂ) + (t : ℂ) * I)‖ = ‖Gamma ((x : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, ← norm_Gamma_conj_eq]
    congr 2
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, ofReal_neg]
    ring

/-- For `|t| ≥ 24` the twist symbol on `Re w = 3/2` is at most `2e²` in norm. -/
theorem norm_twistSymbol_three_halves_le_of_large {t : ℝ} (ht : 24 ≤ |t|) :
    ‖twistSymbol (3 / 2 + t * I)‖ ≤ 2 * Real.exp 2 := by
  set y : ℝ := |t / 6| with hy
  have hy4 : 4 ≤ y := by rw [hy, abs_div]; norm_num; linarith
  have hy0 : 0 < y := by linarith
  have e1 : (1 / 12 + t / 6 * I : ℂ) = ((1 / 12 : ℝ) : ℂ) + ((t / 6 : ℝ) : ℂ) * I := by push_cast; ring
  have e5 : (1 / 12 + t / 6 * I + 1 / 3 : ℂ) = ((5 / 12 : ℝ) : ℂ) + ((t / 6 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [norm_twistSymbol_three_halves, e5, e1, norm_Gamma_vertical_abs, norm_Gamma_vertical_abs (5 / 12),
    ← hy]
  have hb := RHTower.norm_Gamma_vertical_le_rpow_mul (a := 1 / 12) (b := 5 / 12) (y := y)
    (by norm_num) (by norm_num) hy4
  set G1 := ‖Gamma (((1 / 12 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hG1
  set G5 := ‖Gamma (((5 / 12 : ℝ) : ℂ) + (y : ℂ) * I)‖ with hG5
  have hG5pos : 0 < G5 := by
    rw [hG5]; apply norm_pos_iff.mpr; apply Gamma_ne_zero_of_re_pos; simp
  set c : ℝ := y ^ ((1 / 12 : ℝ) - 5 / 12) * Real.exp (6 * (5 / 12 - 1 / 12) / y) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc3 : c ^ 3 = y⁻¹ * Real.exp (6 / y) := by
    rw [hc, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.exp_nat_mul]
    norm_num
    rw [Real.rpow_neg_one, show (3 : ℝ) * (2 / y) = 6 / y by ring]
  have hN : ‖((1 / 12 : ℝ) : ℂ) + ((t / 6 : ℝ) : ℂ) * I‖ ≤ 1 / 12 + y := by
    calc _ ≤ ‖((1 / 12 : ℝ) : ℂ)‖ + ‖((t / 6 : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 12 + y := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, hy]
        simp [abs_div]
  have hG1le : G1 ≤ c * G5 := hb
  have hG1nn : 0 ≤ G1 := norm_nonneg _
  have hpow : G1 ^ 3 ≤ c ^ 3 * G5 ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hG1nn hG1le 3
  have hexp : Real.exp (6 / y) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr; rw [div_le_iff₀ hy0]; linarith
  have hratio : y⁻¹ * (1 / 12 + y) ≤ 2 := by
    rw [mul_add, inv_mul_cancel₀ hy0.ne']
    have : y⁻¹ * (1 / 12) ≤ 1 := by
      rw [inv_mul_le_iff₀ hy0]; linarith
    linarith
  calc G1 ^ 3 * ‖((1 / 12 : ℝ) : ℂ) + ((t / 6 : ℝ) : ℂ) * I‖ / G5 ^ 3
      ≤ c ^ 3 * G5 ^ 3 * (1 / 12 + y) / G5 ^ 3 := by
        gcongr
    _ = y⁻¹ * (1 / 12 + y) * Real.exp (6 / y) := by
        rw [hc3]; field_simp
    _ ≤ 2 * Real.exp 2 := by
        apply mul_le_mul hratio hexp (Real.exp_pos _).le (by norm_num)

/-- The twist symbol is bounded on the line `Re w = 3/2`. -/
theorem exists_bound_twistSymbol_three_halves :
    ∃ C : ℝ, ∀ t : ℝ, ‖twistSymbol (3 / 2 + t * I)‖ ≤ C := by
  have hcont : Continuous fun t : ℝ => twistSymbol (3 / 2 + t * I) := by
    have hs : ∀ t : ℝ, (3 / 2 + t * I : ℂ) ∈ {w : ℂ | -3 < w.re ∧ w.re < 2} := by
      intro t; simp only [Set.mem_setOf_eq, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
      norm_num
    exact differentiableOn_twistSymbol.continuousOn.comp_continuous (by fun_prop) hs
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-24 : ℝ)) (b := 24)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ (2 * Real.exp 2), fun t => ?_⟩
  rcases le_or_gt 24 |t| with h | h
  · exact le_max_of_le_right (norm_twistSymbol_three_halves_le_of_large h)
  · exact le_max_of_le_left (hC₀ t (abs_le.mp h.le))

end RHTower.DegreeThreeHankel
