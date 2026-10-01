import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementScale

open Complex MeasureTheory
noncomputable section
namespace RHTower

/-- One deep scale envelope controls every displacement in the full strict strip;
the constant retains no displacement, smoothing or height dependence. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficient_uniform_strip_scale_le :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ d : ℝ, 0 < d → d < 1 / 2 → ∀ x : ℝ, 0 < x → ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDeepCoefficient d tau x n‖ ≤
        D * x ^ (d - 4) * (1 + |tau|) ^ 4 *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨C, hC, hchi⟩ :=
    exists_norm_zetaChi_neg_seven_halves_le
  let K : ℝ := Real.exp 16 * C
  let J : ℝ := ∫ v : ℝ, (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))
  let c : ℝ := 1 / (2 * Real.pi)
  let D : ℝ := c * K * J
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hC0 : 0 ≤ C := hC.le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun v => by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun d hd hdhalf x hx tau n => ?_⟩
  have hden : 1 ≤ |d - 4| := by rw [abs_of_neg (by linarith : d - 4 < 0)]; linarith
  have hsq : (d - 4) ^ 2 ≤ 16 := by nlinarith
  have hfactor : Real.exp ((d - 4) ^ 2) / |d - 4| ≤ Real.exp 16 := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
    exact (Real.exp_le_exp.mpr hsq).trans
      (le_mul_of_one_le_right (Real.exp_pos 16).le hden)
  let a : ℝ := 1 + |tau|
  let b : ℝ := 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  let M : ℝ := K * x ^ (d - 4) * b * a ^ 4
  have hshift : ∀ v : ℝ,
      1 + |tau| + |v| ≤ a * (1 + |v|) := by
    intro v
    dsimp only [a]
    nlinarith [abs_nonneg tau, abs_nonneg v,
      mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
  have hmajor : Integrable (fun v : ℝ =>
      M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2)))) :=
    (integrable_shifted_pow_mul_exp_neg_sq 1 4).const_mul M
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        ∫ v : ℝ, M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      calc
        ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
            K * x ^ (d - 4) * b *
              ((1 + |tau| + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          have h := norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip
            hx hd hdhalf hchi tau n v
          calc
            _ ≤ (((b * x ^ (d - 4) *
                (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) *
                ((1 + |tau| + |v|) ^ 4 * Real.exp (-(v ^ 2))))) := h
            _ ≤ (((b * x ^ (d - 4) * Real.exp 16 * C) *
                ((1 + |tau| + |v|) ^ 4 * Real.exp (-(v ^ 2))))) := by
              gcongr
            _ = _ := by dsimp only [K]; ring
        _ ≤ K * x ^ (d - 4) * b *
            ((a * (1 + |v|)) ^ 4 * Real.exp (-(v ^ 2))) := by
          gcongr
          exact hshift v
        _ = M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          dsimp only [M]
          rw [mul_pow]
          ring
  unfold smoothAFEZetaDisplacedDeepCoefficient
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    c * ‖∫ v : ℝ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ c * ∫ v : ℝ,
          M * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hint hc
    _ = D * x ^ (d - 4) * (1 + |tau|) ^ 4 *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [integral_const_mul]
      dsimp only [D, M, J, a, b]
      ring

end RHTower

