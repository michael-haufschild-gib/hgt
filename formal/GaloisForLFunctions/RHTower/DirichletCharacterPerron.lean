import GaloisForLFunctions.RHTower.DirichletLLogDerivativeStrip
import GaloisForLFunctions.RHTower.PerronVonMangoldtSwap
import GaloisForLFunctions.RHTower.PerronRectangleResidue

/-!
# Actual character Perron identity and constructed zero-free rectangles

The signed tent sum for chi(n)*Lambda(n) equals the integral of the actual
negative logarithmic derivative. Absolute integral summability is obtained from
the existing scalar von Mangoldt majorant, while the character coefficients
remain unchanged in the identity.

For each nonprincipal character, the proved logarithmic strip constructs entire
Perron rectangles crossing Re(s)=1. Their integrands have vanishing boundary
integral and a uniform logarithmic derivative bound. No nonvanishing or analytic
estimate is left as a source premise. Quantitative contour errors and unsmoothing
are further obligations before this yields a prime sum estimate.
-/

noncomputable section
namespace RHTower
open MeasureTheory Set Filter ArithmeticFunction
variable {Q : ℕ} [NeZero Q]

/-- The actual character von Mangoldt series on its half-plane of absolute convergence. -/
theorem LSeries_character_vonMangoldt_eq (χ : DirichletCharacter ℂ Q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- Exact signed character tent sum equals the actual logarithmic derivative Perron integral. -/
theorem smoothed_character_vonMangoldt_eq_perron_integral (χ : DirichletCharacter ℂ Q)
    {x a : ℝ} (hx : 0 < x) (ha : 1 < a) :
    ∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
        ((max (Real.log (x / n)) 0 : ℝ) : ℂ) =
      ∫ w : ℝ,
        (-deriv (DirichletCharacter.LFunction χ) ((a : ℂ) + 2 * Real.pi * w * Complex.I) /
            DirichletCharacter.LFunction χ ((a : ℂ) + 2 * Real.pi * w * Complex.I)) *
          ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I) /
            ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)) := by
  let F : ℕ → ℝ → ℂ := fun n w => χ n * perronVonMangoldtTerm a x n w
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hbase : ∀ n : ℕ, Integrable (perronVonMangoldtTerm a x n) := by
    intro n
    exact (integrable_perron_integrand ha0 (Real.log (x / n))).const_mul _
  have hint : ∀ n : ℕ, Integrable (F n) := fun n => (hbase n).const_mul _
  have hsum : Summable (fun n : ℕ => ∫ w : ℝ, ‖F n w‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun w => norm_nonneg _))
      (fun n => ?_) (summable_integral_norm_perronVonMangoldtTerm hx ha)
    apply integral_mono (hint n).norm (hbase n).norm
    intro w
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hkernel : ∀ n : ℕ,
      (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
        ((max (Real.log (x / n)) 0 : ℝ) : ℂ) = ∫ w : ℝ, F n w := by
    intro n
    dsimp only [F, perronVonMangoldtTerm]
    rw [integral_const_mul, integral_const_mul, perron_weighted_kernel ha0]
    ring
  have hseries : ∀ w : ℝ, (∑' n : ℕ, F n w) =
      (-deriv (DirichletCharacter.LFunction χ) ((a : ℂ) + 2 * Real.pi * w * Complex.I) /
          DirichletCharacter.LFunction χ ((a : ℂ) + 2 * Real.pi * w * Complex.I)) *
        ((x : ℂ) ^ ((a : ℂ) + 2 * Real.pi * w * Complex.I) /
          ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)) := by
    intro w
    let s : ℂ := (a : ℂ) + 2 * Real.pi * w * Complex.I
    let K : ℂ := (x : ℂ) ^ s / s ^ (2 : ℕ)
    have hs : 1 < s.re := by dsimp [s]; simpa using ha
    have hterm : ∀ n : ℕ, F n w =
        LSeries.term (fun m : ℕ => χ m * ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n * K := by
      intro n
      dsimp only [F]
      rw [perronVonMangoldtTerm_eq_LSeries_term hx w n]
      change χ n * (LSeries.term (fun m : ℕ =>
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s n * K) = _
      by_cases hn : n = 0
      · subst n
        simp [LSeries.term_def]
      · simp only [LSeries.term_def, hn, ↓reduceIte]
        ring
    change (∑' n : ℕ, F n w) = _ * K
    rw [tsum_congr hterm, tsum_mul_right]
    change LSeries (fun m : ℕ => χ m * ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) s * K = _
    rw [LSeries_character_vonMangoldt_eq χ hs]
  calc
    _ = ∑' n : ℕ, ∫ w : ℝ, F n w := tsum_congr hkernel
    _ = ∫ w : ℝ, ∑' n : ℕ, F n w := integral_tsum_of_summable_integral_norm hint hsum
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hseries)

/-- Actual nonprincipal characters admit pole-free Perron rectangles crossing Re(s)=1.
Both nonvanishing and logarithmic derivative bounds are constructed on the whole
rectangle; neither is an input premise. -/
theorem exists_nonprincipal_character_perron_rectangles
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ c ≤ Real.log 3 ^ (9 : ℕ) / 2 ∧
      ∀ T : ℝ, 0 ≤ T →
      let δ := c / Real.log (3 + T) ^ (9 : ℕ)
      (∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 + δ → |s.im| ≤ T →
        0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          B * Real.log (3 + T) ^ (9 : ℕ)) ∧
      (∀ x : ℝ, 0 < x →
        rectIntegral (fun s : ℂ => -deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s * ((x : ℂ) ^ s / s ^ (2 : ℕ)))
          (((1 - δ : ℝ) : ℂ) + (-T : ℝ) * Complex.I)
          (((1 + δ : ℝ) : ℂ) + (T : ℝ) * Complex.I) = 0) := by
  obtain ⟨c₀, B, hc₀, hB, hstrip⟩ := exists_nonprincipal_character_logDeriv_log_strip hχ
  let A : ℝ := Real.log 3 ^ (9 : ℕ)
  let c := min c₀ (A / 2)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 < A := pow_pos hlog3 _
  have hc : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨c, B, hc, hB, min_le_right _ _, fun T hT => ?_⟩
  let δ := c / Real.log (3 + T) ^ (9 : ℕ)
  have hlogT : 0 < Real.log (3 + T) := Real.log_pos (by linarith)
  have hpowT : 0 < Real.log (3 + T) ^ (9 : ℕ) := by positivity
  have hlog3T : Real.log 3 ≤ Real.log (3 + T) := Real.log_le_log (by norm_num) (by linarith)
  have hApow : A ≤ Real.log (3 + T) ^ (9 : ℕ) := pow_le_pow_left₀ hlog3.le hlog3T 9
  have hδ : 0 < δ := div_pos hc hpowT
  have hδhalf : δ ≤ 1 / 2 := by
    apply (div_le_iff₀ hpowT).mpr
    have hca : c ≤ A / 2 := min_le_right _ _
    linarith
  have hrect : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 + δ → |s.im| ≤ T →
      0 < s.re ∧ DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        B * Real.log (3 + T) ^ (9 : ℕ) := by
    intro s hsl hsu ht
    have hlogs : Real.log (3 + |s.im|) ≤ Real.log (3 + T) :=
      Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith)
    have hlog : 0 < Real.log (3 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hpow := pow_le_pow_left₀ hlog.le hlogs 9
    have hwidth : δ ≤ c₀ / Real.log (3 + |s.im|) ^ (9 : ℕ) :=
      (div_le_div_of_nonneg_right (min_le_left _ _) hpowT.le).trans
        (div_le_div_of_nonneg_left hc₀.le (by positivity) hpow)
    have hsabs : |s.re - 1| ≤ c₀ / Real.log (3 + |s.im|) ^ (9 : ℕ) := by
      apply (abs_le.mpr ⟨by linarith, by linarith⟩ : |s.re - 1| ≤ δ).trans hwidth
    obtain ⟨hz, hb⟩ := hstrip s.re s.im hsabs
    simp only [Complex.re_add_im] at hz hb
    exact ⟨by linarith, hz, hb.trans (mul_le_mul_of_nonneg_left hpow hB.le)⟩
  refine ⟨hrect, fun x hx => ?_⟩
  let z₁ : ℂ := ((1 - δ : ℝ) : ℂ) + (-T : ℝ) * Complex.I
  let z₂ : ℂ := ((1 + δ : ℝ) : ℂ) + (T : ℝ) * Complex.I
  let S : Set ℂ := Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im
  apply rectIntegral_eq_zero_of_analyticOnNhd (U := S) (Set.Subset.refl _)
  intro s hs
  have hscoord := Complex.mem_reProdIm.mp hs
  have hsr : 1 - δ ≤ s.re ∧ s.re ≤ 1 + δ := by
    simpa only [z₁, z₂, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Set.uIcc_of_le (by linarith : 1 - δ ≤ 1 + δ), Set.mem_Icc] using hscoord.1
  have hsi : |s.im| ≤ T := by
    apply abs_le.mpr
    simpa only [z₁, z₂, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
      add_zero, zero_add, Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] using hscoord.2
  obtain ⟨hre, hz, _⟩ := hrect s hsr.1 hsr.2 hsi
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hLa : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun z _ => hL.analyticAt z
  exact (((hLa.deriv s (Set.mem_univ _)).neg.div (hL.analyticAt s) hz).mul
    (analyticOnNhd_perron_kernel hx s hre))

end RHTower
