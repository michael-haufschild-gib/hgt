import GaloisForLFunctions.RHTower.ZetaJacksonFourier

/-!
# Products of shifted Jackson windows

The weighted Frobenius norm pairs grid points `k = l + r`, so its grid sums carry the product weights
`W(τ_l + rh) W(τ_l)`.  The product of a shifted Jackson window with itself is again band-limited, with twice the band:

`∫ W(s + a) W(s) e^{−iηs} ds = 0`   for `|η| ≥ 4b`   (`integral_jacksonProduct_mul_cexp_eq_zero`),

because `W(s + a) = ∫ ψ₂(ξ) e^{iξ(s+a)} dξ` with `|ξ| < 2b` and the transform of `W` vanishes at every `|η − ξ| ≥ 2b`.
Hence its grid character sums vanish off the aliases `|jL − y| < 4b` (`hasSum_jacksonProduct_grid_char_eq_zero`).
-/

open Complex MeasureTheory Real Set Filter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b s₀ s₁ : ℝ}

/-- The Jackson window is integrable. -/
theorem integrable_jacksonWindow (hb : 0 < b) (h01 : s₀ ≤ s₁) : Integrable (jacksonWindow b s₀ s₁) := by
  set R : ℝ := 2 * (|s₀| + |s₁| + 1) with hR
  set C : ℝ := (jacksonMass b)⁻¹ * (64 / (3 * b ^ 2)) with hC
  have hC0 : 0 ≤ C := by have := (jacksonMass_pos hb).le; positivity
  have hR1 : 1 ≤ R := by have := abs_nonneg s₀; have := abs_nonneg s₁; linarith
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (R ^ 2 + 1 + 2 * C))
    (continuous_jacksonWindow hb).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  have hpos : 0 < 1 + s ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_or_gt R |s| with hs | hs
  · have hb' := abs_jacksonWindow_le_inv_sq hb h01 hs
    have hs2 : 0 < s ^ 2 := by
      have h0 : 0 < |s| := lt_of_lt_of_le (by linarith) hs
      rw [← sq_abs]; exact pow_pos h0 2
    have h1 : |jacksonWindow b s₀ s₁ s| * s ^ 2 ≤ C := by
      rw [← hC] at hb'; rwa [le_div_iff₀ hs2] at hb'
    have h2 : |jacksonWindow b s₀ s₁ s| ≤ C := by
      have : 1 ≤ s ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith [abs_nonneg (jacksonWindow b s₀ s₁ s)]
    nlinarith [sq_nonneg R, abs_nonneg (jacksonWindow b s₀ s₁ s)]
  · have h1 : |jacksonWindow b s₀ s₁ s| ≤ 1 := by
      rw [abs_of_nonneg (jacksonWindow_nonneg hb h01 s)]; exact jacksonWindow_le_one hb h01 s
    have h2 : s ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg s) hs.le 2
    nlinarith [abs_nonneg (jacksonWindow b s₀ s₁ s)]

/-- **The product of a shifted Jackson window with itself is band-limited to `4b`.** -/
theorem integral_jacksonProduct_mul_cexp_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) (a : ℝ) {η : ℝ}
    (hη : 4 * b ≤ |η|) :
    ∫ s, ((jacksonWindow b s₀ s₁ (s + a) * jacksonWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (-(I * η * s)) = 0 := by
  have hψ := integrable_jacksonPsi (s₀ := s₀) (s₁ := s₁) hb
  have hW := integrable_jacksonWindow hb h01
  set F : ℝ → ℝ → ℂ := fun s ξ => jacksonPsi b s₀ s₁ ξ * cexp (I * ξ * a)
      * (((jacksonWindow b s₀ s₁ s : ℝ) : ℂ) * cexp (-(I * ((η - ξ : ℝ) : ℂ) * s))) with hF
  have hpt : ∀ s : ℝ, ((jacksonWindow b s₀ s₁ (s + a) * jacksonWindow b s₀ s₁ s : ℝ) : ℂ)
      * cexp (-(I * η * s)) = ∫ ξ, F s ξ := by
    intro s
    rw [Complex.ofReal_mul, ← integral_jacksonPsi_mul_cexp hb h01 (s + a), ← integral_mul_const,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF]
    have e : cexp (I * ξ * ((s + a : ℝ) : ℂ)) * cexp (-(I * η * s))
        = cexp (I * ξ * a) * cexp (-(I * ((η - ξ : ℝ) : ℂ) * s)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (jacksonPsi b s₀ s₁ ξ * (jacksonWindow b s₀ s₁ s : ℂ)) * e
  simp_rw [hpt]
  have hnorm : ∀ s ξ, ‖F s ξ‖ = ‖jacksonPsi b s₀ s₁ ξ‖ * |jacksonWindow b s₀ s₁ s| := by
    intro s ξ
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show I * (ξ : ℂ) * (a : ℂ) = ((ξ * a : ℝ) : ℂ) * I by push_cast; ring,
      show -(I * ((η - ξ : ℝ) : ℂ) * (s : ℂ)) = ((-((η - ξ) * s)) : ℝ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
    ring
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry F) := by
      have h1 := continuous_jacksonPsi (s₀ := s₀) (s₁ := s₁) hb
      have h2 := continuous_jacksonWindow (s₀ := s₀) (s₁ := s₁) hb
      simp only [hF]
      fun_prop
    have hmaj : Integrable (fun q : ℝ × ℝ => |jacksonWindow b s₀ s₁ q.1| * ‖jacksonPsi b s₀ s₁ q.2‖)
        (volume.prod volume) := hW.abs.mul_prod hψ.norm
    refine hmaj.mono' hc.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    show ‖F q.1 q.2‖ ≤ |jacksonWindow b s₀ s₁ q.1| * ‖jacksonPsi b s₀ s₁ q.2‖
    rw [hnorm, mul_comm]
  rw [integral_integral_swap hint]
  have h0 : ∀ ξ : ℝ, ∫ s, F s ξ = 0 := by
    intro ξ
    simp only [hF]
    rw [integral_const_mul]
    by_cases hξ : 2 * b ≤ |ξ|
    · rw [jacksonPsi_eq_zero hb hξ]; simp
    · push Not at hξ
      have : 2 * b ≤ |η - ξ| := by have := abs_sub_abs_le_abs_sub η ξ; linarith
      rw [integral_jacksonWindow_mul_cexp_eq_zero hb h01 this, mul_zero]
  simp_rw [h0, integral_zero]

/-- **Grid character sums of the product window vanish off the aliases.** -/
theorem hasSum_jacksonProduct_grid_char_eq_zero (hb : 0 < b) (h01 : s₀ ≤ s₁) (a : ℝ) {L : ℝ}
    (hL : 0 < L) (T y : ℝ) (hy : ∀ j : ℤ, 4 * b ≤ |j * L - y|) :
    HasSum (fun k : ℤ => ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L) + a)
        * jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) : ℝ) : ℂ)
      * cexp (I * y * ((T + k * (2 * π / L) : ℝ) : ℂ))) 0 := by
  have hc : Continuous fun s => jacksonWindow b s₀ s₁ (s + a) * jacksonWindow b s₀ s₁ s :=
    ((continuous_jacksonWindow hb).comp (continuous_add_const a)).mul (continuous_jacksonWindow hb)
  have hk := (jacksonMass_pos hb).le
  exact hasSum_grid_char_eq_zero_of_window (W := fun s => jacksonWindow b s₀ s₁ (s + a)
      * jacksonWindow b s₀ s₁ s) hc (C := (jacksonMass b)⁻¹ * (64 / (3 * b ^ 2))) (by positivity)
    (fun s hs => by
      rw [abs_mul]
      have h1 : |jacksonWindow b s₀ s₁ (s + a)| ≤ 1 := by
        rw [abs_of_nonneg (jacksonWindow_nonneg hb h01 _)]; exact jacksonWindow_le_one hb h01 _
      exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans (abs_jacksonWindow_le_inv_sq hb h01 hs))
    (fun η hη => integral_jacksonProduct_mul_cexp_eq_zero hb h01 a hη) hL T y hy

end FejerWeight

end RHTower
