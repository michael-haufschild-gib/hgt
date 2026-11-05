import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleModel

/-!
# The saddle error of the Jensen polynomials of `Ξ` is small

With `a₀ = a(τ₁)`, `(a₀ − ix)τ₁ = d`, `A = Re a₀`, `ρ = ‖τ₁‖`, `r = Re τ₁`: `A ρ² = d r`, and for `A ≥ 8000`, `r ≥ 400` the defect of the
exact saddle identity has `‖ε‖ ≤ 1/2`.

On the half-circle, `Q = Y Z` with `Z = ζ(1/2 + τ)` and `‖Y − 1‖ ≤ e^{6ρφ²} − 1` (Grönwall). Near the saddle (`Re τ ≥ 200`) `Z` is within
`1/1000` of `1`. Elsewhere `|φ| ≥ r/(2ρ)`, and the Gaussian decay `e^{−d r²/(8π²ρ²)} = e^{−A r/(8π²)}` beats the polynomial bound `‖Z‖ ≤ 5ρ²`. On the
left half-circle `cos φ ≤ |sin θ₁| ≤ 1 − cos²θ₁/2` with `cos θ₁ = r/ρ`. The normalization is `d! e^d/d^d ≤ e√d`.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

theorem one_sub_cos_ge {φ : ℝ} (h : |φ| ≤ π) : 2 / π ^ 2 * φ ^ 2 ≤ 1 - Real.cos φ := by
  have hπ := Real.pi_pos
  set u := |φ| / 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ π / 2 := by rw [hu]; linarith
  have hs := Real.mul_le_sin hu0 hu1
  have hc : Real.cos φ = 1 - 2 * Real.sin u ^ 2 := by
    rw [← Real.cos_abs φ, show |φ| = 2 * u by rw [hu]; ring, Real.cos_two_mul, Real.cos_sq']
    ring
  have hs2 : (2 / π * u) ^ 2 ≤ Real.sin u ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have hφ : φ ^ 2 = 4 * u ^ 2 := by
    rw [hu, div_pow, sq_abs]
    ring
  rw [hc, hφ]
  have : (2 / π * u) ^ 2 = 4 / π ^ 2 * u ^ 2 := by
    field_simp
    ring
  rw [this] at hs2
  have e : 2 / π ^ 2 * (4 * u ^ 2) = 2 * (4 / π ^ 2 * u ^ 2) := by ring
  rw [e]
  linarith

theorem factorial_le_stirling {d : ℕ} (hd : 0 < d) :
    (d.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt d * (d / Real.exp 1) ^ d := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le (d - 1))
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Nat.sub_add_cancel hd] at hanti
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hanti
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpow : 0 < ((d : ℝ) / Real.exp 1) ^ d := by positivity
  have hsq2 : Real.sqrt (2 * d) = Real.sqrt 2 * Real.sqrt d := Real.sqrt_mul (by norm_num) _
  have hs2 : 0 < Real.sqrt 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hs2, hsq2] at hanti
  have : (d.factorial : ℝ) * Real.sqrt 2 ≤ (Real.exp 1 * Real.sqrt d * (d / Real.exp 1) ^ d) * Real.sqrt 2 := by
    calc _ ≤ Real.exp 1 * (Real.sqrt 2 * Real.sqrt d * ((d : ℝ) / Real.exp 1) ^ d) := hanti
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hs2

/-- `A ρ² = d r`. -/
theorem re_saddle_identity {d : ℕ} {x : ℝ} {a₀ τ₁ : ℂ} (hs : (a₀ - I * x) * τ₁ = d) :
    a₀.re * ‖τ₁‖ ^ 2 = d * τ₁.re := by
  have h1 : (a₀ - I * x) * (τ₁ * (starRingEnd ℂ) τ₁) = d * (starRingEnd ℂ) τ₁ := by
    rw [← mul_assoc, hs]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 := congrArg Complex.re h1
  simp only [mul_re, sub_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_zero,
    natCast_re, natCast_im, conj_re, conj_im] at h2
  simpa using h2

theorem norm_saddle_identity {d : ℕ} {x : ℝ} {a₀ τ₁ : ℂ} (hs : (a₀ - I * x) * τ₁ = d) :
    ‖a₀ - I * x‖ * ‖τ₁‖ = d := by
  rw [← norm_mul, hs, Complex.norm_natCast]

/-- `Q = Y Z`. -/
theorem saddleRatio_eq {τ₁ : ℂ} {φ : ℝ} (hre : 0 ≤ (τ₁ * Complex.exp (φ * I)).re)
    (hne : τ₁ * Complex.exp (φ * I) ≠ 1 / 2) :
    saddleRatio (gammaSlope τ₁) τ₁ φ =
      (gammaFactor (τ₁ * Complex.exp (φ * I)) *
        Complex.exp (-(gammaSlope τ₁ * τ₁ * (Complex.exp (φ * I) - 1))) / gammaFactor τ₁) *
        riemannZeta (1 / 2 + τ₁ * Complex.exp (φ * I)) := by
  rw [saddleRatio, xiCentered, xi_half_add_eq hre hne]
  ring

/-! ### Real inequalities for the weight -/

theorem gauss_core {α φ : ℝ} (hα : 0 < α) :
    φ ^ 2 * Real.exp (-(α * φ ^ 2)) ≤ 2 / α * Real.exp (-(α / 2 * φ ^ 2)) := by
  have h1 : α / 2 * φ ^ 2 ≤ Real.exp (α / 2 * φ ^ 2) := by
    have := Real.add_one_le_exp (α / 2 * φ ^ 2)
    linarith
  have h2 : Real.exp (-(α * φ ^ 2)) = Real.exp (-(α / 2 * φ ^ 2)) * Real.exp (-(α / 2 * φ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (α / 2 * φ ^ 2) * Real.exp (-(α / 2 * φ ^ 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hp := Real.exp_pos (-(α / 2 * φ ^ 2))
  rw [h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hp.le
  calc φ ^ 2 * Real.exp (-(α / 2 * φ ^ 2)) = 2 / α * (α / 2 * φ ^ 2 * Real.exp (-(α / 2 * φ ^ 2))) := by
        field_simp
    _ ≤ 2 / α * (Real.exp (α / 2 * φ ^ 2) * Real.exp (-(α / 2 * φ ^ 2))) := by
        gcongr
    _ = 2 / α := by rw [h3, mul_one]

theorem exp_sub_one_le_mul_exp {y : ℝ} : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have hpos := Real.exp_pos y
  have h2 : (1 - y) * Real.exp y ≤ 1 := by
    calc (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y := by
          gcongr
          linarith
      _ = 1 := by rw [← Real.exp_add]; simp
  linarith

/-- The weight against the near bound. -/
theorem saddle_near {W N α φ ρ c₁ : ℝ} (hρ : 0 ≤ ρ) (hα : 0 < α) (hyα : 6 * ρ * φ ^ 2 ≤ α * φ ^ 2) (hW0 : 0 ≤ W)
    (hW : W ≤ Real.exp (-(2 * α * φ ^ 2)))
    (hN : N ≤ 2 * (6 * ρ * φ ^ 2 * Real.exp (6 * ρ * φ ^ 2)) + 1 / 1000) (hc₁ : 24 * ρ / α = c₁) :
    W * N ≤ (c₁ + 1 / 1000) * Real.exp (-(α / 2 * φ ^ 2)) := by
  set y := 6 * ρ * φ ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hrhs : 0 ≤ 2 * (y * Real.exp y) + 1 / 1000 := by positivity
  have h1 : W * N ≤ Real.exp (-(2 * α * φ ^ 2)) * (2 * (y * Real.exp y) + 1 / 1000) :=
    (mul_le_mul_of_nonneg_left hN hW0).trans (mul_le_mul_of_nonneg_right hW hrhs)
  have h2 : Real.exp (-(2 * α * φ ^ 2)) * Real.exp y ≤ Real.exp (-(α * φ ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have h3 : Real.exp (-(2 * α * φ ^ 2)) ≤ Real.exp (-(α / 2 * φ ^ 2)) := by
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg φ]
  have h4 := gauss_core (α := α) (φ := φ) hα
  have h5 : 2 * y * (Real.exp (-(2 * α * φ ^ 2)) * Real.exp y) ≤ c₁ * Real.exp (-(α / 2 * φ ^ 2)) := by
    calc _ ≤ 2 * y * Real.exp (-(α * φ ^ 2)) := by gcongr
      _ = 12 * ρ * (φ ^ 2 * Real.exp (-(α * φ ^ 2))) := by rw [hy]; ring
      _ ≤ 12 * ρ * (2 / α * Real.exp (-(α / 2 * φ ^ 2))) := by gcongr
      _ = _ := by rw [← hc₁]; ring
  calc W * N ≤ _ := h1
    _ = 2 * y * (Real.exp (-(2 * α * φ ^ 2)) * Real.exp y) + 1 / 1000 * Real.exp (-(2 * α * φ ^ 2)) := by ring
    _ ≤ c₁ * Real.exp (-(α / 2 * φ ^ 2)) + 1 / 1000 * Real.exp (-(α / 2 * φ ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The weight against the far bound. -/
theorem saddle_far {W N α φ ρ r y : ℝ} (hα : 0 < α) (hyα : y ≤ α * φ ^ 2) (hW0 : 0 ≤ W)
    (hW : W ≤ Real.exp (-(2 * α * φ ^ 2))) (hN : N ≤ 6 * ρ ^ 2 * Real.exp y)
    (hfar : (r / (2 * ρ)) ^ 2 ≤ φ ^ 2) :
    W * N ≤ 6 * ρ ^ 2 * Real.exp (-(α / 2 * (r / (2 * ρ)) ^ 2)) * Real.exp (-(α / 2 * φ ^ 2)) := by
  have hrhs : 0 ≤ 6 * ρ ^ 2 * Real.exp y := by positivity
  have h1 : W * N ≤ Real.exp (-(2 * α * φ ^ 2)) * (6 * ρ ^ 2 * Real.exp y) :=
    (mul_le_mul_of_nonneg_left hN hW0).trans (mul_le_mul_of_nonneg_right hW hrhs)
  have h2 : Real.exp (-(2 * α * φ ^ 2)) * Real.exp y ≤
      Real.exp (-(α / 2 * (r / (2 * ρ)) ^ 2)) * Real.exp (-(α / 2 * φ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h3 : α / 2 * (r / (2 * ρ)) ^ 2 ≤ α / 2 * φ ^ 2 := by gcongr
    nlinarith
  calc W * N ≤ _ := h1
    _ = 6 * ρ ^ 2 * (Real.exp (-(2 * α * φ ^ 2)) * Real.exp y) := by ring
    _ ≤ 6 * ρ ^ 2 * (Real.exp (-(α / 2 * (r / (2 * ρ)) ^ 2)) * Real.exp (-(α / 2 * φ ^ 2))) := by gcongr
    _ = _ := by ring

/-! ### The ratio on the right half-circle -/

theorem norm_zeta_sub_one_le_of_deep {τ : ℂ} (h : 200 ≤ τ.re) :
    ‖riemannZeta (1 / 2 + τ) - 1‖ ≤ 1 / 1000 := by
  have hs12 : (2 : ℝ) + 10 ≤ (1 / 2 + τ).re := by
    simp only [add_re, div_ofNat_re, one_re]
    linarith
  have h1 := norm_riemannZeta_sub_one_le_scaled (m := 10) (by norm_num) hs12
  refine h1.trans ?_
  rw [show (2 : ℝ) ^ (10 : ℝ) = 1024 by norm_num [Real.rpow_natCast]]
  norm_num

theorem norm_mul_sub_one_near {Y Z : ℂ} {y : ℝ} (hy0 : 0 ≤ y) (hY : ‖Y - 1‖ ≤ Real.exp y - 1)
    (hZ : ‖Z - 1‖ ≤ 1 / 1000) : ‖Y * Z - 1‖ ≤ 2 * (y * Real.exp y) + 1 / 1000 := by
  have hZ2 : ‖Z‖ ≤ 2 := by
    have h1 : ‖Z‖ ≤ ‖Z - 1‖ + ‖(1 : ℂ)‖ := by simpa using norm_add_le (Z - 1) 1
    rw [norm_one] at h1
    linarith
  have e : Y * Z - 1 = (Y - 1) * Z + (Z - 1) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hZ)
  rw [norm_mul]
  have hexp1 : 0 ≤ Real.exp y - 1 := by linarith [Real.one_le_exp hy0]
  calc _ ≤ (Real.exp y - 1) * 2 := mul_le_mul hY hZ2 (norm_nonneg _) hexp1
    _ ≤ (y * Real.exp y) * 2 := by
        have := exp_sub_one_le_mul_exp (y := y)
        linarith
    _ = _ := by ring

theorem norm_mul_sub_one_far {Y Z : ℂ} {y ρ : ℝ} (hy0 : 0 ≤ y) (hρ : 1 ≤ ρ) (hY : ‖Y - 1‖ ≤ Real.exp y - 1)
    (hZ : ‖Z‖ ≤ 5 * ρ ^ 2) : ‖Y * Z - 1‖ ≤ 6 * ρ ^ 2 * Real.exp y := by
  have hYn : ‖Y‖ ≤ Real.exp y := by
    have h1 : ‖Y‖ ≤ ‖Y - 1‖ + ‖(1 : ℂ)‖ := by simpa using norm_add_le (Y - 1) 1
    rw [norm_one] at h1
    linarith
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_one]
  have h1 : 1 ≤ Real.exp y := Real.one_le_exp hy0
  have h2 : 1 ≤ ρ ^ 2 := by nlinarith
  have hone : 1 ≤ ρ ^ 2 * Real.exp y := by nlinarith
  have h3 : ‖Y‖ * ‖Z‖ ≤ Real.exp y * (5 * ρ ^ 2) :=
    mul_le_mul hYn hZ (norm_nonneg _) (Real.exp_pos _).le
  nlinarith

/-- Off the deep region the angle is at least `r/(2ρ)`. -/
theorem sq_le_of_shallow {τ₁ : ℂ} (hr : 400 ≤ τ₁.re) {φ : ℝ} (hsh : (τ₁ * Complex.exp (φ * I)).re < 200) :
    (τ₁.re / (2 * ‖τ₁‖)) ^ 2 ≤ φ ^ 2 := by
  have hρ : 0 < ‖τ₁‖ := lt_of_lt_of_le (by linarith) (Complex.re_le_norm τ₁)
  have hτ0 : τ₁ ≠ 0 := norm_pos_iff.1 hρ
  have h1 := Real.abs_cos_sub_cos_le (Complex.arg τ₁) (Complex.arg τ₁ + φ)
  have h2 : Real.cos (Complex.arg τ₁) = τ₁.re / ‖τ₁‖ := Complex.cos_arg hτ0
  have e : |Complex.arg τ₁ - (Complex.arg τ₁ + φ)| = |φ| := by
    rw [show Complex.arg τ₁ - (Complex.arg τ₁ + φ) = -φ by ring, abs_neg]
  rw [e] at h1
  have h3 : Real.cos (Complex.arg τ₁ + φ) = (τ₁ * Complex.exp (φ * I)).re / ‖τ₁‖ := by
    rw [re_mul_exp]
    field_simp
  rw [h2, h3, div_sub_div_same] at h1
  have h4 := (le_abs_self _).trans h1
  rw [div_le_iff₀ hρ] at h4
  have hfar : τ₁.re / (2 * ‖τ₁‖) ≤ |φ| := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [← sq_abs φ]
  exact pow_le_pow_left₀ (by positivity) hfar 2

/-- **The pointwise bound on the right half-circle.** -/
theorem exp_mul_norm_saddleRatio_sub_one_le {d : ℕ} {τ₁ : ℂ} (hr : 400 ≤ τ₁.re)
    (hρα : 6 * ‖τ₁‖ * π ^ 2 ≤ d) {φ : ℝ}
    (hφ : φ ∈ Icc (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁)) :
    Real.exp (d * (Real.cos φ - 1)) * ‖saddleRatio (gammaSlope τ₁) τ₁ φ - 1‖ ≤
      (24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
        6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2)))) *
        Real.exp (-(d / π ^ 2 / 2 * φ ^ 2)) := by
  have hπ := Real.pi_pos
  have hρ0 : 400 ≤ ‖τ₁‖ := hr.trans (Complex.re_le_norm τ₁)
  have hρpos : 0 < ‖τ₁‖ := by linarith
  have hdpos : (0 : ℝ) < d := by
    have : 0 < 6 * ‖τ₁‖ * π ^ 2 := by positivity
    linarith
  have hαpos : 0 < (d : ℝ) / π ^ 2 := by positivity
  have h6 : 6 * ‖τ₁‖ ≤ (d : ℝ) / π ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact hρα
  have hθ' := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith : 0 < τ₁.re)))
  have habs : |φ| ≤ π := by
    rw [abs_le]
    constructor <;> linarith [hφ.1, hφ.2, hθ'.1, hθ'.2]
  have hτn : ‖τ₁ * Complex.exp (φ * I)‖ = ‖τ₁‖ := norm_mul_exp φ
  have hre : 0 ≤ (τ₁ * Complex.exp (φ * I)).re := by
    rw [re_mul_exp]
    refine mul_nonneg hρpos.le (Real.cos_nonneg_of_mem_Icc ?_)
    constructor <;> linarith [hφ.1, hφ.2]
  have hne : τ₁ * Complex.exp (φ * I) ≠ 1 / 2 := fun h => by
    rw [h, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hτn
    linarith
  have hQ := saddleRatio_eq hre hne
  have hYb := norm_gammaRatio_sub_one_le_of_mem (by linarith) (by linarith) hφ
  have hy0 : 0 ≤ 6 * ‖τ₁‖ * φ ^ 2 := by positivity
  have hweight : Real.exp (d * (Real.cos φ - 1)) ≤ Real.exp (-(2 * ((d : ℝ) / π ^ 2) * φ ^ 2)) := by
    apply Real.exp_le_exp.2
    have h := one_sub_cos_ge habs
    have e : 2 * ((d : ℝ) / π ^ 2) * φ ^ 2 = d * (2 / π ^ 2 * φ ^ 2) := by ring
    rw [e]
    nlinarith
  have hyα : 6 * ‖τ₁‖ * φ ^ 2 ≤ (d : ℝ) / π ^ 2 * φ ^ 2 := by gcongr
  have hEpos : 0 ≤ 6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) := by positivity
  have hc₁0 : 0 ≤ 24 * π ^ 2 * ‖τ₁‖ / d := by positivity
  have hG := Real.exp_pos (-((d : ℝ) / π ^ 2 / 2 * φ ^ 2))
  rw [hQ]
  by_cases hdeep : 200 ≤ (τ₁ * Complex.exp (φ * I)).re
  · have hN := norm_mul_sub_one_near hy0 hYb (norm_zeta_sub_one_le_of_deep hdeep)
    have hc₁ : 24 * ‖τ₁‖ / ((d : ℝ) / π ^ 2) = 24 * π ^ 2 * ‖τ₁‖ / d := by
      field_simp
    have := saddle_near hρpos.le hαpos hyα (Real.exp_pos _).le hweight hN hc₁
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hG.le)
    linarith
  · push Not at hdeep
    have hfar := sq_le_of_shallow hr hdeep
    have hZ := norm_zeta_half_add_le hre (by rw [hτn]; linarith)
    rw [hτn] at hZ
    have hN := norm_mul_sub_one_far hy0 (by linarith) hYb hZ
    have := saddle_far hαpos hyα (Real.exp_pos _).le hweight hN hfar
    have hexpo : (d : ℝ) * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2) =
        (d : ℝ) / π ^ 2 / 2 * (τ₁.re / (2 * ‖τ₁‖)) ^ 2 := by
      field_simp
      ring
    rw [hexpo] at hEpos ⊢
    refine this.trans (mul_le_mul_of_nonneg_right ?_ hG.le)
    linarith

/-- On the left half-circle, `cos φ ≤ 1 − (r/ρ)²/2`. -/
theorem cos_le_of_left_half {τ₁ : ℂ} (hr : 0 < τ₁.re) {φ : ℝ}
    (hφ : φ ∈ uIcc (π / 2 - Complex.arg τ₁) (-(π / 2) - Complex.arg τ₁ + 2 * π)) :
    Real.cos φ ≤ 1 - (τ₁.re / ‖τ₁‖) ^ 2 / 2 := by
  have hπ := Real.pi_pos
  have hτ0 : τ₁ ≠ 0 := fun h => by
    rw [h, zero_re] at hr
    exact lt_irrefl _ hr
  set θ := Complex.arg τ₁ with hθ
  have hθb : |θ| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hr)
  have hθ' := abs_lt.1 hθb
  rw [uIcc_of_le (by linarith)] at hφ
  have hc : Real.cos θ = τ₁.re / ‖τ₁‖ := Complex.cos_arg hτ0
  have hcpos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hnonpos : Real.cos (φ + θ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hφ.1]) (by linarith [hφ.2])
  have hexp : Real.cos φ = Real.cos (φ + θ) * Real.cos θ + Real.sin (φ + θ) * Real.sin θ := by
    rw [← Real.cos_sub]
    congr 1
    ring
  have h1 : Real.sin (φ + θ) * Real.sin θ ≤ |Real.sin θ| := by
    calc _ ≤ |Real.sin (φ + θ) * Real.sin θ| := le_abs_self _
      _ = |Real.sin (φ + θ)| * |Real.sin θ| := abs_mul _ _
      _ ≤ 1 * |Real.sin θ| := by gcongr; exact Real.abs_sin_le_one _
      _ = _ := one_mul _
  have h2 : |Real.sin θ| ≤ 1 - Real.cos θ ^ 2 / 2 := by
    have hs := Real.sin_sq_add_cos_sq θ
    have h3 : 0 ≤ 1 - Real.cos θ ^ 2 / 2 := by
      have := Real.cos_sq_le_one θ
      linarith
    apply abs_le_of_sq_le_sq _ h3
    nlinarith [sq_nonneg (Real.cos θ ^ 2)]
  rw [← hc, hexp]
  nlinarith [mul_nonneg (neg_nonneg.2 hnonpos) hcpos]

/-- **The defect of the saddle identity.** -/
theorem norm_saddleError_le {d : ℕ} (hd : 0 < d) {τ₁ : ℂ} (hr : 400 ≤ τ₁.re)
    (hρα : 6 * ‖τ₁‖ * π ^ 2 ≤ d) :
    ‖saddleError d (gammaSlope τ₁) τ₁‖ ≤
      4 * (24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
        6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2)))) +
      Real.exp 1 * Real.sqrt d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) := by
  have hπ := Real.pi_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set c := 24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
    6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) with hc
  have hc0 : 0 ≤ c := by positivity
  set α : ℝ := d / π ^ 2 with hα
  have hαpos : 0 < α := by positivity
  set a := Complex.arg τ₁ with ha
  have hθb : |a| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith))
  have hθ' := abs_lt.1 hθb
  have hle : -(π / 2) - a ≤ π / 2 - a := by linarith
  have hW := continuous_saddleWeight d
  have hQ := continuous_saddleRatio (gammaSlope τ₁) τ₁
  have hgint : Integrable fun φ : ℝ => Real.exp (-(α / 2 * φ ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := α / 2) (by positivity)
  have hgval : ∫ φ : ℝ, Real.exp (-(α / 2 * φ ^ 2)) = Real.sqrt (π / (α / 2)) := by
    simpa using integral_gaussian (α / 2)
  -- the right half-circle
  have hI1 : ‖∫ φ in (-(π / 2) - a)..(π / 2 - a), saddleWeight d φ * (saddleRatio (gammaSlope τ₁) τ₁ φ - 1)‖ ≤
      Real.exp d * (c * Real.sqrt (π / (α / 2))) := by
    have hbound : ∀ φ ∈ Icc (-(π / 2) - a) (π / 2 - a),
        ‖saddleWeight d φ * (saddleRatio (gammaSlope τ₁) τ₁ φ - 1)‖ ≤
          Real.exp d * (c * Real.exp (-(α / 2 * φ ^ 2))) := fun φ hφ => by
      have h := exp_mul_norm_saddleRatio_sub_one_le hr hρα hφ
      rw [norm_mul, norm_saddleWeight]
      have e : Real.exp (d * Real.cos φ) = Real.exp d * Real.exp (d * (Real.cos φ - 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e, mul_assoc]
      exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hle
      (Eventually.of_forall fun φ hφ => hbound φ ⟨hφ.1.le, hφ.2⟩)
      (((hgint.const_mul c).const_mul (Real.exp d)).intervalIntegrable)
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hle, integral_const_mul, integral_const_mul]
    gcongr
    rw [← hgval]
    exact setIntegral_le_integral hgint (Eventually.of_forall fun φ => (Real.exp_pos _).le)
  -- the left half-circle
  have hI2 : ‖∫ φ in (π / 2 - a)..(-(π / 2) - a + 2 * π), saddleWeight d φ‖ ≤
      Real.exp d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) * π := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := π / 2 - a) (b := -(π / 2) - a + 2 * π)
      (f := saddleWeight d) (C := Real.exp d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2))) fun φ hφ => by
        rw [norm_saddleWeight, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have hcos := cos_le_of_left_half (by linarith : 0 < τ₁.re) (uIoc_subset_uIcc hφ)
        nlinarith
    have hlen : |-(π / 2) - a + 2 * π - (π / 2 - a)| = π := by
      rw [show -(π / 2) - a + 2 * π - (π / 2 - a) = π by ring, abs_of_pos hπ]
    rwa [hlen] at h
  have hfac := factorial_le_stirling hd
  have hdpow : (0 : ℝ) < (d : ℝ) ^ d := by positivity
  have hnorm : ‖((d.factorial : ℂ) / (2 * π * (d : ℂ) ^ d))‖ = (d.factorial : ℝ) / (2 * π * (d : ℝ) ^ d) := by
    rw [norm_div, Complex.norm_natCast, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Complex.norm_two, Real.norm_of_nonneg hπ.le]
  have hfacnorm : (d.factorial : ℝ) / (2 * π * (d : ℝ) ^ d) * Real.exp d ≤
      Real.exp 1 * Real.sqrt d / (2 * π) := by
    have he : ((d : ℝ) / Real.exp 1) ^ d * Real.exp d = (d : ℝ) ^ d := by
      rw [div_pow, ← Real.exp_nat_mul, mul_one]
      field_simp
    calc _ = (d.factorial : ℝ) * Real.exp d / (2 * π * (d : ℝ) ^ d) := by ring
      _ ≤ (Real.exp 1 * Real.sqrt d * ((d : ℝ) / Real.exp 1) ^ d) * Real.exp d / (2 * π * (d : ℝ) ^ d) := by
          gcongr
      _ = Real.exp 1 * Real.sqrt d * (((d : ℝ) / Real.exp 1) ^ d * Real.exp d) / (2 * π * (d : ℝ) ^ d) := by ring
      _ = _ := by
          rw [he]
          field_simp
  rw [saddleError, ← ha, norm_mul, hnorm]
  set F := (d.factorial : ℝ) / (2 * π * (d : ℝ) ^ d) with hF
  have hF0 : 0 ≤ F := by positivity
  have hsum := norm_sub_le
    (∫ φ in (-(π / 2) - a)..(π / 2 - a), saddleWeight d φ * (saddleRatio (gammaSlope τ₁) τ₁ φ - 1))
    (∫ φ in (π / 2 - a)..(-(π / 2) - a + 2 * π), saddleWeight d φ)
  have hsqrtα : Real.sqrt d * Real.sqrt (π / (α / 2)) = π * Real.sqrt (2 * π) := by
    rw [← Real.sqrt_mul hdR.le, show (d : ℝ) * (π / (α / 2)) = π ^ 2 * (2 * π) by
      rw [hα]
      field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le]
  have hconst : Real.exp 1 * Real.sqrt (2 * π) / 2 ≤ 4 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.sqrt (2 * π) ≤ 2.6 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have := Real.pi_lt_d2
      norm_num
      linarith
    have h3 : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
    nlinarith
  calc F * ‖_‖ ≤ F * (Real.exp d * (c * Real.sqrt (π / (α / 2))) +
        Real.exp d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) * π) := by
        gcongr
        exact hsum.trans (add_le_add hI1 hI2)
    _ = (F * Real.exp d) * (c * Real.sqrt (π / (α / 2)) + Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) * π) := by ring
    _ ≤ (Real.exp 1 * Real.sqrt d / (2 * π)) *
        (c * Real.sqrt (π / (α / 2)) + Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) * π) := by
        gcongr
    _ = (Real.exp 1 * Real.sqrt (2 * π) / 2) * c +
        Real.exp 1 * Real.sqrt d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) / 2 := by
        have : Real.exp 1 * Real.sqrt d / (2 * π) * (c * Real.sqrt (π / (α / 2))) =
            Real.exp 1 * c / (2 * π) * (Real.sqrt d * Real.sqrt (π / (α / 2))) := by ring
        rw [mul_add, this, hsqrtα]
        field_simp
    _ ≤ 4 * c + Real.exp 1 * Real.sqrt d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) := by
        have : 0 ≤ Real.exp 1 * Real.sqrt d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) := by positivity
        gcongr
        linarith

/-- **The saddle defect is at most `1/2`** once `Re a₀ ≥ 8000` and `Re τ₁ ≥ 400`. -/
theorem norm_saddleError_le_half {d : ℕ} (hd : 0 < d) {x : ℝ} {τ₁ : ℂ}
    (hs : (gammaSlope τ₁ - I * x) * τ₁ = d) (hA : 8000 ≤ (gammaSlope τ₁).re) (hr : 400 ≤ τ₁.re) :
    ‖saddleError d (gammaSlope τ₁) τ₁‖ ≤ 1 / 2 := by
  have hπ := Real.pi_pos
  have hπ2 : π ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2
    nlinarith
  have hπ2' : 9 ≤ π ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  set A := (gammaSlope τ₁).re with hAdef
  set ρ := ‖τ₁‖ with hρ
  set r := τ₁.re with hrdef
  have hρr : r ≤ ρ := Complex.re_le_norm τ₁
  have hρpos : 0 < ρ := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hid : A * ρ ^ 2 = d * r := re_saddle_identity hs
  have hnid := norm_saddle_identity hs
  have hAle : A ≤ ‖gammaSlope τ₁ - I * x‖ := by
    have h := Complex.re_le_norm (gammaSlope τ₁ - I * x)
    simpa using h
  have hρd : ρ / d ≤ 1 / A := by
    rw [div_le_div_iff₀ hdR (by linarith)]
    rw [← hnid]
    nlinarith
  have hρα : 6 * ρ * π ^ 2 ≤ d := by
    have h1 : ρ * A ≤ d := by
      rw [← hnid]
      nlinarith
    nlinarith
  have hmain := norm_saddleError_le hd hr hρα
  -- `log ρ ≤ 2A + 14`
  have hst := abs_le.1 (abs_re_gammaSlope_sub_le (τ := τ₁) (by linarith))
  have hlogρ : Real.log ρ ≤ 2 * A + 14 := by linarith [hst.1]
  have hρe : ρ ≤ Real.exp (2 * A + 14) := by
    rw [← Real.log_le_iff_le_exp hρpos]
    exact hlogρ
  have hexpo1 : d * r ^ 2 / (8 * π ^ 2 * ρ ^ 2) = A * r / (8 * π ^ 2) := by
    have : d * r ^ 2 = (A * ρ ^ 2) * r := by rw [hid]; ring
    rw [this]
    field_simp
  have hexpo2 : d * (r / ρ) ^ 2 / 2 = A * r / 2 := by
    have : d * r ^ 2 = (A * ρ ^ 2) * r := by rw [hid]; ring
    rw [div_pow, ← mul_div_assoc, this]
    field_simp
  rw [hexpo1, hexpo2] at hmain
  have hAr1 : 5 * A ≤ A * r / (8 * π ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hπ2 (by linarith : (0 : ℝ) ≤ A),
      mul_le_mul_of_nonneg_left hr (by linarith : (0 : ℝ) ≤ A)]
  have hAr2 : 200 * A ≤ A * r / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr (by linarith : (0 : ℝ) ≤ A)]
  have hterm1 : 24 * π ^ 2 * ρ / d ≤ 3 / 100 := by
    calc 24 * π ^ 2 * ρ / d = 24 * π ^ 2 * (ρ / d) := by ring
      _ ≤ 24 * 10 * (1 / 8000) :=
          mul_le_mul (by linarith) (hρd.trans (one_div_le_one_div_of_le (by norm_num) hA))
            (by positivity) (by norm_num)
      _ = 3 / 100 := by norm_num
  have hbig : 1 / 1000 ≥ Real.exp (-(A - 28)) := by
    have h := Real.add_one_le_exp (A - 28)
    rw [Real.exp_neg]
    have hp : 0 < A - 28 + 1 := by linarith
    calc (Real.exp (A - 28))⁻¹ ≤ (A - 28 + 1)⁻¹ := inv_anti₀ hp h
      _ ≤ 1 / 1000 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hterm2 : 6 * ρ ^ 2 * Real.exp (-(A * r / (8 * π ^ 2))) ≤ 6 / 1000 := by
    have h1 : ρ ^ 2 ≤ Real.exp (4 * A + 28) := by
      calc ρ ^ 2 ≤ Real.exp (2 * A + 14) ^ 2 := pow_le_pow_left₀ hρpos.le hρe 2
        _ = _ := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    have h2 : Real.exp (-(A * r / (8 * π ^ 2))) ≤ Real.exp (-(5 * A)) :=
      Real.exp_le_exp.2 (by linarith)
    calc _ ≤ 6 * Real.exp (4 * A + 28) * Real.exp (-(5 * A)) := by gcongr
      _ = 6 * Real.exp (-(A - 28)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ 6 / 1000 := by linarith
  have hterm3 : Real.exp 1 * Real.sqrt d * Real.exp (-(A * r / 2)) ≤ 1 / 1000 := by
    have hdle : (d : ℝ) ≤ A * ρ ^ 2 := by
      have : (d : ℝ) * 1 ≤ d * r := by
        gcongr
        linarith
      linarith
    have hsq : Real.sqrt d ≤ Real.exp A * Real.exp (2 * A + 14) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hA1 : A ≤ Real.exp A := by
        have := Real.add_one_le_exp A
        linarith
      have hA2 : A ≤ Real.exp A ^ 2 := by
        have h1 : 1 ≤ Real.exp A := Real.one_le_exp (by linarith)
        nlinarith
      calc (d : ℝ) ≤ A * ρ ^ 2 := hdle
        _ ≤ Real.exp A ^ 2 * Real.exp (2 * A + 14) ^ 2 := by
            gcongr
        _ = _ := by ring
    have h4 : Real.exp 1 * (Real.exp A * Real.exp (2 * A + 14)) * Real.exp (-(200 * A)) ≤ Real.exp (-(A - 28)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    calc _ ≤ Real.exp 1 * (Real.exp A * Real.exp (2 * A + 14)) * Real.exp (-(200 * A)) := by
          gcongr
      _ ≤ _ := h4.trans hbig
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.norm_saddleError_le_half
