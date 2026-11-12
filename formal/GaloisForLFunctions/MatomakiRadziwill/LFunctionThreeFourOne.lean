import GaloisForLFunctions.MatomakiRadziwill.LFunctionGrowth
import GaloisForLFunctions.HTGeometry.PositiveEulerProductBudget
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The three-four-one inequality for Dirichlet `L`-functions

For a character `χ` mod `q`, `σ > 1` and real `γ`:

* `three_four_one_logDeriv`: with `−L'/L(s,ψ) = Σ ψ(n)Λ(n)n^{-s}`,
  `3 Re(−L'/L(σ,χ₀)) + 4 Re(−L'/L(σ+iγ,χ)) + Re(−L'/L(σ+2iγ,χ²)) ≥ 0`,
  termwise from `3 + 4 Re z + Re z² = 2(1 + Re z)² ≥ 0` on the unit circle;
* `re_neg_logDeriv_trivChar_le`: `Re(−L'/L(σ,χ₀)) ≤ Re(−ζ'/ζ(σ))`;
* `norm_LFunction_le_of_one_lt`: `‖L(σ+iy, ψ)‖ ≤ 1 + 1/(σ−1)`;
* `inv_le_norm_LFunction`: `‖L(σ+iy, ψ)‖ ≥ 1/(1 + 1/(σ−1))`, from Mathlib's product inequality
  `‖L(σ,χ₀)³ L(σ+iy,ψ)⁴ L(σ+2iy,ψ²)‖ ≥ 1`.
-/

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-- `3 + 4 Re z + Re z² = 2(1 + Re z)² ≥ 0` for `|z| = 1`. -/
theorem three_four_one_unit {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h1 := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h1
    nlinarith
  have h2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq, Complex.mul_re]
  rw [h2]
  nlinarith [sq_nonneg (z.re + 1)]

/-- The termwise three-four-one inequality. -/
theorem three_four_one_term (χ : DirichletCharacter ℂ q) {σ : ℝ} (γ : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re +
      4 * (term (↗χ * ↗Λ) ((σ : ℂ) + (γ : ℂ) * I) n).re +
      (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn]
  set u : ℂ := (n : ℂ) ^ ((γ : ℂ) * I) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hσpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  have hs1 : (n : ℂ) ^ ((σ : ℂ) + (γ : ℂ) * I) = (((n : ℝ) ^ σ : ℝ) : ℂ) * u := by
    rw [Complex.cpow_add _ _ hnC, hσpow]
  have hs2 : (n : ℂ) ^ ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = (((n : ℝ) ^ σ : ℝ) : ℂ) * u ^ 2 := by
    rw [Complex.cpow_add _ _ hnC, hσpow, hudef, ← Complex.cpow_nat_mul]
    congr 2
    push_cast
    ring
  rw [hs1, hs2, hσpow]
  set A : ℝ := Λ n / (n : ℝ) ^ σ with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact div_nonneg vonMangoldt_nonneg (by positivity)
  have hnσ : (0 : ℝ) < (n : ℝ) ^ σ := by positivity
  have hnσC : (((n : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnσ.ne'
  by_cases hunit : IsUnit (n : ZMod q)
  · have h1 : ((1 : DirichletCharacter ℂ q) : ZMod q → ℂ) (n : ZMod q) = 1 := MulChar.one_apply hunit
    set z : ℂ := χ (n : ZMod q) / u with hzdef
    have hz : ‖z‖ = 1 := by
      rw [hzdef, norm_div, hu, div_one]
      have := χ.unit_norm_eq_one hunit.unit
      rwa [IsUnit.unit_spec] at this
    have e0 : (((↗(1 : DirichletCharacter ℂ q) * ↗Λ) n) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * 1 := by
      simp only [Pi.mul_apply, h1, one_mul]
      rw [hAdef, ← Complex.ofReal_div, Complex.ofReal_re, mul_one]
    have e1 : (((↗χ * ↗Λ) n) / ((((n : ℝ) ^ σ : ℝ) : ℂ) * u)).re = A * z.re := by
      simp only [Pi.mul_apply]
      rw [hzdef, hAdef, show χ (n : ZMod q) * ((Λ n : ℝ) : ℂ) / ((((n : ℝ) ^ σ : ℝ) : ℂ) * u) =
          (((Λ n / (n : ℝ) ^ σ : ℝ)) : ℂ) * (χ (n : ZMod q) / u) by
        push_cast; field_simp, Complex.re_ofReal_mul]
    have e2 : (((↗(χ ^ 2) * ↗Λ) n) / ((((n : ℝ) ^ σ : ℝ) : ℂ) * u ^ 2)).re = A * (z ^ 2).re := by
      simp only [Pi.mul_apply]
      rw [MulChar.pow_apply' χ two_ne_zero, hzdef, hAdef,
        show χ (n : ZMod q) ^ 2 * ((Λ n : ℝ) : ℂ) / ((((n : ℝ) ^ σ : ℝ) : ℂ) * u ^ 2) =
          (((Λ n / (n : ℝ) ^ σ : ℝ)) : ℂ) * (χ (n : ZMod q) / u) ^ 2 by
        push_cast; field_simp, Complex.re_ofReal_mul]
    rw [e0, e1, e2]
    have := three_four_one_unit hz
    nlinarith
  · have h0 : ((1 : DirichletCharacter ℂ q) : ZMod q → ℂ) (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ hunit
    have hχ0 : χ (n : ZMod q) = 0 := MulChar.map_nonunit _ hunit
    simp [Pi.mul_apply, h0, hχ0, MulChar.pow_apply' χ two_ne_zero]

/-- **Three-four-one for `−L'/L`.** -/
theorem three_four_one_logDeriv (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (γ : ℝ) :
    0 ≤ 3 * (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ)).re +
      4 * (LSeries (↗χ * ↗Λ) ((σ : ℂ) + (γ : ℂ) * I)).re +
      (LSeries (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simp [hσ]
  have hs1 : 1 < ((σ : ℂ) + (γ : ℂ) * I).re := by simp [hσ]
  have hs2 : 1 < ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re := by simp [hσ]
  have H0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) hs0
  have H1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have H2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) hs2
  have R0 := (Complex.hasSum_re H0.hasSum).summable
  have R1 := (Complex.hasSum_re H1.hasSum).summable
  have R2 := (Complex.hasSum_re H2.hasSum).summable
  rw [LSeries, LSeries, LSeries, Complex.re_tsum H0, Complex.re_tsum H1, Complex.re_tsum H2,
    ← tsum_mul_left, ← tsum_mul_left, ← (R0.mul_left 3).tsum_add (R1.mul_left 4),
    ← ((R0.mul_left 3).add (R1.mul_left 4)).tsum_add R2]
  exact tsum_nonneg fun n => three_four_one_term χ γ n

/-- `Re(−L'/L(σ,χ₀)) ≤ Re(−ζ'/ζ(σ))` for real `σ > 1`. -/
theorem re_LSeries_trivChar_vonMangoldt_le {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ)).re ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ)).re := by simp [hσ]
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have H0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) hs
  have HΛ := LSeriesSummable_vonMangoldt hs
  rw [LSeries, LSeries, Complex.re_tsum H0, Complex.re_tsum HΛ]
  refine (Complex.hasSum_re H0.hasSum).summable.tsum_le_tsum (fun n => ?_)
    (Complex.hasSum_re HΛ.hasSum).summable
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [term_of_ne_zero hn, term_of_ne_zero hn]
  have hσpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  rw [hσpow]
  simp only [Pi.mul_apply]
  have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  have hnσ : (0 : ℝ) < (n : ℝ) ^ σ := by positivity
  by_cases hunit : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hunit, one_mul]
  · rw [MulChar.map_nonunit _ hunit, zero_mul, zero_div, Complex.zero_re,
      ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg hΛ hnσ.le

/-- `‖L(s, ψ)‖ ≤ 1 + 1/(σ−1)` for `Re s = σ > 1`. -/
theorem norm_LFunction_le_of_one_lt (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ 1 + (s.re - 1)⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs, LSeries]
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ n : ℕ, ‖term (fun n => ψ n) s n‖ ≤ (n : ℝ) ^ (-s.re) := by
    intro n
    rw [norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.rpow_neg hn0.le, ← one_div]
      exact div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) (by positivity)
  calc ‖∑' n, term (fun n => ψ n) s n‖ ≤ ∑' n, ‖term (fun n => ψ n) s n‖ :=
        norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
        (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm).tsum_le_tsum hterm hsum
    _ ≤ 1 + (s.re - 1)⁻¹ := GaloisForLFunctions.HTGeometry.tsum_nat_rpow_neg_le_one_add_inv hs

/-- **Lower bound off the line.** `‖L(σ+iy, ψ)‖ ≥ 1/(1 + 1/(σ−1))` for `σ > 1`. -/
theorem inv_le_norm_LFunction (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (1 + (σ - 1)⁻¹)⁻¹ ≤ ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (y : ℂ) * I)‖ := by
  set Z : ℝ := 1 + (σ - 1)⁻¹ with hZdef
  have hσ1 : 0 < σ - 1 := by linarith
  have hZ1 : 1 ≤ Z := by rw [hZdef]; have : 0 < (σ - 1)⁻¹ := by positivity
                         linarith
  have hZ0 : 0 < Z := by linarith
  have hprod := DirichletCharacter.norm_LFunction_product_ge_one ψ hσ1 y
  have e0 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by push_cast; ring
  have e1 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) + I * (y : ℂ) = (σ : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  have e2 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) + 2 * I * (y : ℂ) = (σ : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e1, e2, norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  rw [show ((1 : ℂ) + ((σ - 1 : ℝ) : ℂ)) = (σ : ℂ) from e0] at hprod
  have hA : ‖DirichletCharacter.LFunctionTrivChar q (σ : ℂ)‖ ≤ Z := by
    have := norm_LFunction_le_of_one_lt (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simp [hσ])
    simpa [hZdef] using this
  have hC : ‖DirichletCharacter.LFunction (ψ ^ 2) ((σ : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖ ≤ Z := by
    have := norm_LFunction_le_of_one_lt (ψ ^ 2) (s := (σ : ℂ) + ((2 * y : ℝ) : ℂ) * I)
      (by simp [hσ])
    simpa [hZdef] using this
  set B := ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (y : ℂ) * I)‖ with hBdef
  have hB0 : 0 ≤ B := norm_nonneg _
  have hA0 : 0 ≤ ‖DirichletCharacter.LFunctionTrivChar q (σ : ℂ)‖ := norm_nonneg _
  have hC0 : 0 ≤ ‖DirichletCharacter.LFunction (ψ ^ 2) ((σ : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  -- `1 ≤ Z³ B⁴ Z = Z⁴ B⁴`
  have h1 : 1 ≤ Z ^ 3 * B ^ 4 * Z := by
    calc (1 : ℝ) ≤ _ := hprod
      _ ≤ Z ^ 3 * B ^ 4 * Z := by gcongr
  have h2 : 1 ≤ (Z * B) ^ 4 := by nlinarith
  have h3 : 1 ≤ Z * B := by
    by_contra h
    rw [not_le] at h
    have hZB0 : 0 ≤ Z * B := by positivity
    have : (Z * B) ^ 4 < 1 := pow_lt_one₀ hZB0 h (by norm_num)
    linarith
  rw [inv_le_iff_one_le_mul₀ hZ0]
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
