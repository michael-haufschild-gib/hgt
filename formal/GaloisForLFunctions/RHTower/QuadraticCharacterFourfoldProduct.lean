import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The fourfold product `L(s,1)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` of quadratic characters is at least `(2 − π²/6)³` on `(1,2]`

For quadratic characters `χ₁, χ₂` modulo `N` the logarithmic derivative of

`F(s) = L(s,1_N) L(s,χ₁) L(s,χ₂) L(s,χ₁χ₂)`

on the real axis `σ > 1` is `-Σ_n Λ(n) n^{-σ} 1_N(n)(1+χ₁(n))(1+χ₂(n))`, whose coefficients are
nonnegative because a quadratic character takes the values `0, ±1`.  Hence `F` is real, positive and
nonincreasing on `(1,2]`, so `F(σ) ≥ F(2)`.  At `σ = 2` every factor is a Dirichlet series whose
first coefficient is `1` and whose other coefficients are at least `-1/n²`, so each factor is at least
`2 - ζ(2) = 2 - π²/6 > 0`, and the trivial factor is at least `1`.

This is the share-ledger input of the exceptional-zero argument: the pole of `L(s,1_N)` pays for at
most one nearby real zero of the two characters.
-/

open Complex Filter Topology
open scoped LSeries.notation ArithmeticFunction.vonMangoldt

namespace RHTower

noncomputable section

variable {N : ℕ}

/-! ## Real values of quadratic characters -/

theorem im_eq_zero_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (a : ZMod N) :
    (χ a).im = 0 := by
  rcases hχ a with h | h | h <;> simp [h]

theorem neg_one_le_re_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    (a : ZMod N) : -1 ≤ (χ a).re := by
  rcases hχ a with h | h | h <;> simp [h]

theorem eq_ofReal_re_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    (a : ZMod N) : χ a = (((χ a).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [im_eq_zero_of_isQuadratic hχ a]

theorem isQuadratic_one : (1 : DirichletCharacter ℂ N).IsQuadratic := by
  intro a
  by_cases hu : IsUnit a
  · rw [MulChar.one_apply hu]
    simp
  · rw [MulChar.map_nonunit _ hu]
    simp

theorem isQuadratic_mul {χ₁ χ₂ : DirichletCharacter ℂ N} (h₁ : χ₁.IsQuadratic)
    (h₂ : χ₂.IsQuadratic) : (χ₁ * χ₂).IsQuadratic := by
  intro a
  rw [MulChar.mul_apply]
  rcases h₁ a with e₁ | e₁ | e₁ <;> rcases h₂ a with e₂ | e₂ | e₂ <;> simp [e₁, e₂]

/-! ## Real coefficients -/

/-- The real coefficient of a character. -/
def charRe (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ := (χ (n : ZMod N)).re

theorem charRe_one_of_isQuadratic {χ : DirichletCharacter ℂ N} (_hχ : χ.IsQuadratic) :
    charRe χ 1 = 1 := by
  simp [charRe]

theorem charRe_mul_of_isQuadratic {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) (n : ℕ) : charRe (χ₁ * χ₂) n = charRe χ₁ n * charRe χ₂ n := by
  unfold charRe
  rw [MulChar.mul_apply, Complex.mul_re, im_eq_zero_of_isQuadratic hχ₁,
    im_eq_zero_of_isQuadratic hχ₂]
  ring

theorem charRe_one_of_isUnit {n : ℕ} (hu : IsUnit (n : ZMod N)) :
    charRe (1 : DirichletCharacter ℂ N) n = 1 := by
  unfold charRe
  rw [MulChar.one_apply hu]
  simp

theorem charRe_eq_zero_of_not_isUnit (χ : DirichletCharacter ℂ N) {n : ℕ}
    (hu : ¬ IsUnit (n : ZMod N)) : charRe χ n = 0 := by
  unfold charRe
  rw [MulChar.map_nonunit χ hu]
  simp

theorem charRe_one_nonneg (n : ℕ) : 0 ≤ charRe (1 : DirichletCharacter ℂ N) n := by
  by_cases hu : IsUnit (n : ZMod N)
  · rw [charRe_one_of_isUnit hu]
    norm_num
  · rw [charRe_eq_zero_of_not_isUnit _ hu]

theorem LSeries_term_eq_ofReal_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    LSeries.term (↗χ) (σ : ℂ) n = ((charRe χ n * realPowerKernel σ n : ℝ) : ℂ) := by
  have h := LSeries_term_dirichletCharacter_eq χ hσ n
  rw [h, eq_ofReal_re_of_isQuadratic hχ]
  push_cast
  rw [charRe]
  ring

/-! ## The twisted von Mangoldt coefficients -/

/-- The real twisted von Mangoldt coefficient. -/
def twistRe (χ : DirichletCharacter ℂ N) (σ : ℝ) (n : ℕ) : ℝ :=
  charRe χ n * Λ n * realPowerKernel σ n

theorem LSeries_term_twist_eq_ofReal {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    LSeries.term (↗χ * ↗Λ) (σ : ℂ) n = ((twistRe χ σ n : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, twistRe, realPowerKernel_zero hσ]
    simp
  · rw [LSeries.term_of_ne_zero hn, twistRe, Pi.mul_apply]
    have hker : ((n : ℂ)) ^ (σ : ℂ) = (((realPowerKernel σ n)⁻¹ : ℝ) : ℂ) := by
      rw [realPowerKernel, Real.rpow_neg (Nat.cast_nonneg n), inv_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    rw [hker, eq_ofReal_re_of_isQuadratic hχ, charRe]
    push_cast
    rw [div_inv_eq_mul]

/-- The real coefficient sum of the four twisted series: `Λ(n) n^{-σ} 1_N(n)(1+χ₁(n))(1+χ₂(n))`. -/
theorem twistRe_sum_eq {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) (σ : ℝ) (n : ℕ) :
    twistRe (1 : DirichletCharacter ℂ N) σ n + twistRe χ₁ σ n + twistRe χ₂ σ n
        + twistRe (χ₁ * χ₂) σ n
      = charRe (1 : DirichletCharacter ℂ N) n * ((1 + charRe χ₁ n) * (1 + charRe χ₂ n))
          * Λ n * realPowerKernel σ n := by
  have hmul := charRe_mul_of_isQuadratic hχ₁ hχ₂ n
  by_cases hu : IsUnit (n : ZMod N)
  · have h1 := charRe_one_of_isUnit (N := N) hu
    simp only [twistRe, hmul, h1]
    ring
  · have h0 := charRe_eq_zero_of_not_isUnit (1 : DirichletCharacter ℂ N) hu
    have h1 := charRe_eq_zero_of_not_isUnit χ₁ hu
    have h2 := charRe_eq_zero_of_not_isUnit χ₂ hu
    simp only [twistRe, hmul, h0, h1, h2]
    ring

theorem twistRe_sum_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) (σ : ℝ) (n : ℕ) :
    0 ≤ twistRe (1 : DirichletCharacter ℂ N) σ n + twistRe χ₁ σ n + twistRe χ₂ σ n
        + twistRe (χ₁ * χ₂) σ n := by
  rw [twistRe_sum_eq hχ₁ hχ₂]
  have h0 := charRe_one_nonneg (N := N) n
  have h1 : 0 ≤ 1 + charRe χ₁ n := by
    have := neg_one_le_re_of_isQuadratic hχ₁ (n : ZMod N)
    unfold charRe
    linarith
  have h2 : 0 ≤ 1 + charRe χ₂ n := by
    have := neg_one_le_re_of_isQuadratic hχ₂ (n : ZMod N)
    unfold charRe
    linarith
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hk := realPowerKernel_nonneg σ n
  exact mul_nonneg (mul_nonneg (mul_nonneg h0 (mul_nonneg h1 h2)) hΛ) hk

/-- The total real twisted series of the fourfold product. -/
def fourfoldTwist (χ₁ χ₂ : DirichletCharacter ℂ N) (σ : ℝ) : ℝ :=
  ∑' n, (twistRe (1 : DirichletCharacter ℂ N) σ n + twistRe χ₁ σ n + twistRe χ₂ σ n
    + twistRe (χ₁ * χ₂) σ n)

theorem fourfoldTwist_nonneg {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) (σ : ℝ) : 0 ≤ fourfoldTwist χ₁ χ₂ σ :=
  tsum_nonneg (fun n => twistRe_sum_nonneg hχ₁ hχ₂ σ n)

/-! ## The twisted series on the real axis -/

theorem summable_twistRe {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) {σ : ℝ}
    (hσ : 1 < σ) : Summable (twistRe χ σ) := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hσ'
  have h : Summable (fun n => ((twistRe χ σ n : ℝ) : ℂ)) :=
    hsum.congr (fun n => LSeries_term_twist_eq_ofReal hχ (by linarith) n)
  exact Complex.summable_ofReal.mp h

theorem LSeries_twist_ofReal_eq_tsum {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) {σ : ℝ}
    (hσ : 1 < σ) :
    LSeries (↗χ * ↗Λ) (σ : ℂ) = ((∑' n, twistRe χ σ n : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (fun n => LSeries_term_twist_eq_ofReal hχ (by linarith) n)

theorem fourfoldTwist_eq {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    fourfoldTwist χ₁ χ₂ σ
      = (∑' n, twistRe (1 : DirichletCharacter ℂ N) σ n) + (∑' n, twistRe χ₁ σ n)
        + (∑' n, twistRe χ₂ σ n) + (∑' n, twistRe (χ₁ * χ₂) σ n) := by
  have s₀ := summable_twistRe (isQuadratic_one (N := N)) hσ
  have s₁ := summable_twistRe hχ₁ hσ
  have s₂ := summable_twistRe hχ₂ hσ
  have s₃ := summable_twistRe (isQuadratic_mul hχ₁ hχ₂) hσ
  unfold fourfoldTwist
  rw [((s₀.add s₁).add s₂).tsum_add s₃, (s₀.add s₁).tsum_add s₂, s₀.tsum_add s₁]

/-! ## Real Dirichlet series on the real axis -/

variable [NeZero N]

theorem summable_charRe_mul_kernel {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) {σ : ℝ}
    (hσ : 1 < σ) : Summable (fun n => charRe χ n * realPowerKernel σ n) := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hsum : LSeriesSummable (↗χ) (σ : ℂ) :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr hσ'
  have h : Summable (fun n => ((charRe χ n * realPowerKernel σ n : ℝ) : ℂ)) :=
    hsum.congr (fun n => LSeries_term_eq_ofReal_of_isQuadratic hχ (by linarith) n)
  exact Complex.summable_ofReal.mp h

theorem LFunction_ofReal_eq_tsum_of_isQuadratic {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic)
    {σ : ℝ} (hσ : 1 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ)
      = ((∑' n, charRe χ n * realPowerKernel σ n : ℝ) : ℂ) := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ', LSeries, Complex.ofReal_tsum]
  exact tsum_congr (fun n => LSeries_term_eq_ofReal_of_isQuadratic hχ (by linarith) n)

/-! ## Lower bounds at `σ = 2` -/

/-- The kernel at exponent `2` is `1/n²`. -/
theorem realPowerKernel_two (n : ℕ) : realPowerKernel 2 n = 1 / (n : ℝ) ^ 2 := by
  rw [realPowerKernel, Real.rpow_neg (Nat.cast_nonneg n), one_div, Real.rpow_two]

/-- The comparison sequence `2·[n = 1] − 1/n²`, whose sum is `2 − π²/6`. -/
theorem hasSum_comparison_two :
    HasSum (fun n : ℕ => (if n = 1 then (2 : ℝ) else 0) - 1 / (n : ℝ) ^ 2) (2 - Real.pi ^ 2 / 6) :=
  (hasSum_ite_eq (1 : ℕ) (2 : ℝ)).sub hasSum_zeta_two

theorem two_sub_pi_sq_div_six_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  have h := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

/-- Every quadratic character has `L(2,χ) ≥ 2 − π²/6`. -/
theorem two_sub_le_tsum_charRe_two {χ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) :
    2 - Real.pi ^ 2 / 6 ≤ ∑' n, charRe χ n * realPowerKernel 2 n := by
  have hsum := summable_charRe_mul_kernel hχ (by norm_num : (1 : ℝ) < 2)
  refine hasSum_le (fun n => ?_) hasSum_comparison_two hsum.hasSum
  rw [realPowerKernel_two]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [charRe]
    · norm_num [charRe_one_of_isQuadratic hχ]
  · have hn1 : n ≠ 1 := by omega
    rw [if_neg hn1, zero_sub]
    have hpos : 0 < 1 / (n : ℝ) ^ 2 := by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    have hre := neg_one_le_re_of_isQuadratic hχ (n : ZMod N)
    have : -1 * (1 / (n : ℝ) ^ 2) ≤ charRe χ n * (1 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hre hpos.le
    linarith

/-- The trivial character has `L(2,1_N) ≥ 1`. -/
theorem one_le_tsum_charRe_one_two :
    1 ≤ ∑' n, charRe (1 : DirichletCharacter ℂ N) n * realPowerKernel 2 n := by
  have hsum := summable_charRe_mul_kernel (isQuadratic_one (N := N)) (by norm_num : (1 : ℝ) < 2)
  have hnonneg : ∀ n, 0 ≤ charRe (1 : DirichletCharacter ℂ N) n * realPowerKernel 2 n :=
    fun n => mul_nonneg (charRe_one_nonneg n) (realPowerKernel_nonneg _ _)
  have h1 : charRe (1 : DirichletCharacter ℂ N) 1 * realPowerKernel 2 1 = 1 := by
    simp [charRe, realPowerKernel]
  calc (1 : ℝ) = charRe (1 : DirichletCharacter ℂ N) 1 * realPowerKernel 2 1 := h1.symm
    _ ≤ ∑' n, charRe (1 : DirichletCharacter ℂ N) n * realPowerKernel 2 n :=
        hsum.le_tsum 1 (fun n _ => hnonneg n)

/-! ## The twisted series and the derivative on the real axis -/

/-- The derivative of `L(·,χ)` at real `σ > 1` is `-L(σ,χ)` times the real twisted series. -/
theorem hasDerivAt_LFunction_ofReal_of_isQuadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (DirichletCharacter.LFunction χ)
      (-((∑' n, twistRe χ σ n : ℝ) : ℂ) * DirichletCharacter.LFunction χ (σ : ℂ)) (σ : ℂ) := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hdiff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) (σ : ℂ) :=
    DirichletCharacter.differentiableAt_LFunction χ (σ : ℂ) (Or.inl hne1)
  have hL : DirichletCharacter.LFunction χ (σ : ℂ) = LSeries (↗χ) (σ : ℂ) :=
    DirichletCharacter.LFunction_eq_LSeries χ hσ'
  have hLne : LSeries (↗χ) (σ : ℂ) ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hσ'
  have htwist := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hσ'
  have hderiv : deriv (DirichletCharacter.LFunction χ) (σ : ℂ)
      = -(LSeries (↗χ * ↗Λ) (σ : ℂ)) * LSeries (↗χ) (σ : ℂ) := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hσ', htwist]
    field_simp
  have := hdiff.hasDerivAt
  rw [hderiv, ← hL, LSeries_twist_ofReal_eq_tsum hχ hσ] at this
  exact this

/-! ## The fourfold product -/

/-- `F(s) = L(s,1_N) L(s,χ₁) L(s,χ₂) L(s,χ₁χ₂)`. -/
def fourfoldProduct (χ₁ χ₂ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s * DirichletCharacter.LFunction χ₁ s
    * DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (χ₁ * χ₂) s

/-- Derivative of the fourfold product at real `σ > 1`: `F' = -F · fourfoldTwist`. -/
theorem hasDerivAt_fourfoldProduct_ofReal {χ₁ χ₂ : DirichletCharacter ℂ N}
    (hχ₁ : χ₁.IsQuadratic) (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fourfoldProduct χ₁ χ₂)
      (-(((fourfoldTwist χ₁ χ₂ σ : ℝ) : ℂ) * fourfoldProduct χ₁ χ₂ (σ : ℂ))) (σ : ℂ) := by
  have h0 := hasDerivAt_LFunction_ofReal_of_isQuadratic (isQuadratic_one (N := N)) hσ
  have h1 := hasDerivAt_LFunction_ofReal_of_isQuadratic hχ₁ hσ
  have h2 := hasDerivAt_LFunction_ofReal_of_isQuadratic hχ₂ hσ
  have h3 := hasDerivAt_LFunction_ofReal_of_isQuadratic (isQuadratic_mul hχ₁ hχ₂) hσ
  have h := ((h0.mul h1).mul h2).mul h3
  refine h.congr_deriv ?_
  rw [fourfoldTwist_eq hχ₁ hχ₂ hσ]
  unfold fourfoldProduct
  simp only [Pi.mul_apply]
  push_cast
  ring

/-- The real value of the fourfold product on the real axis. -/
def fourfoldRe (χ₁ χ₂ : DirichletCharacter ℂ N) (σ : ℝ) : ℝ :=
  (fourfoldProduct χ₁ χ₂ (σ : ℂ)).re

theorem fourfoldProduct_ofReal_eq {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    fourfoldProduct χ₁ χ₂ (σ : ℂ) = ((fourfoldRe χ₁ χ₂ σ : ℝ) : ℂ) := by
  unfold fourfoldRe fourfoldProduct
  rw [LFunction_ofReal_eq_tsum_of_isQuadratic (isQuadratic_one (N := N)) hσ,
    LFunction_ofReal_eq_tsum_of_isQuadratic hχ₁ hσ,
    LFunction_ofReal_eq_tsum_of_isQuadratic hχ₂ hσ,
    LFunction_ofReal_eq_tsum_of_isQuadratic (isQuadratic_mul hχ₁ hχ₂) hσ]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]

theorem hasDerivAt_fourfoldRe {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (fourfoldRe χ₁ χ₂) (-(fourfoldTwist χ₁ χ₂ σ * fourfoldRe χ₁ χ₂ σ)) σ := by
  have h := (hasDerivAt_fourfoldProduct_ofReal hχ₁ hχ₂ hσ).real_of_complex
  rw [fourfoldProduct_ofReal_eq hχ₁ hχ₂ hσ] at h
  have hre : (-(((fourfoldTwist χ₁ χ₂ σ : ℝ) : ℂ) * ((fourfoldRe χ₁ χ₂ σ : ℝ) : ℂ))).re
      = -(fourfoldTwist χ₁ χ₂ σ * fourfoldRe χ₁ χ₂ σ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re]
  rw [hre] at h
  exact h

theorem fourfoldProduct_ne_zero (χ₁ χ₂ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    fourfoldProduct χ₁ χ₂ (σ : ℂ) ≠ 0 := by
  have hre : 1 ≤ ((σ : ℂ)).re := by simpa using hσ.le
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold fourfoldProduct
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_ <;>
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hne1) hre

/-- At `σ = 2` the fourfold product is at least `(2 − π²/6)³`. -/
theorem fourfoldRe_two_ge {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) :
    (2 - Real.pi ^ 2 / 6) ^ 3 ≤ fourfoldRe χ₁ χ₂ 2 := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hrw : fourfoldRe χ₁ χ₂ 2
      = (∑' n, charRe (1 : DirichletCharacter ℂ N) n * realPowerKernel 2 n)
        * (∑' n, charRe χ₁ n * realPowerKernel 2 n)
        * (∑' n, charRe χ₂ n * realPowerKernel 2 n)
        * (∑' n, charRe (χ₁ * χ₂) n * realPowerKernel 2 n) := by
    unfold fourfoldRe fourfoldProduct
    rw [LFunction_ofReal_eq_tsum_of_isQuadratic (isQuadratic_one (N := N)) h2,
      LFunction_ofReal_eq_tsum_of_isQuadratic hχ₁ h2,
      LFunction_ofReal_eq_tsum_of_isQuadratic hχ₂ h2,
      LFunction_ofReal_eq_tsum_of_isQuadratic (isQuadratic_mul hχ₁ hχ₂) h2]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hrw]
  have hc := two_sub_pi_sq_div_six_pos
  have ha := one_le_tsum_charRe_one_two (N := N)
  have hb := two_sub_le_tsum_charRe_two hχ₁
  have hc' := two_sub_le_tsum_charRe_two hχ₂
  have hd := two_sub_le_tsum_charRe_two (isQuadratic_mul hχ₁ hχ₂)
  set A := ∑' n, charRe (1 : DirichletCharacter ℂ N) n * realPowerKernel 2 n with hA
  set B := ∑' n, charRe χ₁ n * realPowerKernel 2 n with hB
  set C := ∑' n, charRe χ₂ n * realPowerKernel 2 n with hC
  set D := ∑' n, charRe (χ₁ * χ₂) n * realPowerKernel 2 n with hD
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h1 : 1 * (2 - Real.pi ^ 2 / 6) ≤ A * B := mul_le_mul ha hb hc.le hA0
  have h2' : 1 * (2 - Real.pi ^ 2 / 6) * (2 - Real.pi ^ 2 / 6) ≤ A * B * C :=
    mul_le_mul h1 hc' hc.le (mul_nonneg hA0 hB0)
  have h3 : 1 * (2 - Real.pi ^ 2 / 6) * (2 - Real.pi ^ 2 / 6) * (2 - Real.pi ^ 2 / 6)
      ≤ A * B * C * D :=
    mul_le_mul h2' hd hc.le (mul_nonneg (mul_nonneg hA0 hB0) hC0)
  calc (2 - Real.pi ^ 2 / 6) ^ 3
      = 1 * (2 - Real.pi ^ 2 / 6) * (2 - Real.pi ^ 2 / 6) * (2 - Real.pi ^ 2 / 6) := by ring
    _ ≤ A * B * C * D := h3

theorem continuousOn_fourfoldRe {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ₀ : ℝ} (h1 : 1 < σ₀) :
    ContinuousOn (fourfoldRe χ₁ χ₂) (Set.Icc σ₀ 2) := by
  intro x hx
  exact (hasDerivAt_fourfoldRe hχ₁ hχ₂ (by linarith [hx.1])).continuousAt.continuousWithinAt

/-- The fourfold product is positive on `(1, 2]`. -/
theorem fourfoldRe_pos {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) : 0 < fourfoldRe χ₁ χ₂ σ := by
  by_contra hneg
  have hneg' : fourfoldRe χ₁ χ₂ σ ≤ 0 := not_lt.mp hneg
  have hcont := continuousOn_fourfoldRe hχ₁ hχ₂ h1
  have hval2 := fourfoldRe_two_ge hχ₁ hχ₂
  have hc := two_sub_pi_sq_div_six_pos
  have hpos2 : 0 < fourfoldRe χ₁ χ₂ 2 := lt_of_lt_of_le (by positivity) hval2
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc h2 hcont ⟨hneg', hpos2.le⟩
  have hx1 : 1 < x := by linarith [hx.1]
  apply fourfoldProduct_ne_zero χ₁ χ₂ hx1
  rw [fourfoldProduct_ofReal_eq hχ₁ hχ₂ hx1, hx0]
  simp

theorem fourfoldRe_antitoneOn {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ₀ : ℝ} (h1 : 1 < σ₀) :
    AntitoneOn (fourfoldRe χ₁ χ₂) (Set.Icc σ₀ 2) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc σ₀ 2) (continuousOn_fourfoldRe hχ₁ hχ₂ h1) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_fourfoldRe hχ₁ hχ₂ (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_fourfoldRe hχ₁ hχ₂ (by linarith [hx.1])).deriv]
    have hf := fourfoldRe_pos hχ₁ hχ₂ (by linarith [hx.1]) hx.2.le
    have hw := fourfoldTwist_nonneg hχ₁ hχ₂ x
    nlinarith

/-- **The fourfold product is at least `(2 − π²/6)³` on `(1, 2]`.** -/
theorem fourfoldRe_ge {χ₁ χ₂ : DirichletCharacter ℂ N} (hχ₁ : χ₁.IsQuadratic)
    (hχ₂ : χ₂.IsQuadratic) {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (2 - Real.pi ^ 2 / 6) ^ 3 ≤ fourfoldRe χ₁ χ₂ σ := by
  have hmono := fourfoldRe_antitoneOn hχ₁ hχ₂ h1
  have hle := hmono (Set.left_mem_Icc.mpr h2) (Set.right_mem_Icc.mpr h2) h2
  linarith [fourfoldRe_two_ge hχ₁ hχ₂]

end

end RHTower
