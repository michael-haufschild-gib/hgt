import GaloisForLFunctions.RHTower.MarkovThreeStageCountertermAndSpectralGapRigidityPBAP

/-!
# Exact FTC Evaluation of the First-Cell Cosine-Log Quadrature Integral $I_2(r)$, Clamped Product-Measure Fubini, and Coercivity & Spectral Gap Laws up to `106 / 5 = 21.2`, `70 / 3 > 23.333`, and `99 / 4 = 24.75` for Route HF / PBAP

1. **Section 1:** Universal alternating Taylor polynomial hierarchy for `1 - Real.cos θ` and
   `θ * Real.sin θ` up to degree 12 via `nonneg_of_deriv_nonneg`.
2. **Section 2:** Exact FTC evaluation of `I_2(r) = ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / √x`
   (`neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq`) and the pure-`r²` bound
   `-(13 / 720) * r ^ 2 ≤ I_2(r)` (`neg_thirteen_seven_twentieths_mul_sq_le_integral_one_two_cosLogProfile`).
3. **Section 3:** Clamped product-measure Fubini on `[1, 2] × ℝ` and upgraded coercivity &
   spectral gap laws up to `S / L ≤ 106 / 5 = 21.2`, `45 / 2 = 22.5`, `70 / 3 > 23.3333`, and
   `99 / 4 = 24.75`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Universal Alternating Taylor Polynomial Hierarchy for `Real.cos` and `Real.sin` up to Degree 12 -/

/-- Universal MVT monotonicity principle on `[0, ∞)`: if `f 0 = 0`, `HasDerivAt f (f' t) t` on
`(0, x]`, and `0 ≤ f' t` for `0 ≤ t`, then `0 ≤ f x` for all `0 ≤ x`. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ t : ℝ, HasDerivAt f (f' t) t) (hf' : ∀ t : ℝ, 0 ≤ t → 0 ≤ f' t)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · rw [hf0]
  · have hcont : ContinuousOn f (Icc 0 x) :=
      fun t _ => (hd t).continuousAt.continuousWithinAt
    have hdiff : ∀ t ∈ Ioo 0 x, HasDerivAt f (f' t) t :=
      fun t _ => hd t
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f f' hx_pos hcont hdiff
    have hslope : f x - f 0 = f' c * (x - 0) :=
      ((eq_div_iff (sub_pos.mpr hx_pos).ne').mp hc_eq).symm
    have hfc : 0 ≤ f' c := hf' c hc_mem.1.le
    have hprod : 0 ≤ f' c * (x - 0) := mul_nonneg hfc (sub_nonneg.mpr hx)
    linarith

/-- Step 1 (`f₁`): for all `0 ≤ θ`, `Real.sin θ ≤ θ`. -/
theorem sin_le_self_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : Real.sin θ ≤ θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => t - Real.sin t)
    (f' := fun t => 1 - Real.cos t)
    (by simp)
    (fun t => (hasDerivAt_id t).sub (Real.hasDerivAt_sin t))
    (fun t _ => sub_nonneg.mpr (Real.cos_le_one t))
    hθ
  linarith

/-- Step 2 (`f₂`): for all `θ : ℝ`, `1 - Real.cos θ ≤ θ ^ 2 / 2`. -/
private theorem one_sub_cos_le_sq_div_two (θ : ℝ) : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ Real.cos u - (1 - u ^ 2 / 2) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      rw [Real.cos_neg, neg_sq] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (f' := fun t => -Real.sin t + t)
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub
        ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2))).congr_deriv ?_
      norm_num)
    (fun t ht => by linarith [sin_le_self_of_nonneg ht])
    hu

/-- Step 3 (`f₃`): for all `0 ≤ θ`, `θ - θ ^ 3 / 6 ≤ Real.sin θ`. -/
theorem self_sub_cube_div_six_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 ≤ Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub
        ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_sq_div_two t])
    hθ
  linarith

/-- Step 4 (`f₄`): for all `θ : ℝ`, `θ ^ 2 / 2 - θ ^ 4 / 24 ≤ 1 - Real.cos θ`. -/
theorem sq_div_two_sub_pow_four_div_twenty_four_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 ≤ 1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      rw [Real.cos_neg, neg_sq, hpow4] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
    (f' := fun t => -t + t ^ 3 / 6 + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [self_sub_cube_div_six_le_sin_of_nonneg ht])
    hu

/-- Step 5 (`f₅`): for all `0 ≤ θ`, `Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120`. -/
theorem sin_le_self_sub_cube_div_six_add_pow_five_div_one_twenty_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [sq_div_two_sub_pow_four_div_twenty_four_le_one_sub_cos t])
    hθ
  linarith

/-- Step 6 (`f₆`): for all `θ : ℝ`,
`1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720`. -/
theorem one_sub_cos_le_sq_div_two_sub_pow_four_add_pow_six (θ : ℝ) :
    1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 := by
  suffices h : ∀ u : ℝ, 0 ≤ u → 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (f' := fun t => -Real.sin t + (t - t ^ 3 / 6 + t ^ 5 / 120))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub
        ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub
            ((hasDerivAt_pow 6 t).div_const 720))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_self_sub_cube_div_six_add_pow_five_div_one_twenty_of_nonneg ht])
    hu

/-- Step 7 (`f₇`): for all `0 ≤ θ`,
`θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 ≤ Real.sin θ`. -/
theorem self_sub_cube_add_pow_five_sub_pow_seven_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 ≤ Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
    (f' := fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub
        ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub
            ((hasDerivAt_pow 7 t).div_const 5040))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_sq_div_two_sub_pow_four_add_pow_six t])
    hθ
  linarith

/-- **Global Even-Degree Lower Bound on `θ * Real.sin θ`**:
for **every** `θ : ℝ`, `θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 ≤ θ * Real.sin θ`. -/
theorem mul_sin_ge_taylor_degree_eight (θ : ℝ) :
    θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 ≤ θ * Real.sin θ := by
  rcases le_total 0 θ with hθ | hθ
  · have h := mul_le_mul_of_nonneg_left
      (self_sub_cube_add_pow_five_sub_pow_seven_le_sin_of_nonneg hθ) hθ
    linarith [show θ * (θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 by ring]
  · have hθ_neg : 0 ≤ -θ := by linarith
    have h := mul_le_mul_of_nonneg_left
      (self_sub_cube_add_pow_five_sub_pow_seven_le_sin_of_nonneg hθ_neg) hθ_neg
    rw [Real.sin_neg] at h
    linarith [show (-θ) * ((-θ) - (-θ) ^ 3 / 6 + (-θ) ^ 5 / 120 - (-θ) ^ 7 / 5040) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 by ring,
      show (-θ) * -Real.sin θ = θ * Real.sin θ by ring]

/-- Step 8 (`f₈`): for all `θ : ℝ`,
`θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 ≤ 1 - Real.cos θ`. -/
theorem sq_div_two_sub_pow_four_add_pow_six_sub_pow_eight_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 ≤ 1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      have hpow8 : (-θ) ^ 8 = θ ^ 8 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6, hpow8] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
        ((hasDerivAt_pow 8 t).div_const 40320)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [self_sub_cube_add_pow_five_sub_pow_seven_le_sin_of_nonneg ht])
    hu

/-- Step 9 (`f₉`): for all `0 ≤ θ`,
`Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880`. -/
theorem sin_le_taylor_degree_nine_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880) - Real.sin t)
    (f' := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
        ((hasDerivAt_pow 9 t).div_const 362880)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [sq_div_two_sub_pow_four_add_pow_six_sub_pow_eight_le_one_sub_cos t])
    hθ
  linarith

/-- Step 10 (`f₁₀`): for all `θ : ℝ`,
`1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800`. -/
theorem one_sub_cos_le_taylor_degree_ten (θ : ℝ) :
    1 - Real.cos θ ≤
      θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      0 ≤ Real.cos u -
        (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 - u ^ 10 / 3628800) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      have hpow8 : (-θ) ^ 8 = θ ^ 8 := by ring
      have hpow10 : (-θ) ^ 10 = θ ^ 10 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6, hpow8, hpow10] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t -
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800))
    (f' := fun t => -Real.sin t +
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub
        ((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub
          ((hasDerivAt_pow 10 t).div_const 3628800))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_taylor_degree_nine_of_nonneg ht])
    hu

/-- Step 11 (`f₁₁`): for all `0 ≤ θ`,
`θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 ≤ Real.sin θ`. -/
theorem taylor_degree_eleven_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 ≤
      Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t -
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - t ^ 11 / 39916800))
    (f' := fun t => Real.cos t -
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub
        ((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
          ((hasDerivAt_pow 9 t).div_const 362880)).sub
          ((hasDerivAt_pow 11 t).div_const 39916800))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_taylor_degree_ten t])
    hθ
  linarith

/-- **Global Even-Degree-12 Lower Bound on `θ * Real.sin θ`**:
for **every** `θ : ℝ`,
`θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 - θ ^ 12 / 39916800 ≤ θ * Real.sin θ`. -/
theorem mul_sin_ge_taylor_degree_twelve (θ : ℝ) :
    θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 - θ ^ 12 / 39916800 ≤
      θ * Real.sin θ := by
  rcases le_total 0 θ with hθ | hθ
  · have h := mul_le_mul_of_nonneg_left (taylor_degree_eleven_le_sin_of_nonneg hθ) hθ
    linarith [show θ * (θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 -
        θ ^ 11 / 39916800) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 -
        θ ^ 12 / 39916800 by ring]
  · have hθ_neg : 0 ≤ -θ := by linarith
    have h := mul_le_mul_of_nonneg_left (taylor_degree_eleven_le_sin_of_nonneg hθ_neg) hθ_neg
    rw [Real.sin_neg] at h
    linarith [show (-θ) * ((-θ) - (-θ) ^ 3 / 6 + (-θ) ^ 5 / 120 - (-θ) ^ 7 / 5040 +
        (-θ) ^ 9 / 362880 - (-θ) ^ 11 / 39916800) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 -
        θ ^ 12 / 39916800 by ring,
      show (-θ) * -Real.sin θ = θ * Real.sin θ by ring]

/-- Step 12 (`f₁₂`): for all `θ : ℝ`,
`θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 ≤ 1 - Real.cos θ`. -/
theorem taylor_degree_twelve_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
        θ ^ 10 / 3628800 - θ ^ 12 / 479001600 ≤
      1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 -
        u ^ 10 / 3628800 + u ^ 12 / 479001600) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      have hpow8 : (-θ) ^ 8 = θ ^ 8 := by ring
      have hpow10 : (-θ) ^ 10 = θ ^ 10 := by ring
      have hpow12 : (-θ) ^ 12 = θ ^ 12 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6, hpow8, hpow10, hpow12] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
      t ^ 10 / 3628800 + t ^ 12 / 479001600) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
      t ^ 11 / 39916800) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
        ((hasDerivAt_pow 8 t).div_const 40320)).sub
        ((hasDerivAt_pow 10 t).div_const 3628800)).add
        ((hasDerivAt_pow 12 t).div_const 479001600)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [taylor_degree_eleven_le_sin_of_nonneg ht])
    hu

/-! ## Section 2: Exact FTC Evaluation of the First-Cell Cosine-Log Quadrature Integral $I_2(r)$ and the Sharp Pure-Second-Moment Bound `-(13 / 720) * r² ≤ I_2(r)` -/

/-- Explicit elementary antiderivative of `cosLogProfile r x / Real.sqrt x` on `(0, ∞)`. -/
def cosLogAntideriv (r x : ℝ) : ℝ :=
  Real.sqrt x * ((1 / 2) * Real.cos (r * Real.log x) + r * Real.sin (r * Real.log x)) /
    (1 / 4 + r ^ 2)

/-- For every `r : ℝ` and `0 < x`,
`HasDerivAt (cosLogAntideriv r) (cosLogProfile r x / Real.sqrt x) x`. -/
theorem hasDerivAt_cosLogAntideriv (r : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (cosLogAntideriv r) (cosLogProfile r x / Real.sqrt x) x := by
  unfold cosLogAntideriv cosLogProfile
  have hx_ne : x ≠ 0 := hx.ne'
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hd_arg : HasDerivAt (fun t => r * Real.log t) (r * x⁻¹) x :=
    (Real.hasDerivAt_log hx_ne).const_mul r
  have hd_cos : HasDerivAt (fun t => Real.cos (r * Real.log t))
      (-Real.sin (r * Real.log x) * (r * x⁻¹)) x :=
    hd_arg.cos
  have hd_sin : HasDerivAt (fun t => Real.sin (r * Real.log t))
      (Real.cos (r * Real.log x) * (r * x⁻¹)) x :=
    hd_arg.sin
  have hd_lin : HasDerivAt
      (fun t => (1 / 2) * Real.cos (r * Real.log t) + r * Real.sin (r * Real.log t))
      ((1 / 2) * (-Real.sin (r * Real.log x) * (r * x⁻¹)) +
        r * (Real.cos (r * Real.log x) * (r * x⁻¹))) x :=
    (hd_cos.const_mul (1 / 2)).add (hd_sin.const_mul r)
  have hd_prod := (Real.hasDerivAt_sqrt hx_ne).mul hd_lin
  refine (hd_prod.div_const (1 / 4 + r ^ 2)).congr_deriv ?_
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  apply mul_right_cancel₀ hsqrt_ne
  apply mul_right_cancel₀ hx_ne
  apply mul_right_cancel₀ hden_ne
  field_simp [hsqrt_ne, hx_ne, hden_ne]
  rw [hsq]
  ring

/-- **Exact Closed Form of the First-Cell Cosine-Log Quadrature Integral $I_2(r)$**. -/
theorem neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq (r : ℝ) :
  -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) =
      2 * (Real.sqrt 2 - 1) * r ^ 2 - Real.sqrt 2 * r * Real.sin (r * Real.log 2) +
        ((2 * Real.sqrt 2 - 1) / 3 - ((4 - 2 * Real.sqrt 2) / 3) * r ^ 2) *
          (1 - Real.cos (r * Real.log 2)) := by
  let F : ℝ → ℝ := fun x =>
    cosLogAntideriv r x -
      (2 * Real.sqrt x +
        (cosLogProfile r 2 - 1) * ((2 / 3) * x * Real.sqrt x - 2 * Real.sqrt x))
  have hderiv : ∀ x ∈ uIcc (1 : ℝ) 2,
      HasDerivAt F ((cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
    have hd1 := hasDerivAt_cosLogAntideriv r hx_pos
    have hd2 : HasDerivAt (fun t => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt x))) x :=
      (Real.hasDerivAt_sqrt hx_pos.ne').const_mul 2
    have hd3 := (hasDerivAt_two_thirds_mul_sqrt_sub_two_mul_sqrt hx_pos).const_mul
      (cosLogProfile r 2 - 1)
    refine (hd1.sub (hd2.add hd3)).congr_deriv ?_
    unfold cellSecant cosLogProfile
    norm_num [Real.log_one, Real.cos_zero]
    field_simp [hsqrt_ne]
    ring
  have hint : IntervalIntegrable
      (fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)
      volume 1 2 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    refine ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) (fun x hx =>
      (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hx.1)).ne')
    refine ContinuousOn.sub ?_ ?_
    · unfold cosLogProfile
      exact Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx =>
          (lt_of_lt_of_le zero_lt_one hx.1).ne'))
    · unfold cellSecant
      fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F, cosLogAntideriv, cosLogProfile]
  norm_num [Real.sqrt_one, Real.log_one, Real.cos_zero, Real.sin_zero]
  have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hden_ne]
  ring

/-- **Four-Panel Fourth-Order Midpoint Lower Bound `69313 / 100000 ≤ Real.log 2`** on
`[1, 5/4]`, `[5/4, 3/2]`, `[3/2, 7/4]`, and `[7/4, 2]`. -/
theorem two_panel_log_two_lower :
    (69313 / 100000 : ℝ) ≤ Real.log 2 := by
  have h1 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 1) (b := 5 / 4) (by norm_num) (by norm_num)
  have h2 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num)
  have h3 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 3 / 2) (b := 7 / 4) (by norm_num) (by norm_num)
  have h4 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 7 / 4) (b := 2) (by norm_num) (by norm_num)
  rw [Real.log_one] at h1
  linarith

/-- Upper bound `Real.sqrt 2 ≤ 577 / 408` (`(577 / 408)² = 332929 / 166464 = 2 + 1 / 166464`). -/
theorem sqrt_two_le_five_seventy_seven_four_hundred_eighths :
    Real.sqrt 2 ≤ 577 / 408 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 577 / 408)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Lower bound `8119 / 5741 ≤ Real.sqrt 2`. -/
theorem eight_thousand_one_hundred_nineteen_le_sqrt_two :
    (8119 / 5741 : ℝ) ≤ Real.sqrt 2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8119 / 5741)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Sum-of-squares polynomial inequality on `0 ≤ u ≤ 49` from the rational coefficient bounds. -/
lemma first_cell_poly_of_coeffs {c0 c1 c2 c3 c4 c5 c6 u : ℝ}
    (hc0 : c0 ≤ 0) (hc1 : c1 ≤ -211 / 10000) (hc2 : c2 ≤ 1970 / 1000000)
    (hc3 : c3 ≤ -392 / 10000000) (hc4 : c4 ≤ 378 / 1000000000)
    (hc5 : c5 ≤ -211 / 100000000000) (hc6 : c6 ≤ 101 / 10000000000000)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 49) :
    c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 + c5 * u ^ 5 + c6 * u ^ 6 ≤
      (13 / 720) * (1 / 4 + u) := by
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hm1 := mul_le_mul_of_nonneg_right hc1 hu_nonneg
  have hm2 := mul_le_mul_of_nonneg_right hc2 hu2
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 4)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 5)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hu6 : 0 ≤ 49 * u ^ 5 - u ^ 6 := by
    rw [show 49 * u ^ 5 - u ^ 6 = u ^ 5 * (49 - u) by ring]
    exact mul_nonneg (by positivity) (by linarith)
  have hsq5 : 0 ≤ u ^ 5 - 116 * u ^ 4 + 3364 * u ^ 3 := by
    rw [show u ^ 5 - 116 * u ^ 4 + 3364 * u ^ 3 = u ^ 3 * (u - 58) ^ 2 by ring]
    positivity
  have hsq4 : 0 ≤ -u ^ 4 + 81 * u ^ 3 - 1824 * u ^ 2 + 12544 * u := by
    rw [show -u ^ 4 + 81 * u ^ 3 - 1824 * u ^ 2 + 12544 * u =
      u * (49 - u) * (u - 16) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg hu_nonneg (by linarith)) (sq_nonneg _)
  have hsq3 : 0 ≤ 4 * u ^ 3 - 356 * u ^ 2 + 7921 * u := by
    rw [show 4 * u ^ 3 - 356 * u ^ 2 + 7921 * u = u * (2 * u - 89) ^ 2 by ring]
    positivity
  linarith only [hc0, hm1, hm2, hm3, hm4, hm5, hm6, hu6, hsq5, hsq4, hsq3, hu_nonneg, hu2]

/-- **Polynomial Taylor Upper Bound for the First Cell (`0 ≤ u ≤ 49`)**. -/
theorem first_cell_taylor_poly_le {ℓ s2 u : ℝ}
    (hℓ_low : 69313 / 100000 ≤ ℓ) (hℓ_high : ℓ ≤ 14411 / 20790)
    (hs2_low : 8119 / 5741 ≤ s2) (hs2_high : s2 ≤ 577 / 408)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 49) :
    (2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
      (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
      (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
      (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
      (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
      (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10) * u ^ 5 +
      ((4 - 2 * s2) / 1437004800 * ℓ ^ 12) * u ^ 6 ≤
    (13 / 720) * (1 / 4 + u) := by
  have hℓ0 : 0 ≤ ℓ := by linarith only [hℓ_low]
  have hs2_0 : 0 ≤ s2 := by linarith only [hs2_low]
  have hℓ1_1 : (69313 / 100000 : ℝ) ≤ ℓ := hℓ_low
  have hℓ1_2 : ℓ ≤ 69317 / 100000 := by linarith only [hℓ_high]
  have hℓ2_1 : (48042 / 100000 : ℝ) ≤ ℓ ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ1_1 2)
  have hℓ2_2 : ℓ ^ 2 ≤ 48049 / 100000 :=
    le_trans (pow_le_pow_left₀ hℓ0 hℓ1_2 2) (by norm_num)
  have hℓ3_1 : (33299 / 100000 : ℝ) ≤ ℓ ^ 3 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ1_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ3_2 : ℓ ^ 3 ≤ 33307 / 100000 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ4_1 : (23080 / 100000 : ℝ) ≤ ℓ ^ 4 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ2_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ4_2 : ℓ ^ 4 ≤ 23088 / 100000 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ2_2 (sq_nonneg ℓ) (by norm_num)) (by norm_num)
  have hℓ5_1 : (15997 / 100000 : ℝ) ≤ ℓ ^ 5 := by
    rw [show ℓ ^ 5 = ℓ ^ 4 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ6_1 : (11088 / 100000 : ℝ) ≤ ℓ ^ 6 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ3_1 hℓ3_1 (by norm_num) (by positivity))
  have hℓ6_2 : ℓ ^ 6 ≤ 11094 / 100000 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (mul_le_mul hℓ3_2 hℓ3_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ7_2 : ℓ ^ 7 ≤ 7691 / 100000 := by
    rw [show ℓ ^ 7 = ℓ ^ 6 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ8_1 : (5326 / 100000 : ℝ) ≤ ℓ ^ 8 := by
    rw [show ℓ ^ 8 = ℓ ^ 4 * ℓ ^ 4 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ4_1 (by norm_num) (by positivity))
  have hℓ8_2 : ℓ ^ 8 ≤ 5331 / 100000 := by
    rw [show ℓ ^ 8 = ℓ ^ 4 * ℓ ^ 4 by ring]
    exact le_trans (mul_le_mul hℓ4_2 hℓ4_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ9_1 : (3691 / 100000 : ℝ) ≤ ℓ ^ 9 := by
    rw [show ℓ ^ 9 = ℓ ^ 8 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ8_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ10_1 : (2559 / 100000 : ℝ) ≤ ℓ ^ 10 := by
    rw [show ℓ ^ 10 = ℓ ^ 5 * ℓ ^ 5 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ5_1 hℓ5_1 (by norm_num) (by positivity))
  have hℓ10_2 : ℓ ^ 10 ≤ 2562 / 100000 := by
    rw [show ℓ ^ 10 = ℓ ^ 4 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ4_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ11_2 : ℓ ^ 11 ≤ 1776 / 100000 := by
    rw [show ℓ ^ 11 = ℓ ^ 10 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ10_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ12_2 : ℓ ^ 12 ≤ 1231 / 100000 := by
    rw [show ℓ ^ 12 = ℓ ^ 6 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hc0 : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 ≤ 0 := by
    have hlin : 2 - ℓ + ℓ ^ 2 / 3 ≤ 2 - 69313 / 100000 + (48049 / 100000) / 3 := by
      linarith only [hℓ1_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 =
        (2 - ℓ + ℓ ^ 2 / 3) * s2 - 2 - ℓ ^ 2 / 6 := by ring
    linarith only [hℓ2_1, hmul, hexp]
  have hc1 : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 ≤
      -211 / 10000 := by
    have hlin : ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3 ≤
        (33307 / 100000) / 6 - (23080 / 100000) / 36 + (48049 / 100000) / 3 := by
      linarith only [hℓ3_2, hℓ4_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 =
        (ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3) * s2 + ℓ ^ 4 / 72 - 2 / 3 * ℓ ^ 2 := by ring
    linarith only [hℓ4_2, hℓ2_1, hmul, hexp]
  have hc2 : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 ≤
      1970 / 1000000 := by
    have hlin : (15997 / 100000 : ℝ) / 120 - (11094 / 100000) / 1080 + (23080 / 100000) / 36 ≤
        ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36 := by
      linarith only [hℓ5_1, hℓ6_2, hℓ4_1]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 =
        -(ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36) * s2 - ℓ ^ 6 / 2160 + ℓ ^ 4 / 18 := by ring
    linarith only [hℓ6_1, hℓ4_2, hmul, hexp]
  have hc3 : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
      (2 * s2 - 1) / 120960 * ℓ ^ 8 ≤ -392 / 10000000 := by
    have hlin : ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480 ≤
        (7691 / 100000) / 5040 + (11094 / 100000) / 1080 - (5326 / 100000) / 60480 := by
      linarith only [hℓ7_2, hℓ6_2, hℓ8_1]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8 =
        (ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480) * s2 - ℓ ^ 6 / 540 + ℓ ^ 8 / 120960 := by
      ring
    linarith only [hℓ6_1, hℓ8_2, hmul, hexp]
  have hc4 : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
      (2 * s2 - 1) / 10886400 * ℓ ^ 10 ≤ 378 / 1000000000 := by
    have hlin : (3691 / 100000 : ℝ) / 362880 + (5326 / 100000) / 60480 -
        (2562 / 100000) / 5443200 ≤
        ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200 := by
      linarith only [hℓ9_1, hℓ8_1, hℓ10_2]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10 =
        -(ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200) * s2 +
          ℓ ^ 8 / 30240 - ℓ ^ 10 / 10886400 := by ring
    linarith only [hℓ8_2, hℓ10_1, hmul, hexp]
  have hc5 : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 ≤
      -211 / 100000000000 := by
    have hlin : ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200 ≤
        (1776 / 100000) / 39916800 + (2562 / 100000) / 5443200 := by
      linarith only [hℓ11_2, hℓ10_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 =
        (ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200) * s2 - ℓ ^ 10 / 2721600 := by ring
    linarith only [hℓ10_1, hmul, hexp]
  have hc6 : (4 - 2 * s2) / 1437004800 * ℓ ^ 12 ≤ 101 / 10000000000000 := by
    have hlin : (4 - 2 * s2) / 1437004800 ≤ (4 - 2 * (8119 / 5741)) / 1437004800 := by
      linarith only [hs2_low]
    have hmul := mul_le_mul hlin hℓ12_2 (by positivity) (by norm_num)
    linarith only [hmul]
  exact first_cell_poly_of_coeffs hc0 hc1 hc2 hc3 hc4 hc5 hc6 hu_nonneg hr

/-- **Small/Medium Frequency Bound (`r ^ 2 ≤ 49`)**:
for every `r : ℝ` with `r ^ 2 ≤ 49`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x ≤ (13 / 720) * r ^ 2 * (1 / 4 + r ^ 2)`. -/
theorem neg_mul_integral_one_two_cosLogProfile_le_of_sq_le {r : ℝ} (hr : r ^ 2 ≤ 49) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
      (13 / 720) * r ^ 2 * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
  set ℓ := Real.log 2
  set s2 := Real.sqrt 2
  set u := r ^ 2
  have hu_nonneg : 0 ≤ u := sq_nonneg r
  have hℓ_low : (69313 / 100000 : ℝ) ≤ ℓ := two_panel_log_two_lower
  have hℓ_high : ℓ ≤ 14411 / 20790 :=
    log_two_le_fourteen_thousand_four_hundred_eleven_twenty_thousand_seven_hundred_ninetieths
  have hℓ_pos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓ_low
  have hs2_low : (8119 / 5741 : ℝ) ≤ s2 := eight_thousand_one_hundred_nineteen_le_sqrt_two
  have hs2_high : s2 ≤ 577 / 408 := sqrt_two_le_five_seventy_seven_four_hundred_eighths
  set θ := r * ℓ
  have hcos_up := one_sub_cos_le_taylor_degree_ten θ
  have hcos_low := taylor_degree_twelve_le_one_sub_cos θ
  have hsin_low := mul_sin_ge_taylor_degree_twelve θ
  have hsin_scaled :
      r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
        ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800) ≤
        r * Real.sin θ := by
    have hdiv := div_le_div_of_nonneg_right hsin_low hℓ_pos.le
    have h1 : (θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 +
        θ ^ 10 / 362880 - θ ^ 12 / 39916800) / ℓ =
        r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
          ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800) := by
      dsimp [θ, u]
      field_simp [hℓ_pos.ne']
    have h2 : θ * Real.sin θ / ℓ = r * Real.sin θ := by
      dsimp [θ]
      field_simp [hℓ_pos.ne']
    linarith
  have hcoeff_pos1 : 0 ≤ (2 * s2 - 1) / 3 := by linarith
  have hcoeff_pos2 : 0 ≤ ((4 - 2 * s2) / 3) * r ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg r)
  have hterm_cos1 := mul_le_mul_of_nonneg_left hcos_up hcoeff_pos1
  have hterm_cos2 := mul_le_mul_of_nonneg_left hcos_low hcoeff_pos2
  have hterm_sin := mul_le_mul_of_nonneg_left hsin_scaled (by linarith : 0 ≤ s2)
  have hpoly_id :
      2 * (s2 - 1) * r ^ 2 -
        s2 * (r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
          ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800)) +
        ((2 * s2 - 1) / 3) *
          (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800) -
        (((4 - 2 * s2) / 3) * r ^ 2) *
          (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
            θ ^ 10 / 3628800 - θ ^ 12 / 479001600) =
      u * ((2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
        (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
        (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
        (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
          (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
        (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
          (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
        (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10) * u ^ 5 +
        ((4 - 2 * s2) / 1437004800 * ℓ ^ 12) * u ^ 6) := by
    dsimp [θ, u]
    ring
  have hinner_le := first_cell_taylor_poly_le hℓ_low hℓ_high hs2_low hs2_high hu_nonneg hr
  have hprod_le := mul_le_mul_of_nonneg_left hinner_le hu_nonneg
  dsimp [u] at hprod_le hpoly_id ⊢
  linarith

/-- **Large Frequency Bound (`49 ≤ r ^ 2`)**:
for every `r : ℝ` with `49 ≤ r ^ 2`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x ≤ (13 / 720) * r ^ 2 * (1 / 4 + r ^ 2)`. -/
theorem neg_mul_integral_one_two_cosLogProfile_le_of_le_sq {r : ℝ} (hr : 49 ≤ r ^ 2) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
      (13 / 720) * r ^ 2 * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
  set s2 := Real.sqrt 2
  set u := r ^ 2
  have hu_nonneg : 0 ≤ u := by linarith
  have hs2_low : (8119 / 5741 : ℝ) ≤ s2 := eight_thousand_one_hundred_nineteen_le_sqrt_two
  have hs2_high : s2 ≤ 577 / 408 := sqrt_two_le_five_seventy_seven_four_hundred_eighths
  have hs2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsplit :
      2 * (s2 - 1) * r ^ 2 - s2 * r * Real.sin (r * Real.log 2) +
        ((2 * s2 - 1) / 3 - ((4 - 2 * s2) / 3) * r ^ 2) * (1 - Real.cos (r * Real.log 2)) =
      ((8 * s2 - 10) / 3 * u + (2 * s2 - 1) / 3) +
        ((((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
          (-s2 * r) * Real.sin (r * Real.log 2)) := by
    dsimp [u]
    ring
  have hcs := sq_linear_cos_sin_le
    (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) (-s2 * r) (r * Real.log 2)
  have hamp_sq :
      (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) ^ 2 + (-s2 * r) ^ 2 ≤
        ((391 / 1000) * u + 39 / 20) ^ 2 := by
    have hrew : (-s2 * r) ^ 2 = 2 * u := by
      dsimp [u]
      linear_combination r ^ 2 * hs2_sq
    have hcoeff_sq : (((4 - 2 * s2) / 3) ^ 2 - (391 / 1000) ^ 2) * u ^ 2 ≤ 0 := by
      refine mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg u)
      nlinarith [hs2_low, hs2_high]
    rw [hrew]
    nlinarith [hs2_low, hs2_high, hcoeff_sq]
  have hosc_le :
      (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
        (-s2 * r) * Real.sin (r * Real.log 2) ≤ (391 / 1000) * u + 39 / 20 := by
    have h1 := le_abs_self
      ((((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
        (-s2 * r) * Real.sin (r * Real.log 2))
    have h2 :
        |(((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
          (-s2 * r) * Real.sin (r * Real.log 2)| ≤ (391 / 1000) * u + 39 / 20 := by
      rw [← Real.sqrt_sq_eq_abs,
        ← Real.sqrt_sq (by positivity : 0 ≤ (391 / 1000) * u + 39 / 20)]
      exact Real.sqrt_le_sqrt (hcs.trans hamp_sq)
    exact h1.trans h2
  have hmain_le :
      ((8 * s2 - 10) / 3 * u + (2 * s2 - 1) / 3) + ((391 / 1000) * u + 39 / 20) ≤
        (13 / 720) * u * (1 / 4 + u) := by
    have hu_quad : 0 ≤ u ^ 2 - 98 * u + 2401 := by
      have h : 0 ≤ (u - 49) ^ 2 := sq_nonneg (u - 49)
      linarith [show (u - 49) ^ 2 = u ^ 2 - 98 * u + 2401 by ring]
    have hs2_u : (8 * s2 - 10) / 3 * u ≤ (8 * (577 / 408) - 10) / 3 * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu_nonneg
    linarith [hs2_high, hr, hu_quad, hs2_u,
      show (13 / 720) * u * (1 / 4 + u) = (13 / 2880) * u + (13 / 720) * u ^ 2 by ring]
  dsimp [u] at hsplit hosc_le hmain_le ⊢
  linarith

/-- **Global Pure-Second-Moment First-Cell Quadrature Inequality**:
for **every** `r : ℝ`,
`-(13 / 720) * r ^ 2 ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x`. -/
theorem neg_thirteen_seven_twentieths_mul_sq_le_integral_one_two_cosLogProfile (r : ℝ) :
    -(13 / 720) * r ^ 2 ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have hden_pos : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  have hmul :
      -(1 / 4 + r ^ 2) *
          (∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
        (13 / 720) * r ^ 2 * (1 / 4 + r ^ 2) := by
    rcases le_total (r ^ 2) 49 with hle | hge
    · exact neg_mul_integral_one_two_cosLogProfile_le_of_sq_le hle
    · exact neg_mul_integral_one_two_cosLogProfile_le_of_le_sq hge
  nlinarith

/-! ## Section 3: Clamped Product-Measure Fubini on `[1, 2] × ℝ`, the `-(65 / 3600) S - (71 / 3600) √(S(S + 2L))` Secant Numerator Law, and Upgraded Coercivity & Spectral Gap Laws -/

/-- **Clamped Product-Measure Fubini Identity on the First Cell `[1, 2]`**:
for every `f : WeilTestFn`,
`∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / Real.sqrt x = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)`. -/
theorem integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral
    (f : WeilTestFn) :
    (∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x) =
      (1 / (2 * π)) *
        ∫ r : ℝ,
          ‖paperFT f.1 r‖ ^ 2 *
            (2 * ∫ x in (1 : ℝ)..2,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) := by
  let clamp : ℝ → ℝ := fun x => min 2 (max 1 x)
  let G : ℝ → ℝ → ℝ := fun x r =>
    ‖paperFT f.1 r‖ ^ 2 *
      (2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 2 (clamp x)) /
        Real.sqrt (clamp x))
  have hclamp_eq : ∀ x ∈ Icc (1 : ℝ) 2, clamp x = x := fun x hx => by
    dsimp only [clamp]
    rw [max_eq_right hx.1, min_eq_right hx.2]
  have hclamp_ge_one : ∀ x : ℝ, 1 ≤ clamp x := fun x => by
    dsimp only [clamp]
    exact le_min (by norm_num) (le_max_left 1 x)
  have hclamp_le_two : ∀ x : ℝ, clamp x ≤ 2 := fun x => by
    dsimp only [clamp]
    exact min_le_left 2 (max 1 x)
  have hclamp_cont : Continuous clamp :=
    continuous_const.min (continuous_const.max continuous_id)
  have hG_meas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioc (1 : ℝ) 2)).prod volume) := by
    have hft_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖paperFT f.1 p.2‖ ^ 2)
        ((volume.restrict (Ioc (1 : ℝ) 2)).prod volume) :=
      (integrable_paperFT_norm_sq f).aestronglyMeasurable.comp_snd
    have hlog_clamp : Continuous fun p : ℝ × ℝ => Real.log (clamp p.1) :=
      Real.continuousOn_log.comp_continuous (hclamp_cont.comp continuous_fst) fun p =>
        (lt_of_lt_of_le zero_lt_one (hclamp_ge_one p.1)).ne'
    have hcos_clamp : Continuous fun p : ℝ × ℝ => cosLogProfile p.2 (clamp p.1) := by
      unfold cosLogProfile
      exact Real.continuous_cos.comp (continuous_snd.mul hlog_clamp)
    have hsec_clamp : Continuous fun p : ℝ × ℝ => cellSecant (cosLogProfile p.2) 2 (clamp p.1) := by
      unfold cellSecant cosLogProfile
      have h1 : Continuous fun p : ℝ × ℝ => (2 : ℝ) - clamp p.1 :=
        continuous_const.sub (hclamp_cont.comp continuous_fst)
      have h2 : Continuous fun p : ℝ × ℝ => clamp p.1 - (2 - 1) :=
        (hclamp_cont.comp continuous_fst).sub continuous_const
      have h3 : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * Real.log (2 - 1)) :=
        Real.continuous_cos.comp (continuous_snd.mul continuous_const)
      have h4 : Continuous fun p : ℝ × ℝ => Real.cos (p.2 * Real.log 2) :=
        Real.continuous_cos.comp (continuous_snd.mul continuous_const)
      exact (h1.mul h3).add (h2.mul h4)
    have hsqrt_clamp : Continuous fun p : ℝ × ℝ => Real.sqrt (clamp p.1) :=
      Real.continuous_sqrt.comp (hclamp_cont.comp continuous_fst)
    have hquot : Continuous fun p : ℝ × ℝ =>
        2 * (cosLogProfile p.2 (clamp p.1) - cellSecant (cosLogProfile p.2) 2 (clamp p.1)) /
          Real.sqrt (clamp p.1) :=
      (continuous_const.mul (hcos_clamp.sub hsec_clamp)).div hsqrt_clamp fun p =>
        (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (hclamp_ge_one p.1))).ne'
    exact hft_meas.mul hquot.aestronglyMeasurable
  have hG_bound : ∀ p : ℝ × ℝ, ‖Function.uncurry G p‖ ≤ 6 * ‖paperFT f.1 p.2‖ ^ 2 := by
    intro ⟨x, r⟩
    change ‖G x r‖ ≤ 6 * ‖paperFT f.1 r‖ ^ 2
    dsimp only [G]
    have hc1 : 1 ≤ clamp x := hclamp_ge_one x
    have hc2 : clamp x ≤ 2 := hclamp_le_two x
    have hsqrt_ge : 1 ≤ Real.sqrt (clamp x) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hc1
    have hcos_abs : |cosLogProfile r (clamp x)| ≤ 1 := Real.abs_cos_le_one _
    have hsec_abs : |cellSecant (cosLogProfile r) 2 (clamp x)| ≤ 2 := by
      unfold cellSecant
      norm_num
      have ha : |cosLogProfile r 1| ≤ 1 := Real.abs_cos_le_one _
      have hb : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
      have htri := abs_add_le ((2 - clamp x) * cosLogProfile r 1)
        ((clamp x - 1) * cosLogProfile r 2)
      have hw1 : |2 - clamp x| = 2 - clamp x := abs_of_nonneg (by linarith)
      have hw2 : |clamp x - 1| = clamp x - 1 := abs_of_nonneg (by linarith)
      rw [abs_mul, abs_mul, hw1, hw2] at htri
      nlinarith
    have hnum_abs :
        |2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 2 (clamp x))| ≤ 6 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_sub (cosLogProfile r (clamp x)) (cellSecant (cosLogProfile r) 2 (clamp x))
      linarith
    have hdiv_abs :
        |2 * (cosLogProfile r (clamp x) - cellSecant (cosLogProfile r) 2 (clamp x)) /
          Real.sqrt (clamp x)| ≤ 6 := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
      exact (div_le_self (abs_nonneg _) hsqrt_ge).trans hnum_abs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right hdiv_abs (sq_nonneg _)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (1 : ℝ) 2)) := ⟨by simp [Real.volume_Ioc]⟩
  have hprod_int : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (1 : ℝ) 2)).prod volume) :=
    Integrable.mono' ((integrable_const (6 : ℝ)).mul_prod (integrable_paperFT_norm_sq f))
      hG_meas (Eventually.of_forall hG_bound)
  have hswap := MeasureTheory.integral_integral_swap hprod_int
  have hlhs :
      (∫ x in (1 : ℝ)..2,
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
            Real.sqrt x) =
        (1 / (2 * π)) * ∫ x in Ioc (1 : ℝ) 2, ∫ r : ℝ, G x r := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_cc : x ∈ Icc (1 : ℝ) 2 := Ioc_subset_Icc_self hx
    rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f 2 x, mul_div_assoc,
      ← integral_div]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only [G]
    rw [hclamp_eq x hx_cc, mul_div_assoc]
  have hrhs :
      (∫ r : ℝ, ∫ x in Ioc (1 : ℝ) 2, G x r) =
        ∫ r : ℝ,
          ‖paperFT f.1 r‖ ^ 2 *
            (2 * ∫ x in (1 : ℝ)..2,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hx_cc : x ∈ Icc (1 : ℝ) 2 := Ioc_subset_Icc_self hx
    dsimp only [G]
    rw [hclamp_eq x hx_cc, mul_div_assoc]
  rw [hlhs, hswap, hrhs]

/-- **First-Cell Pure Second-Moment Quadrature Lower Bound**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))`,
`-(13 / 720) * spectralSecondMoment f.1 ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / Real.sqrt x`. -/
theorem neg_thirteen_seven_twentieths_spectralSecondMoment_le_integral_one_two
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    -(13 / 720) * spectralSecondMoment f.1 ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f]
  have hrhs_eq :
      -(13 / 720) * spectralSecondMoment f.1 =
        (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (-(13 / 720) * r ^ 2)) := by
    unfold spectralSecondMoment
    rw [← mul_assoc, mul_comm (-(13 / 720 : ℝ)), mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    ring
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  have hint_lhs : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 * (2 * (-(13 / 720) * r ^ 2)) := by
    have heq : (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (-(13 / 720) * r ^ 2))) =
        fun r : ℝ => (-(13 / 720)) * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) := by
      ext r; ring
    rw [heq]
    exact hint2.const_mul _
  have hint_rhs : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) := by
    have hmeas : AEStronglyMeasurable (fun r : ℝ =>
        ‖paperFT f.1 r‖ ^ 2 *
          (2 * ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) volume := by
      have h1 : AEStronglyMeasurable (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2) volume :=
        (integrable_paperFT_norm_sq f).aestronglyMeasurable
      have h2 : Continuous fun r : ℝ =>
          ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
        have hrew : (fun r : ℝ =>
            ∫ x in (1 : ℝ)..2,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) =
            fun r : ℝ =>
              -(2 * (Real.sqrt 2 - 1) * r ^ 2 - Real.sqrt 2 * r * Real.sin (r * Real.log 2) +
                ((2 * Real.sqrt 2 - 1) / 3 - ((4 - 2 * Real.sqrt 2) / 3) * r ^ 2) *
                  (1 - Real.cos (r * Real.log 2))) / (1 / 4 + r ^ 2) := by
          ext r
          have h := neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r
          have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
          apply mul_left_cancel₀ hden_ne
          rw [mul_div_cancel₀ _ hden_ne]
          linarith
        rw [hrew]
        refine Continuous.div (by fun_prop) (by fun_prop) (fun r => by positivity)
      exact h1.mul (continuous_const.mul h2).aestronglyMeasurable
    have hbound : ∀ r : ℝ,
        ‖‖paperFT f.1 r‖ ^ 2 *
          (2 * ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)‖ ≤
          6 * ‖paperFT f.1 r‖ ^ 2 := by
      intro r
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hint_abs :
          |∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x| ≤ 3 := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := 1) (b := 2) (C := 3)
          (f := fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)
          (fun x hx => by
            rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
            have hx1 : 1 ≤ x := hx.1.le
            have hx2 : x ≤ 2 := hx.2
            have hsqrt_ge : 1 ≤ Real.sqrt x := by
              rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt hx1
            have hcos_abs : |cosLogProfile r x| ≤ 1 := Real.abs_cos_le_one _
            have hsec_abs : |cellSecant (cosLogProfile r) 2 x| ≤ 2 := by
              unfold cellSecant
              norm_num
              have ha : |cosLogProfile r 1| ≤ 1 := Real.abs_cos_le_one _
              have hb : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
              have htri := abs_add_le ((2 - x) * cosLogProfile r 1)
                ((x - 1) * cosLogProfile r 2)
              have hw1 : |2 - x| = 2 - x := abs_of_nonneg (by linarith)
              have hw2 : |x - 1| = x - 1 := abs_of_nonneg (by linarith)
              rw [abs_mul, abs_mul, hw1, hw2] at htri
              nlinarith
            rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
            refine (div_le_self (abs_nonneg _) hsqrt_ge).trans ?_
            have htri := abs_sub (cosLogProfile r x) (cellSecant (cosLogProfile r) 2 x)
            linarith)
        rw [Real.norm_eq_abs] at h
        linarith [show |(2 : ℝ) - 1| = 1 by norm_num]
      nlinarith [sq_nonneg ‖paperFT f.1 r‖]
    exact Integrable.mono' ((integrable_paperFT_norm_sq f).const_mul 6)
      hmeas (Eventually.of_forall hbound)
  refine integral_mono hint_lhs hint_rhs fun r => ?_
  dsimp only
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (neg_thirteen_seven_twentieths_mul_sq_le_integral_one_two_cosLogProfile r)
      (by norm_num))
    (sq_nonneg _)

/-- **Tail Geometric-Mean Law on `Finset.Icc 3 N`**:
for every `f : WeilTestFn` and `N : ℕ`,
`-(71 / 3600) * Real.sqrt (spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ u, ‖f.1 u‖ ^ 2)) ≤ ∑ n ∈ Finset.Icc 3 N, ∫ x in (n - 1 : ℝ)..(n : ℝ), (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x`. -/
theorem neg_seventy_one_thirty_six_hundredths_sqrt_le_sum_Icc_three
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(71 / 3600) *
        Real.sqrt
          (spectralSecondMoment f.1 *
            (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      ∑ n ∈ Finset.Icc 3 N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
            Real.sqrt x := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hvar : ∀ {b : ℝ}, 0 < b →
      -(71 / 3600) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤
        ∑ n ∈ Finset.Icc 3 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
    intro b hb
    let M := (b + 1 / (4 * b)) * S + 2 * b * L
    have hM_nonneg : 0 ≤ M := by dsimp only [M]; positivity
    have hcell_le : ∀ n ∈ Finset.Icc 3 N,
        -M * hermiteQuinticCellWeight n ≤
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x := by
      intro n hn
      have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : 2 ≤ n := by omega
      have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hn_le : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
      have hint_low : IntervalIntegrable
          (fun x => -M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x))
          volume ((n : ℝ) - 1) (n : ℝ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hn_le]
        refine continuousOn_const.mul (ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) ?_)
        · refine (Real.continuousOn_log.mono ?_).sub ?_
          · intro x hx
            have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
            exact hx_pos.ne'
          · unfold cellSecant; fun_prop
        · intro x hx
          have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
          exact (Real.sqrt_pos.mpr hx_pos).ne'
      have hint_high : IntervalIntegrable
          (fun x =>
            (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
              Real.sqrt x)
          volume ((n : ℝ) - 1) (n : ℝ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hn_le]
        refine ContinuousOn.div ?_ (Real.continuous_sqrt.continuousOn) ?_
        · refine ((continuousOn_weilSymmetricLogNumerator f).mono ?_).sub ?_
          · intro x hx; exact mem_Ici.mpr (by linarith [hx.1, hn2_real])
          · unfold cellSecant; fun_prop
        · intro x hx
          have hx_pos : 0 < x := by linarith [hx.1, hn2_real]
          exact (Real.sqrt_pos.mpr hx_pos).ne'
      have hmono := intervalIntegral.integral_mono_on hn_le hint_low hint_high fun x hx => by
        have hx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx.1, hn2_real])
        have habs := (abs_le.mp
          (abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational f hint2 hb hn2 hx)).1
        have hdiv := div_le_div_of_nonneg_right habs hx_pos.le
        dsimp only [M, S, L]
        linarith [show -(((b + 1 / (4 * b)) * spectralSecondMoment f.1 +
            2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) * (Real.log x - cellSecant Real.log n x)) /
            Real.sqrt x =
          -((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) *
            ((Real.log x - cellSecant Real.log n x) / Real.sqrt x) by ring]
      rw [intervalIntegral.integral_const_mul] at hmono
      have hweight := mul_le_mul_of_nonneg_left
        (integral_log_sub_cellSecant_div_sqrt_le_hermiteQuinticCellWeight hn2) hM_nonneg
      linarith
    have hsum := Finset.sum_le_sum hcell_le
    rw [← Finset.mul_sum] at hsum
    have htail := mul_le_mul_of_nonneg_left (sum_Icc_three_hermiteQuinticCellWeight_le N) hM_nonneg
    linarith
  change -(71 / 3600) * Real.sqrt (S * (S + 2 * L)) ≤ _
  rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
  · rw [← hS0, zero_mul, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases eq_or_lt_of_le hL_nonneg with hL0 | hL_pos
    · have h1 := hvar zero_lt_one
      rw [← hS0, ← hL0] at h1
      linarith
    · let b := 1800 * ε / (71 * L)
      have hb_pos : 0 < b := by dsimp only [b]; positivity
      have h1 := hvar hb_pos
      rw [← hS0, mul_zero, zero_add] at h1
      have h2 : (71 / 3600) * (2 * b * L) = ε := by
        dsimp only [b]
        field_simp [hL_pos.ne']
        ring
      linarith
  · let P := Real.sqrt (S * (S + 2 * L))
    have hP_pos : 0 < P := Real.sqrt_pos.mpr (mul_pos hS_pos (by positivity))
    let b := S / (2 * P)
    have hb_pos : 0 < b := div_pos hS_pos (by positivity)
    have h1 := hvar hb_pos
    have hP_sq : P ^ 2 = S * (S + 2 * L) := Real.sq_sqrt (by positivity)
    have hid : (b + 1 / (4 * b)) * S + 2 * b * L = P := by
      dsimp only [b]
      have hS_ne : S ≠ 0 := hS_pos.ne'
      have hP_ne : P ≠ 0 := hP_pos.ne'
      apply mul_right_cancel₀ hP_ne
      field_simp [hS_ne, hP_ne]
      linear_combination -4 * hP_sq
    rw [hid] at h1
    exact h1

/-- **The Split First-Cell / Tail Secant Numerator Law**:
for every `f : WeilTestFn` and `N : ℕ`,
`-(65 / 3600) * spectralSecondMoment f.1 - (71 / 3600) * Real.sqrt (spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ u, ‖f.1 u‖ ^ 2)) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(65 / 3600) * spectralSecondMoment f.1 -
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment f.1 *
              (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      secantNumeratorCellDefect f.1 N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  unfold secantNumeratorCellDefect
  by_cases hN : 2 ≤ N
  · rw [sum_Icc_two_eq_add_sum_Icc_three _ hN]
    have h2 := neg_thirteen_seven_twentieths_spectralSecondMoment_le_integral_one_two f hint2
    have h3 := neg_seventy_one_thirty_six_hundredths_sqrt_le_sum_Icc_three f hint2 N
    norm_num at h2 ⊢
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    have hsqrt_nonneg : 0 ≤ Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) := Real.sqrt_nonneg _
    linarith

/-- **Universal Tangent Upper Bound `Real.sqrt (S * (S + 2 * L)) ≤ (1013 / 1012) * S + (22 / 23) * L`**:
evaluating the variational envelope at `b = 11 / 23` (`((1013 / 1012) S + (22 / 23) L)² - S(S + 2L) = ((45 / 1012) S - (22 / 23) L)² ≥ 0`) gives a linear upper bound that is exact at `S / L = 968 / 45 ≈ 21.511`. -/
theorem sqrt_spectralSecondMoment_mul_add_two_l2_le_add
    (f : WeilTestFn) :
    Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      (1013 / 1012) * spectralSecondMoment f.1 + (22 / 23) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (1013 / 1012) * S + (22 / 23) * L)]
  refine Real.sqrt_le_sqrt ?_
  have hsq : 0 ≤ ((45 / 1012) * S - (22 / 23) * L) ^ 2 := sq_nonneg _
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity up to Critical Ratio `106 / 5 = 21.2`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_hundred_six_fifths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (106 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add f
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity on the Nonnegative Log-Value Cone up to
Critical Ratio `45 / 2 = 22.5`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_forty_five_halves_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (45 / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `70 / 3 > 23.3333`**:
whenever `spectralSecondMoment f.1 ≤ (70 / 3) * ∫ ‖f.1‖²`, we have
`(1 / 360) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_three_sixtieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_seventy_thirds
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (70 / 3) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 360) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (6 / 143)
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Nonnegative Log-Value Cone up to `99 / 4 = 24.75`**: -/
theorem one_six_thousandth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_ninety_nine_fourths_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (99 / 4) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 6000) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (4 / 101)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to `99 / 4 = 24.75`**: -/
theorem one_six_thousandth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_ninety_nine_fourths_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (99 / 4) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 6000) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (4 / 101)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add f
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane up to `(70 / 3) * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_seventy_thirds_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (70 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 761
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (761 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (760 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_thousand_nine_hundred_fifty_three_thirty_six_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add (realWeilTestFn f hf hfc)
  have hcomb :=
    one_three_sixtieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_seventy_thirds
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (760 : ℝ) * ((1 / 360) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Nonnegative Log-Value Cone up to `(99 / 4) * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_ninety_nine_fourths_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (99 / 4) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 13001
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (13001 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (13000 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh hN1 hθlog hN (fun n hn => by simpa [iteratedForwardDiff] using hpos n hn)
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_sixty_five_thirty_six_hundredths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add (realWeilTestFn f hf hfc)
  have hcomb :=
    one_six_thousandth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_ninety_nine_fourths_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec_bound
  have hθ_comb :
      (13000 : ℝ) * ((1 / 6000) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `70 / 3 > 23.3333` Spectral Poincaré / Uncertainty Gap Law on the Primitive Hyperplane**: -/
theorem seventy_thirds_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (70 / 3) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_three_sixtieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_seventy_thirds
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `99 / 4 = 24.75` Spectral Poincaré / Uncertainty Gap Law on the Nonnegative Log-Value Cone**: -/
theorem ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (99 / 4) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_six_thousandth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_ninety_nine_fourths_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hle
  have hunit_nonneg :
      0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight (realWeilTestFn f hf hfc)
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn)
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `99 / 4 = 24.75` Spectral Poincaré / Uncertainty Gap Law on the Prime-Blind Cone**: -/
theorem ninety_nine_fourths_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (99 / 4) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_six_thousandth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_ninety_nine_fourths_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
