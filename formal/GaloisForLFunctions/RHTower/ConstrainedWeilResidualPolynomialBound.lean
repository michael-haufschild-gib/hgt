import GaloisForLFunctions.HTGeometry.SinCosAlternatingTaylorBounds

/-!
# Polynomial bounds for the pole-constrained Fourier residual

On the rescaled aperture `s ∈ [-1, 1]` the pole-constrained Fourier bound of a test on `(-a, a)`
involves the residual energy

`R(θ) = ∫_{-1}^{1} [(cos θs − α cosh(as/2))² + (sin θs − (2B/a) sinh(as/2))²] ds`,

the squared distance from the character `e^{-iθs}` to the approximant `α cosh(as/2) − i(2B/a) sinh(as/2)`
of the two pole directions.  This file bounds `R(θ)` uniformly on a band `|θ − θ_c| ≤ h` by an
explicit rational expression:

* the characters are replaced by the midpoints of their alternating Taylor enclosures of degree
  ten and eleven, and `cosh`, `sinh` by their Taylor polynomials with `exp_bound` remainders;
* the resulting residual polynomials `M₁ = Σ m_k s^{2k}`, `M₂ = Σ n_k s^{2k+1}` have exact
  integrals `∫_{-1}^{1} M₁² = Σ_{k,l} 2 m_k m_l/(2k+2l+1)` and `∫_{-1}^{1} M₂² = Σ_{k,l} 2 n_k n_l/(2k+2l+3)`;
* the band is absorbed by `|e^{-iθs} − e^{-iθ_c s}| ≤ |θ − θ_c||s|` and
  `(x + y)² ≤ (1 + ε)x² + (1 + 1/ε)y²`.
-/

open Real Finset MeasureTheory intervalIntegral

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Enclosures -/

theorem abs_cosh_sub_quadratic_le {z : ℝ} (hz : |z| ≤ 1) :
    |Real.cosh z - (1 + z ^ 2 / 2)| ≤ 5 * z ^ 4 / 96 := by
  have h1 := Real.exp_bound hz (n := 4) (by norm_num)
  have hz' : |-z| ≤ 1 := by rwa [abs_neg]
  have h2 := Real.exp_bound hz' (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at h1 h2
  norm_num at h1 h2
  have hz4 : |z| ^ 4 = z ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  rw [hz4] at h1 h2
  rw [Real.cosh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem abs_sinh_sub_cubic_le {z : ℝ} (hz : |z| ≤ 1) :
    |Real.sinh z - (z + z ^ 3 / 6)| ≤ |z| ^ 5 / 100 := by
  have h1 := Real.exp_bound hz (n := 5) (by norm_num)
  have hz' : |-z| ≤ 1 := by rwa [abs_neg]
  have h2 := Real.exp_bound hz' (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat] at h1 h2
  norm_num at h1 h2
  rw [Real.sinh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem cosTaylorSum_six_eq (y : ℝ) :
    cosTaylorSum 6 y = cosTaylorSum 5 y - y ^ 10 / 3628800 := by
  simp only [cosTaylorSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num
  ring

theorem sinTaylorSum_six_eq (y : ℝ) :
    sinTaylorSum 6 y = sinTaylorSum 5 y - y ^ 11 / 39916800 := by
  simp only [sinTaylorSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num
  ring

theorem sinTaylorSum_neg (n : ℕ) (y : ℝ) : sinTaylorSum n (-y) = -sinTaylorSum n y := by
  unfold sinTaylorSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Odd.neg_pow ⟨k, rfl⟩]
  ring

/-- Cosine midpoint enclosure of degree ten. -/
theorem abs_cos_sub_cosMidpoint_le (y : ℝ) :
    |Real.cos y - (cosTaylorSum 5 y - y ^ 10 / 7257600)| ≤ y ^ 10 / 7257600 := by
  have hu := cos_le_cosTaylorSum_odd 2 y
  have hl := cosTaylorSum_even_le_cos 2 y
  norm_num at hu hl
  rw [cosTaylorSum_six_eq] at hl
  rw [abs_le]
  constructor <;> linarith

/-- Sine midpoint enclosure of degree eleven. -/
theorem abs_sin_sub_sinMidpoint_le (y : ℝ) :
    |Real.sin y - (sinTaylorSum 5 y - y ^ 11 / 79833600)| ≤ |y| ^ 11 / 79833600 := by
  have key : ∀ x, 0 ≤ x →
      |Real.sin x - (sinTaylorSum 5 x - x ^ 11 / 79833600)| ≤ x ^ 11 / 79833600 := by
    intro x hx
    have hu := sin_le_sinTaylorSum_odd 2 hx
    have hl := sinTaylorSum_even_le_sin 2 hx
    norm_num at hu hl
    rw [sinTaylorSum_six_eq] at hl
    rw [abs_le]
    constructor <;> linarith
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · have h := key (-y) (by linarith)
    rw [Real.sin_neg, sinTaylorSum_neg, abs_of_nonpos hy] at *
    rw [show -Real.sin y - (-sinTaylorSum 5 y - (-y) ^ 11 / 79833600) =
      -(Real.sin y - (sinTaylorSum 5 y - y ^ 11 / 79833600)) by ring, abs_neg] at h
    exact h

/-! ## Residual polynomials -/

/-- Coefficients of the even residual polynomial `M₁(s) = Σ_k m_k s^{2k}`. -/
noncomputable def evenResidualCoeff (θ α A2 : ℝ) : ℕ → ℝ
  | 0 => 1 - α
  | 1 => -θ ^ 2 / 2 - α * A2 / 8
  | 2 => θ ^ 4 / 24
  | 3 => -θ ^ 6 / 720
  | 4 => θ ^ 8 / 40320
  | 5 => -θ ^ 10 / 7257600
  | _ => 0

/-- Coefficients of the odd residual polynomial `M₂(s) = Σ_k n_k s^{2k+1}`. -/
noncomputable def oddResidualCoeff (θ B A2 : ℝ) : ℕ → ℝ
  | 0 => θ - B
  | 1 => -θ ^ 3 / 6 - B * A2 / 24
  | 2 => θ ^ 5 / 120
  | 3 => -θ ^ 7 / 5040
  | 4 => θ ^ 9 / 362880
  | 5 => -θ ^ 11 / 79833600
  | _ => 0

theorem evenResidual_eq (θ α A2 s : ℝ) :
    cosTaylorSum 5 (θ * s) - (θ * s) ^ 10 / 7257600 - α * (1 + A2 * s ^ 2 / 8) =
      ∑ k ∈ range 6, evenResidualCoeff θ α A2 k * s ^ (2 * k) := by
  simp only [cosTaylorSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    evenResidualCoeff]
  norm_num
  ring

theorem oddResidual_eq (θ B A2 s : ℝ) :
    sinTaylorSum 5 (θ * s) - (θ * s) ^ 11 / 79833600 - B * (s + A2 * s ^ 3 / 24) =
      ∑ k ∈ range 6, oddResidualCoeff θ B A2 k * s ^ (2 * k + 1) := by
  simp only [sinTaylorSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
    oddResidualCoeff]
  norm_num
  ring

/-- `∫_{-1}^{1} (Σ_k m_k s^{2k})² = Σ_{k,l} 2 m_k m_l/(2k+2l+1)`. -/
theorem integral_evenPoly_sq (N : ℕ) (m : ℕ → ℝ) :
    (∫ s in (-1 : ℝ)..1, (∑ k ∈ range N, m k * s ^ (2 * k)) ^ 2) =
      ∑ k ∈ range N, ∑ l ∈ range N, m k * m l * (2 / (2 * k + 2 * l + 1)) := by
  have hexp : (fun s : ℝ => (∑ k ∈ range N, m k * s ^ (2 * k)) ^ 2) =
      fun s => ∑ k ∈ range N, ∑ l ∈ range N, m k * m l * s ^ (2 * k + 2 * l) := by
    funext s
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [pow_add]; ring
  rw [hexp, intervalIntegral.integral_finsetSum (fun k _ => ?_)]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_finsetSum (fun l _ => ?_)]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [intervalIntegral.integral_const_mul, integral_pow]
      have hodd : Odd (2 * k + 2 * l + 1) := ⟨k + l, by ring⟩
      rw [hodd.neg_pow, one_pow]
      push_cast
      ring
    · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  · exact (continuous_finsetSum _ (fun l _ =>
      continuous_const.mul (continuous_pow _))).intervalIntegrable _ _

/-- `∫_{-1}^{1} (Σ_k n_k s^{2k+1})² = Σ_{k,l} 2 n_k n_l/(2k+2l+3)`. -/
theorem integral_oddPoly_sq (N : ℕ) (n : ℕ → ℝ) :
    (∫ s in (-1 : ℝ)..1, (∑ k ∈ range N, n k * s ^ (2 * k + 1)) ^ 2) =
      ∑ k ∈ range N, ∑ l ∈ range N, n k * n l * (2 / (2 * k + 2 * l + 3)) := by
  have hexp : (fun s : ℝ => (∑ k ∈ range N, n k * s ^ (2 * k + 1)) ^ 2) =
      fun s => ∑ k ∈ range N, ∑ l ∈ range N, n k * n l * s ^ (2 * k + 2 * l + 2) := by
    funext s
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show 2 * k + 2 * l + 2 = (2 * k + 1) + (2 * l + 1) by ring, pow_add]; ring
  rw [hexp, intervalIntegral.integral_finsetSum (fun k _ => ?_)]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_finsetSum (fun l _ => ?_)]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [intervalIntegral.integral_const_mul, integral_pow]
      have hodd : Odd (2 * k + 2 * l + 2 + 1) := ⟨k + l + 1, by ring⟩
      rw [hodd.neg_pow, one_pow]
      push_cast
      ring
    · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  · exact (continuous_finsetSum _ (fun l _ =>
      continuous_const.mul (continuous_pow _))).intervalIntegrable _ _

/-- The even residual energy `∫_{-1}^{1} M₁²`. -/
noncomputable def evenResidualEnergy (θ α A2 : ℝ) : ℝ :=
  ∑ k ∈ range 6, ∑ l ∈ range 6,
    evenResidualCoeff θ α A2 k * evenResidualCoeff θ α A2 l * (2 / (2 * k + 2 * l + 1))

/-- The odd residual energy `∫_{-1}^{1} M₂²`. -/
noncomputable def oddResidualEnergy (θ B A2 : ℝ) : ℝ :=
  ∑ k ∈ range 6, ∑ l ∈ range 6,
    oddResidualCoeff θ B A2 k * oddResidualCoeff θ B A2 l * (2 / (2 * k + 2 * l + 3))

/-- The uniform band bound for the residual energy. -/
noncomputable def residualBandBound (θc α B A2 ea a4 ε ε' h : ℝ) : ℝ :=
  (1 + ε) * ((1 + ε') * (evenResidualEnergy θc α A2 + oddResidualEnergy θc B A2) +
      (1 + 1 / ε') * 2 * ((θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536)) ^ 2 +
        (θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600)) ^ 2)) +
    (1 + 1 / ε) * (2 / 3) * h ^ 2

/-- `(x + y)² ≤ (1 + ε) x² + (1 + 1/ε) y²`. -/
theorem sq_add_le_weighted {x y ε : ℝ} (hε : 0 < ε) :
    (x + y) ^ 2 ≤ (1 + ε) * x ^ 2 + (1 + 1 / ε) * y ^ 2 := by
  have h : 0 ≤ (ε * x - y) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have hexp : (1 + ε) * x ^ 2 + (1 + 1 / ε) * y ^ 2 - (x + y) ^ 2 = (ε * x - y) ^ 2 / ε := by
    field_simp; ring
  linarith

theorem abs_sub_sub_le (x y z : ℝ) : |x - y - z| ≤ |x| + |y| + |z| := by
  have h1 := abs_sub (x - y) z
  have h2 := abs_sub x y
  linarith

theorem sq_le_sq_of_abs_le {x d : ℝ} (h : |x| ≤ d) : x ^ 2 ≤ d ^ 2 := by
  have hd : 0 ≤ d := le_trans (abs_nonneg x) h
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- The even residual differs from its polynomial model by at most `Δ₁`. -/
theorem abs_evenResidual_error_le {a θc α A2 ea a4 s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA2 : |a ^ 2 - A2| ≤ ea) (ha4 : a ^ 4 ≤ a4) (hα : 0 ≤ α) (hθ : 0 ≤ θc) (hs : |s| ≤ 1) :
    |Real.cos (θc * s) - α * Real.cosh (a * s / 2) -
      (cosTaylorSum 5 (θc * s) - (θc * s) ^ 10 / 7257600 - α * (1 + A2 * s ^ 2 / 8))| ≤
      θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536) := by
  have habs : 0 ≤ |s| := abs_nonneg s
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_abs s]
  have hsn : ∀ n : ℕ, |s| ^ n ≤ 1 := fun n => pow_le_one₀ habs hs
  have hz : |a * s / 2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos ha, abs_two]
    nlinarith
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) hA2
  have hcos := abs_cos_sub_cosMidpoint_le (θc * s)
  have hcosh := abs_cosh_sub_quadratic_le hz
  have hdecomp : Real.cos (θc * s) - α * Real.cosh (a * s / 2) -
      (cosTaylorSum 5 (θc * s) - (θc * s) ^ 10 / 7257600 - α * (1 + A2 * s ^ 2 / 8)) =
      (Real.cos (θc * s) - (cosTaylorSum 5 (θc * s) - (θc * s) ^ 10 / 7257600)) -
        α * (Real.cosh (a * s / 2) - (1 + (a * s / 2) ^ 2 / 2)) -
        α * ((a ^ 2 - A2) * s ^ 2 / 8) := by ring
  rw [hdecomp]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hα]
  have hy10 : (θc * s) ^ 10 / 7257600 ≤ θc ^ 10 / 7257600 := by
    have e : (θc * s) ^ 10 = θc ^ 10 * |s| ^ 10 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 10)]
    rw [e]
    have := mul_le_mul_of_nonneg_left (hsn 10) (pow_nonneg hθ 10)
    linarith
  have hz4 : 5 * (a * s / 2) ^ 4 / 96 ≤ 5 * a4 / 1536 := by
    have h4 : (a * s / 2) ^ 4 = a ^ 4 * |s| ^ 4 / 16 := by
      rw [div_pow, mul_pow, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 4)]
      ring
    rw [h4]
    have := mul_le_mul ha4 (hsn 4) (by positivity) (le_trans (by positivity) ha4)
    linarith
  have hA2s : |(a ^ 2 - A2) * s ^ 2 / 8| ≤ ea / 8 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s), abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    have := mul_le_mul hA2 hs2 (sq_nonneg s) hea
    linarith
  have h1 := hcos.trans hy10
  have h2 := mul_le_mul_of_nonneg_left (hcosh.trans hz4) hα
  have h3 := mul_le_mul_of_nonneg_left hA2s hα
  have hsplit : α * (ea / 8 + 5 * a4 / 1536) = α * (ea / 8) + α * (5 * a4 / 1536) := by ring
  linarith

/-- The odd residual differs from its polynomial model by at most `Δ₂`. -/
theorem abs_oddResidual_error_le {a θc B A2 ea a4 s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA2 : |a ^ 2 - A2| ≤ ea) (ha4 : a ^ 4 ≤ a4) (hB : 0 ≤ B) (hθ : 0 ≤ θc) (hs : |s| ≤ 1) :
    |Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2) -
      (sinTaylorSum 5 (θc * s) - (θc * s) ^ 11 / 79833600 - B * (s + A2 * s ^ 3 / 24))| ≤
      θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600) := by
  have habs : 0 ≤ |s| := abs_nonneg s
  have hsn : ∀ n : ℕ, |s| ^ n ≤ 1 := fun n => pow_le_one₀ habs hs
  have hz : |a * s / 2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos ha, abs_two]
    nlinarith
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) hA2
  have hsin := abs_sin_sub_sinMidpoint_le (θc * s)
  have hsinh := abs_sinh_sub_cubic_le hz
  have hdecomp : Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2) -
      (sinTaylorSum 5 (θc * s) - (θc * s) ^ 11 / 79833600 - B * (s + A2 * s ^ 3 / 24)) =
      (Real.sin (θc * s) - (sinTaylorSum 5 (θc * s) - (θc * s) ^ 11 / 79833600)) -
        (2 * B / a) * (Real.sinh (a * s / 2) - (a * s / 2 + (a * s / 2) ^ 3 / 6)) -
        B * ((a ^ 2 - A2) * s ^ 3 / 24) := by
    field_simp
    ring
  rw [hdecomp]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hB, abs_of_nonneg (by positivity : 0 ≤ 2 * B / a)]
  have hy11 : |θc * s| ^ 11 / 79833600 ≤ θc ^ 11 / 79833600 := by
    rw [abs_mul, abs_of_nonneg hθ, mul_pow]
    have := mul_le_mul_of_nonneg_left (hsn 11) (pow_nonneg hθ 11)
    linarith
  have hz5 : 2 * B / a * (|a * s / 2| ^ 5 / 100) ≤ B * (a4 / 1600) := by
    have h5 : |a * s / 2| ^ 5 = a ^ 5 * |s| ^ 5 / 32 := by
      rw [abs_div, abs_mul, abs_of_pos ha, abs_two, div_pow, mul_pow]
      norm_num
    rw [h5]
    have hkey : 2 * B / a * (a ^ 5 * |s| ^ 5 / 32 / 100) = B * (a ^ 4 * |s| ^ 5 / 1600) := by
      field_simp
      ring
    rw [hkey]
    have := mul_le_mul ha4 (hsn 5) (by positivity) (le_trans (by positivity) ha4)
    exact mul_le_mul_of_nonneg_left (by linarith) hB
  have hA2s : |(a ^ 2 - A2) * s ^ 3 / 24| ≤ ea / 24 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24), abs_pow]
    have := mul_le_mul hA2 (hsn 3) (by positivity) hea
    linarith
  have h1 := hsin.trans hy11
  have h2 := mul_le_mul_of_nonneg_left hsinh (by positivity : 0 ≤ 2 * B / a)
  have h3 := mul_le_mul_of_nonneg_left hA2s hB
  have hsplit : B * (ea / 24 + a4 / 1600) = B * (ea / 24) + B * (a4 / 1600) := by ring
  linarith

/-- Pointwise residual bound at the band centre. -/
theorem centre_residual_le {a θc α B A2 ea a4 ε' s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hA2 : |a ^ 2 - A2| ≤ ea) (ha4 : a ^ 4 ≤ a4) (hα : 0 ≤ α) (hB : 0 ≤ B) (hθ : 0 ≤ θc)
    (hε' : 0 < ε') (hs : |s| ≤ 1) :
    (Real.cos (θc * s) - α * Real.cosh (a * s / 2)) ^ 2 +
        (Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2 ≤
      (1 + ε') * ((∑ k ∈ range 6, evenResidualCoeff θc α A2 k * s ^ (2 * k)) ^ 2 +
          (∑ k ∈ range 6, oddResidualCoeff θc B A2 k * s ^ (2 * k + 1)) ^ 2) +
        (1 + 1 / ε') * ((θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536)) ^ 2 +
          (θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600)) ^ 2) := by
  rw [← evenResidual_eq, ← oddResidual_eq]
  set r1 := Real.cos (θc * s) - α * Real.cosh (a * s / 2)
  set r2 := Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2)
  set M1 := cosTaylorSum 5 (θc * s) - (θc * s) ^ 10 / 7257600 - α * (1 + A2 * s ^ 2 / 8)
  set M2 := sinTaylorSum 5 (θc * s) - (θc * s) ^ 11 / 79833600 - B * (s + A2 * s ^ 3 / 24)
  set D1 := θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536)
  set D2 := θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600)
  have e1 := sq_add_le_weighted (x := M1) (y := r1 - M1) hε'
  have e2 := sq_add_le_weighted (x := M2) (y := r2 - M2) hε'
  rw [show M1 + (r1 - M1) = r1 by ring] at e1
  rw [show M2 + (r2 - M2) = r2 by ring] at e2
  have f1 : (r1 - M1) ^ 2 ≤ D1 ^ 2 :=
    sq_le_sq_of_abs_le (abs_evenResidual_error_le ha ha1 hA2 ha4 hα hθ hs)
  have f2 : (r2 - M2) ^ 2 ≤ D2 ^ 2 :=
    sq_le_sq_of_abs_le (abs_oddResidual_error_le ha ha1 hA2 ha4 hB hθ hs)
  have hc : (0 : ℝ) ≤ 1 + 1 / ε' := by positivity
  have g1 := mul_le_mul_of_nonneg_left f1 hc
  have g2 := mul_le_mul_of_nonneg_left f2 hc
  have hexp : (1 + ε') * (M1 ^ 2 + M2 ^ 2) + (1 + 1 / ε') * (D1 ^ 2 + D2 ^ 2) =
      (1 + ε') * M1 ^ 2 + (1 + ε') * M2 ^ 2 + ((1 + 1 / ε') * D1 ^ 2 + (1 + 1 / ε') * D2 ^ 2) := by
    ring
  rw [hexp]
  linarith

/-- The characters move by at most `|θ − θ_c||s|`. -/
theorem character_shift_sq_le (θ θc s : ℝ) :
    (Real.cos (θ * s) - Real.cos (θc * s)) ^ 2 + (Real.sin (θ * s) - Real.sin (θc * s)) ^ 2 ≤
      (θ - θc) ^ 2 * s ^ 2 := by
  have hid : (Real.cos (θ * s) - Real.cos (θc * s)) ^ 2 + (Real.sin (θ * s) - Real.sin (θc * s)) ^ 2 =
      2 - 2 * Real.cos (θ * s - θc * s) := by
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq (θ * s), Real.sin_sq_add_cos_sq (θc * s)]
  rw [hid]
  have := Real.one_sub_sq_div_two_le_cos (x := θ * s - θc * s)
  nlinarith

/-- The residual centre bound, abbreviated. -/
noncomputable def residualCentreBound (θc α B A2 ea a4 ε' s : ℝ) : ℝ :=
  (1 + ε') * ((∑ k ∈ range 6, evenResidualCoeff θc α A2 k * s ^ (2 * k)) ^ 2 +
      (∑ k ∈ range 6, oddResidualCoeff θc B A2 k * s ^ (2 * k + 1)) ^ 2) +
    (1 + 1 / ε') * ((θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536)) ^ 2 +
      (θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600)) ^ 2)

/-- Pointwise band bound. -/
theorem band_residual_pointwise_le {a θc θ α B A2 ea a4 ε ε' h s : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hA2 : |a ^ 2 - A2| ≤ ea) (ha4 : a ^ 4 ≤ a4) (hα : 0 ≤ α) (hB : 0 ≤ B)
    (hθc : 0 ≤ θc) (hε : 0 < ε) (hε' : 0 < ε') (hθ : |θ - θc| ≤ h) (hs : |s| ≤ 1) :
    (Real.cos (θ * s) - α * Real.cosh (a * s / 2)) ^ 2 +
        (Real.sin (θ * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2 ≤
      (1 + ε) * residualCentreBound θc α B A2 ea a4 ε' s + (1 + 1 / ε) * h ^ 2 * s ^ 2 := by
  have hc : (Real.cos (θc * s) - α * Real.cosh (a * s / 2)) ^ 2 +
      (Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2 ≤
      residualCentreBound θc α B A2 ea a4 ε' s :=
    centre_residual_le ha ha1 hA2 ha4 hα hB hθc hε' hs
  set x1 := Real.cos (θc * s) - α * Real.cosh (a * s / 2)
  set x2 := Real.sin (θc * s) - 2 * B / a * Real.sinh (a * s / 2)
  set y1 := Real.cos (θ * s) - Real.cos (θc * s)
  set y2 := Real.sin (θ * s) - Real.sin (θc * s)
  have e1 := sq_add_le_weighted (x := x1) (y := y1) hε
  have e2 := sq_add_le_weighted (x := x2) (y := y2) hε
  have hx1 : x1 + y1 = Real.cos (θ * s) - α * Real.cosh (a * s / 2) := by
    simp only [x1, y1]; ring
  have hx2 : x2 + y2 = Real.sin (θ * s) - 2 * B / a * Real.sinh (a * s / 2) := by
    simp only [x2, y2]; ring
  rw [← hx1, ← hx2]
  have hsh : y1 ^ 2 + y2 ^ 2 ≤ (θ - θc) ^ 2 * s ^ 2 := character_shift_sq_le θ θc s
  have hθ2 : (θ - θc) ^ 2 ≤ h ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hsh' : (θ - θc) ^ 2 * s ^ 2 ≤ h ^ 2 * s ^ 2 :=
    mul_le_mul_of_nonneg_right hθ2 (sq_nonneg s)
  have hc1 : (0 : ℝ) ≤ 1 + 1 / ε := by positivity
  have hcε : (0 : ℝ) ≤ 1 + ε := by positivity
  have hcs := mul_le_mul_of_nonneg_left hc hcε
  have hss := mul_le_mul_of_nonneg_left (hsh.trans hsh') hc1
  have k1 : (1 + ε) * (x1 ^ 2 + x2 ^ 2) = (1 + ε) * x1 ^ 2 + (1 + ε) * x2 ^ 2 := by ring
  have k2 : (1 + 1 / ε) * (y1 ^ 2 + y2 ^ 2) = (1 + 1 / ε) * y1 ^ 2 + (1 + 1 / ε) * y2 ^ 2 := by
    ring
  have k3 : (1 + 1 / ε) * h ^ 2 * s ^ 2 = (1 + 1 / ε) * (h ^ 2 * s ^ 2) := by ring
  linarith

/-- **Band bound for the residual energy.**  For `|θ − θ_c| ≤ h`,
`∫_{-1}^{1} [(cos θs − α cosh(as/2))² + (sin θs − (2B/a) sinh(as/2))²] ds` is at most the explicit
rational expression `residualBandBound`. -/
theorem integral_residual_le_residualBandBound {a θc θ α B A2 ea a4 ε ε' h : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hA2 : |a ^ 2 - A2| ≤ ea) (ha4 : a ^ 4 ≤ a4) (hα : 0 ≤ α) (hB : 0 ≤ B)
    (hθc : 0 ≤ θc) (hε : 0 < ε) (hε' : 0 < ε') (hθ : |θ - θc| ≤ h) :
    (∫ s in (-1 : ℝ)..1, ((Real.cos (θ * s) - α * Real.cosh (a * s / 2)) ^ 2 +
        (Real.sin (θ * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2)) ≤
      residualBandBound θc α B A2 ea a4 ε ε' h := by
  have hpt : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      (Real.cos (θ * s) - α * Real.cosh (a * s / 2)) ^ 2 +
        (Real.sin (θ * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2 ≤
      (1 + ε) * residualCentreBound θc α B A2 ea a4 ε' s + (1 + 1 / ε) * h ^ 2 * s ^ 2 :=
    fun s hs => band_residual_pointwise_le ha ha1 hA2 ha4 hα hB hθc hε hε' hθ
      (abs_le.2 ⟨hs.1, hs.2⟩)
  have hcontL : Continuous fun s : ℝ => (Real.cos (θ * s) - α * Real.cosh (a * s / 2)) ^ 2 +
      (Real.sin (θ * s) - 2 * B / a * Real.sinh (a * s / 2)) ^ 2 := by fun_prop
  have hP1 : Continuous fun s : ℝ => ∑ k ∈ range 6, evenResidualCoeff θc α A2 k * s ^ (2 * k) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_pow _))
  have hP2 : Continuous fun s : ℝ =>
      ∑ k ∈ range 6, oddResidualCoeff θc B A2 k * s ^ (2 * k + 1) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_pow _))
  have hcontR : Continuous fun s : ℝ =>
      (1 + ε) * residualCentreBound θc α B A2 ea a4 ε' s + (1 + 1 / ε) * h ^ 2 * s ^ 2 := by
    unfold residualCentreBound
    fun_prop
  refine (intervalIntegral.integral_mono_on (by norm_num) (hcontL.intervalIntegrable _ _)
    (hcontR.intervalIntegrable _ _) hpt).trans (le_of_eq ?_)
  set P1 : ℝ → ℝ := fun s => ∑ k ∈ range 6, evenResidualCoeff θc α A2 k * s ^ (2 * k) with hP1def
  set P2 : ℝ → ℝ := fun s => ∑ k ∈ range 6, oddResidualCoeff θc B A2 k * s ^ (2 * k + 1)
    with hP2def
  set c1 := (1 + ε) * (1 + ε')
  set c2 := (1 + ε) * (1 + 1 / ε') * ((θc ^ 10 / 7257600 + α * (ea / 8 + 5 * a4 / 1536)) ^ 2 +
    (θc ^ 11 / 79833600 + B * (ea / 24 + a4 / 1600)) ^ 2)
  set c3 := (1 + 1 / ε) * h ^ 2
  have i1 : IntervalIntegrable (fun s => c1 * P1 s ^ 2) volume (-1) 1 :=
    ((hP1.pow 2).const_mul c1).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => c1 * P2 s ^ 2) volume (-1) 1 :=
    ((hP2.pow 2).const_mul c1).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun _ : ℝ => c2) volume (-1) 1 := intervalIntegrable_const
  have i4 : IntervalIntegrable (fun s : ℝ => c3 * s ^ 2) volume (-1) 1 :=
    ((continuous_pow 2).const_mul c3).intervalIntegrable _ _
  have hlin : (fun s : ℝ => (1 + ε) * residualCentreBound θc α B A2 ea a4 ε' s +
      (1 + 1 / ε) * h ^ 2 * s ^ 2) =
      fun s => ((c1 * P1 s ^ 2 + c1 * P2 s ^ 2) + c2) + c3 * s ^ 2 := by
    funext s; simp only [P1, P2, c1, c2, c3]; unfold residualCentreBound; ring
  rw [hlin, intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow,
    integral_evenPoly_sq 6 (evenResidualCoeff θc α A2),
    integral_oddPoly_sq 6 (oddResidualCoeff θc B A2)]
  unfold residualBandBound evenResidualEnergy oddResidualEnergy
  simp only [c1, c2, c3]
  norm_num
  ring

end RHTower
