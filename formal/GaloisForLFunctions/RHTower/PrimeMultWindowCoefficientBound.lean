import GaloisForLFunctions.RHTower.PrimeMultWindowSecondMoment

/-!
# The near-sum coefficient bound at a free window ratio

`sq_norm_mul_rpow_le_zeroShortWeight` bounds a near-sum coefficient by the zero weight, but it is
stated with the window ratio in the form `X^{θ-1}`.  Any positive ratio is of that form: for `X > 1`
and `δ > 0`, taking `θ = 1 + log δ / log X` gives `X^{θ-1} = δ`.  Specialising at that exponent turns
the coefficient sums of `multWindowMoment` into `25 δ²` times a weight sum, with the weight parameter
`192/(5 ε δ²)`.
-/

set_option autoImplicit false

namespace RHTower

open MeasureTheory

noncomputable section

/-- The exponent realising a given window ratio at a given scale. -/
def ratioExponent (δ X : ℝ) : ℝ := 1 + Real.log δ / Real.log X

/-- `X^{θ-1} = δ` for `θ = ratioExponent δ X`, when `1 < X` and `0 < δ`. -/
theorem rpow_ratioExponent_sub_one {δ X : ℝ} (hX : 1 < X) (hδ : 0 < δ) :
    X ^ (ratioExponent δ X - 1) = δ := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog : Real.log X ≠ 0 := by
    have : 0 < Real.log X := Real.log_pos hX
    exact ne_of_gt this
  rw [ratioExponent, add_sub_cancel_left, Real.rpow_def_of_pos hX0,
    mul_comm, div_mul_cancel₀ _ hlog]
  exact Real.exp_log hδ

/-- `(X²)^{2((1-θ)/2)} = δ⁻²` for `θ = ratioExponent δ X`. -/
theorem rpow_ratioExponent_weight {δ X : ℝ} (hX : 1 < X) (hδ : 0 < δ) :
    (X ^ 2) ^ (2 * ((1 - ratioExponent δ X) / 2)) = δ⁻¹ ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX20 : (0 : ℝ) < X ^ 2 := by positivity
  have hkey : (X ^ 2) ^ (2 * ((1 - ratioExponent δ X) / 2))
      = (X ^ (ratioExponent δ X - 1)) ^ (-2 : ℝ) := by
    rw [show (2 : ℝ) * ((1 - ratioExponent δ X) / 2) = -(ratioExponent δ X - 1) by ring]
    rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le]
    congr 1
    push_cast
    ring
  rw [hkey, rpow_ratioExponent_sub_one hX hδ,
    show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hδ.le, Real.rpow_natCast]
  exact (inv_pow δ 2).symm

/-- **The coefficient sum of the inner near sum.**  Mirrors the bound used for the multiplicative
window, at a free ratio `δ`. -/
theorem sum_sq_norm_multWindowCoeff_le {δ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 1 < X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∑ q ∈ almostAllLowZeros X,
        ‖multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 25 * δ ^ 2 * ∑ q ∈ almostAllLowZeros X,
          zeroShortWeight (X ^ 2) (192 / (5 * ε) * δ⁻¹ ^ 2) (q.1 : ℂ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hη0 : (0 : ℝ) < ε * δ / 16 := by positivity
  have h2η : 2 * (ε * δ / 16) ≤ δ := by nlinarith
  have hη4 : ε * δ / 16 ≤ 1 / 4 := by nlinarith
  have hrat := rpow_ratioExponent_sub_one hX hδ0
  have hwt := rpow_ratioExponent_weight hX hδ0
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h5 : ‖multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)‖ ≤ 5 * X ^ (ratioExponent δ X - 1) := by
    rw [hrat]
    have := norm_multWindowCoeff_le_two_mul hη0 h2η (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    linarith
  have h12 : ‖multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)‖
      ≤ 12 / (ε * X ^ (ratioExponent δ X - 1) / 16
          * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by
    rw [hrat]
    have := norm_multWindowCoeff_le_div hη0 h2η (by linarith) (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    refine le_trans this (le_of_eq ?_)
    field_simp
  have h := sq_norm_mul_rpow_le_zeroShortWeight (θ := ratioExponent δ X) hε hX0 h5 h12
  rw [hrat, hwt] at h
  exact h

/-- **The coefficient sum of the outer near sum.** -/
theorem sum_sq_norm_multWindowCoeffOuter_le {δ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 1 < X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∑ q ∈ almostAllLowZeros X,
        ‖multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 25 * δ ^ 2 * ∑ q ∈ almostAllLowZeros X,
          zeroShortWeight (X ^ 2) (192 / (5 * ε) * δ⁻¹ ^ 2) (q.1 : ℂ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hη0 : (0 : ℝ) < ε * δ / 16 := by positivity
  have h2η : 2 * (ε * δ / 16) ≤ δ := by nlinarith
  have hη4 : ε * δ / 16 ≤ 1 / 4 := by nlinarith
  have hrat := rpow_ratioExponent_sub_one hX hδ0
  have hwt := rpow_ratioExponent_weight hX hδ0
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h5 : ‖multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)‖
      ≤ 5 * X ^ (ratioExponent δ X - 1) := by
    rw [hrat]
    have hb := norm_multWindowCoeffOuter_le hη0 (by linarith) hδ0.le (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    nlinarith [hb, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) hδ0.le]
  have h12 : ‖multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)‖
      ≤ 12 / (ε * X ^ (ratioExponent δ X - 1) / 16
          * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by
    rw [hrat]
    have hbase := norm_multWindowCoeffOuter_le_div hη0 hη4 hδ0.le hδ (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    refine le_trans hbase ?_
    have hρne := xiZeroCopy_ne_zero q
    have hρ1ne : 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero q
    have hP0 : 0 < ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ :=
      mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
    have he : ε * δ / 16 * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖) > 0 := by positivity
    rw [div_le_div_iff₀ he he]
    nlinarith [hP0]
  have h := sq_norm_mul_rpow_le_zeroShortWeight (θ := ratioExponent δ X) hε hX0 h5 h12
  rw [hrat, hwt] at h
  exact h


/-- `almostAllHarmonicWeight` is nonnegative. -/
theorem almostAllHarmonicWeight_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ almostAllHarmonicWeight X := by
  rw [almostAllHarmonicWeight]
  have hX4 : (1 : ℝ) ≤ X ^ 4 := one_le_pow₀ hX
  have h1 : (0 : ℝ) ≤ Real.log (3 * X ^ 4 + 4) := Real.log_nonneg (by linarith)
  have h2 : (0 : ℝ) ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by linarith)
  positivity

/-- **The dyadic second moment in terms of the zero weight.**  Both near-sum coefficient sums are
at most `25δ²` times the weight sum, so the whole moment is. -/
theorem multWindowMoment_le {δ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 1 < X)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    multWindowMoment δ ε X
      ≤ 3 * ((3 * ε / 16) ^ 2 * δ ^ 2 * (7 * X ^ 3 / 3)
          + 2 * ((2 * X) ^ 3 * (4 * almostAllHarmonicWeight X * (25 * δ ^ 2 *
              ∑ q ∈ almostAllLowZeros X,
                zeroShortWeight (X ^ 2) (192 / (5 * ε) * δ⁻¹ ^ 2) (q.1 : ℂ))))) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hW0 : 0 ≤ almostAllHarmonicWeight X := almostAllHarmonicWeight_nonneg (by linarith)
  have hcube : (0 : ℝ) ≤ (2 * X) ^ 3 := by positivity
  have hD := sum_sq_norm_multWindowCoeff_le hε hε1 hX hδ0 hδ
  have hE := sum_sq_norm_multWindowCoeffOuter_le hε hε1 hX hδ0 hδ
  rw [multWindowMoment]
  have hstepD : (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X *
      ∑ q ∈ almostAllLowZeros X,
        ‖multWindowCoeff δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2))
      ≤ (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X * (25 * δ ^ 2 *
          ∑ q ∈ almostAllLowZeros X,
            zeroShortWeight (X ^ 2) (192 / (5 * ε) * δ⁻¹ ^ 2) (q.1 : ℂ))) := by
    gcongr
  have hstepE : (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X *
      ∑ q ∈ almostAllLowZeros X,
        ‖multWindowCoeffOuter δ (ε * δ / 16) (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2))
      ≤ (2 * X) ^ 3 * (4 * almostAllHarmonicWeight X * (25 * δ ^ 2 *
          ∑ q ∈ almostAllLowZeros X,
            zeroShortWeight (X ^ 2) (192 / (5 * ε) * δ⁻¹ ^ 2) (q.1 : ℂ))) := by
    gcongr
  linarith [hstepD, hstepE]

end

end RHTower
