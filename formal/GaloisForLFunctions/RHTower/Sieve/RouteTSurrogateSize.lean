import GaloisForLFunctions.RHTower.Sieve.RouteTTailElementary

/-!
# The size of the tail surrogates

The surrogates of `Sieve/RouteTTailSurrogate` are closed but still nested: the height surrogate sits
inside a ninth-tenths power and inside a logarithm.  Here both are majorised by a single increasing
function of `log|t|` alone,

```text
   routeTHeightBudget t      = 23 + 2·log|t| ,
   routeTReciprocalBudget A t = 10·D_A·(routeTHeightBudget t)^{9/10}·(1 + log routeTHeightBudget t)² ,
```

after which the three tail regimes read as inequalities in `log i` and `log|t|` only.
-/

namespace RHTower.Sieve

noncomputable section

/-- The closed budget for the height surrogate. -/
def routeTHeightBudget (t : ℝ) : ℝ := 23 + 2 * Real.log |t|

/-- The closed budget for the reciprocal-width surrogate. -/
def routeTReciprocalBudget (A t : ℝ) : ℝ :=
  10 * routeTZeroFreeDeltaEnvelopeConstant A * (routeTHeightBudget t) ^ ((9 : ℝ) / 10)
    * (1 + Real.log (routeTHeightBudget t)) ^ 2

theorem one_le_routeTHeightBudget {t : ℝ} (ht : 1 ≤ |t|) : 1 ≤ routeTHeightBudget t := by
  have hlog : (0 : ℝ) ≤ Real.log |t| := Real.log_nonneg ht
  rw [routeTHeightBudget]
  linarith

/-- The height surrogate is below its budget. -/
theorem routeTHeightSurrogate_le {t : ℝ} (ht : 1 ≤ |t|) :
    routeTHeightSurrogate (-t) ≤ routeTHeightBudget t := by
  have habs : |(-t : ℝ)| = |t| := abs_neg t
  have h12 : Real.log 12 ≤ 11 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 12 by norm_num)
    linarith
  have hle : 6 * |t| + 6 ≤ 12 * |t| := by linarith
  have hlog : Real.log (6 * |t| + 6) ≤ Real.log 12 + Real.log |t| := by
    have h1 : Real.log (6 * |t| + 6) ≤ Real.log (12 * |t|) :=
      Real.log_le_log (by linarith) hle
    rwa [Real.log_mul (by norm_num) (by linarith)] at h1
  rw [routeTHeightSurrogate, routeTHeightBudget, habs]
  linarith

/-- The comparison function of the surrogate is monotone. -/
theorem surrogate_shape_mono {Z W : ℝ} (hZ : 1 ≤ Z) (hZW : Z ≤ W) :
    Z ^ ((9 : ℝ) / 10) * (1 + Real.log Z) ^ 2 ≤ W ^ ((9 : ℝ) / 10) * (1 + Real.log W) ^ 2 := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hW1 : (1 : ℝ) ≤ W := le_trans hZ hZW
  have hpow : Z ^ ((9 : ℝ) / 10) ≤ W ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow (by linarith) hZW (by norm_num)
  have hlogZ : (0 : ℝ) ≤ Real.log Z := Real.log_nonneg hZ
  have hlog : Real.log Z ≤ Real.log W := Real.log_le_log hZ0 hZW
  have hsq : (1 + Real.log Z) ^ 2 ≤ (1 + Real.log W) ^ 2 := by nlinarith [hlogZ, hlog]
  have hp0 : (0 : ℝ) ≤ Z ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hs0 : (0 : ℝ) ≤ (1 + Real.log Z) ^ 2 := sq_nonneg _
  exact mul_le_mul hpow hsq hs0 (Real.rpow_nonneg (by linarith) _)

/-- The reciprocal-width surrogate is below its budget. -/
theorem routeTWidthReciprocalSurrogate_le {A t : ℝ} (ht : 1 ≤ |t|) :
    routeTWidthReciprocalSurrogate A (-t) ≤ routeTReciprocalBudget A t := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have h1 := one_le_routeTHeightSurrogate (-t)
  have h2 := routeTHeightSurrogate_le ht
  have hshape := surrogate_shape_mono h1 h2
  rw [routeTWidthReciprocalSurrogate, routeTReciprocalBudget]
  nlinarith [hshape, hD]

/-- The width surrogate is above the reciprocal of its budget. -/
theorem routeTWidthLowSurrogate_ge {A t : ℝ} (ht : 1 ≤ |t|) :
    1 / routeTReciprocalBudget A t ≤ routeTWidthLowSurrogate A (-t) := by
  have hpos := routeTWidthReciprocalSurrogate_pos A (-t)
  have hle := routeTWidthReciprocalSurrogate_le (A := A) ht
  rw [routeTWidthLowSurrogate]
  exact one_div_le_one_div_of_le hpos hle

/-- The height factor surrogate is below an explicit polylogarithm in `log|t|`. -/
theorem routeTHeightFactorUpper_le {A t : ℝ} (ht : 1 ≤ |t|) :
    routeTHeightFactorUpper A (-t) ≤ 1 + (4 + Real.log |t|) * routeTReciprocalBudget A t := by
  have habs : |(-t : ℝ)| = |t| := abs_neg t
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hpos := routeTWidthReciprocalSurrogate_pos A (-t)
  have hle := routeTWidthReciprocalSurrogate_le (A := A) ht
  have hlogt : (0 : ℝ) ≤ Real.log |t| := Real.log_nonneg ht
  have h5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 5 by norm_num)
    linarith
  have hbound : Real.log (3 * |t| / 2 + 3) ≤ 4 + Real.log |t| := by
    have hle5 : 3 * |t| / 2 + 3 ≤ 5 * |t| := by linarith
    have h1 : Real.log (3 * |t| / 2 + 3) ≤ Real.log (5 * |t|) :=
      Real.log_le_log (by linarith) hle5
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hlogpos : (0 : ℝ) ≤ Real.log (3 * |t| / 2 + 3) :=
    Real.log_nonneg (by linarith)
  have hmul : Real.log (3 * |(-t : ℝ)| / 2 + 3) * routeTWidthReciprocalSurrogate A (-t)
      ≤ (4 + Real.log |t|) * routeTReciprocalBudget A t := by
    rw [habs]
    exact mul_le_mul hbound hle hpos.le (by linarith)
  rw [routeTHeightFactorUpper]
  linarith

end

end RHTower.Sieve
