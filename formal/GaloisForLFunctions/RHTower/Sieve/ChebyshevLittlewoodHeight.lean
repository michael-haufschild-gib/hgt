import GaloisForLFunctions.RHTower.Sieve.ChebyshevHeightOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodShape

/-!
# The balanced height for a shift of depth `A`

The exponent-one chain fixes the truncation height at `exp(2√(log x))`, which is the balance point
for a contour shifted by `1/40000/log T`.  When the shift is `A/log T` with `A` free the balance
moves: the left edge saves `exp(-A·log x/log T)` and the truncation costs `1/T`, so the height must
be

```text
chebHeightLw A x = exp(2√(A log x)) ,
```

at which the saving exponent is `√(A log x)/2`.  At `A = 1/40000` this is `√(log x)/400`, and the
exponent-one chain's `√(log x)/80000` is the same shape with the height not re-optimised.  The
point of carrying `A` is that the saving grows like `√A`, so `A ≍ log log x` — which the Littlewood
region permits — gives `exp(-c√(log x · log log x))`.
-/

namespace RHTower.Sieve

/-- The balanced truncation height for a shift of depth `A`. -/
noncomputable def chebHeightLw (A x : ℝ) : ℝ := Real.exp (2 * Real.sqrt (A * Real.log x))

theorem chebHeightLw_pos (A x : ℝ) : 0 < chebHeightLw A x := Real.exp_pos _

theorem one_le_chebHeightLw (A x : ℝ) : 1 ≤ chebHeightLw A x := by
  rw [chebHeightLw]
  exact Real.one_le_exp (by positivity)

theorem log_chebHeightLw (A x : ℝ) :
    Real.log (chebHeightLw A x) = 2 * Real.sqrt (A * Real.log x) := by
  rw [chebHeightLw, Real.log_exp]

theorem four_le_sqrt_mul_log {A x : ℝ} (hx : 16 ≤ A * Real.log x) :
    4 ≤ Real.sqrt (A * Real.log x) := by
  have h : Real.sqrt 16 ≤ Real.sqrt (A * Real.log x) := Real.sqrt_le_sqrt hx
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h16]

theorem eight_le_log_chebHeightLw {A x : ℝ} (hx : 16 ≤ A * Real.log x) :
    8 ≤ Real.log (chebHeightLw A x) := by
  rw [log_chebHeightLw]
  linarith [four_le_sqrt_mul_log hx]

/-- The height clears the depth condition `2A ≤ log T` of the width-`A/log T` data. -/
theorem two_mul_le_log_chebHeightLw {A x : ℝ} (hA : 0 < A) (hAx : A ≤ Real.log x) :
    2 * A ≤ Real.log (chebHeightLw A x) := by
  rw [log_chebHeightLw]
  have hsq : Real.sqrt (A * Real.log x) * Real.sqrt (A * Real.log x) = A * Real.log x :=
    Real.mul_self_sqrt (by nlinarith)
  have hnn : (0 : ℝ) ≤ Real.sqrt (A * Real.log x) := Real.sqrt_nonneg _
  nlinarith [hsq, hnn, hA, hAx]

/-- **The left edge's saving at the balanced height.**  Depth `A` saves `√(A log x)/2`. -/
theorem saving_exponent_lw {A x : ℝ} (hA : 0 < A) (hx : 0 < Real.log x) :
    A / Real.log (chebHeightLw A x) * Real.log x = Real.sqrt (A * Real.log x) / 2 := by
  rw [log_chebHeightLw]
  have hAx : (0 : ℝ) < A * Real.log x := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (A * Real.log x) := Real.sqrt_pos.mpr hAx
  have hsq : Real.sqrt (A * Real.log x) * Real.sqrt (A * Real.log x) = A * Real.log x :=
    Real.mul_self_sqrt hAx.le
  field_simp
  nlinarith [hsq, hs0]

/-- **The right line's growth at the balanced height.** -/
theorem right_exponent_lw {A x : ℝ} (hA : 0 < A) (hx : 0 < Real.log x) :
    1 / Real.log (chebHeightLw A x) * Real.log x
      = Real.sqrt (A * Real.log x) / (2 * A) := by
  rw [log_chebHeightLw]
  have hAx : (0 : ℝ) < A * Real.log x := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (A * Real.log x) := Real.sqrt_pos.mpr hAx
  have hsq : Real.sqrt (A * Real.log x) * Real.sqrt (A * Real.log x) = A * Real.log x :=
    Real.mul_self_sqrt hAx.le
  field_simp
  nlinarith [hsq, hs0, hA]

/-- The height's logarithm, squared. -/
theorem sq_log_chebHeightLw (A x : ℝ) (hAx : 0 ≤ A * Real.log x) :
    Real.log (chebHeightLw A x) ^ 2 = 4 * (A * Real.log x) := by
  rw [log_chebHeightLw]
  have hsq : Real.sqrt (A * Real.log x) * Real.sqrt (A * Real.log x) = A * Real.log x :=
    Real.mul_self_sqrt hAx
  nlinarith [hsq]

end RHTower.Sieve
