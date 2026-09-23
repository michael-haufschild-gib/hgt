import GaloisForLFunctions.RHTower.Sieve.HalaszDichotomyInstance
/-!
# The window measure with the frequency weight evaluated

The corpus's frequency weight is `logSqWeight z = (log z)²/2 − 39 log z − 25`, and once `log z ≥ 160` its linear
terms are absorbed: `logSqWeight z ≥ (log z)²/4`.  Substituted into the window measure,

`halaszWindowMeasureBound T z δ ≤ (2T log z/π + 1)·(4√2 πδ/log z)`,

whose product with the trivial size of the series is of order `Tδ`.  So the exceptional window costs a term
*linear* in the distance level `δ`, while off the window the series is damped by `e^{−δ²}`: the balance the
Halász argument strikes, with both sides now explicit in the corpus.
-/

noncomputable section
namespace RHTower.Sieve
open Real

/-- **The frequency weight is at least a quarter of the squared logarithm.**  `logSqWeight z = (log z)²/2 − 39
log z − 25`, and the linear terms are absorbed once `log z ≥ 160`. -/
theorem logSqWeight_ge_quarter {z : ℕ} (hz : 160 ≤ Real.log z) :
    (Real.log z) ^ (2 : ℕ) / 4 ≤ logSqWeight z := by
  rw [logSqWeight]
  nlinarith [hz]

/-- **The window measure, with the weight evaluated.**  At `log z ≥ 160` the measure of the exceptional window is
at most `(2T log z/π + 1)·4√2 πδ/log z`, so its product with the trivial size is of order `Tδ`: linear in the
distance level, against which the damping off the window is exponential. -/
theorem halaszWindowMeasureBound_le {T : ℝ} (hT : 0 ≤ T) {z : ℕ} (hz : 160 ≤ Real.log z)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    halaszWindowMeasureBound T z δ
      ≤ (2 * T * Real.log (z : ℝ) / Real.pi + 1) * (4 * Real.sqrt 2 * Real.pi * δ / Real.log z) := by
  have hlogz : (0 : ℝ) < Real.log z := by linarith
  have hW : (Real.log z) ^ (2 : ℕ) / 4 ≤ logSqWeight z := logSqWeight_ge_quarter hz
  have hW0 : 0 < logSqWeight z := by
    have h4 : (0 : ℝ) < (Real.log z) ^ (2 : ℕ) / 4 := by positivity
    linarith
  have hfac0 : (0 : ℝ) ≤ 2 * T * Real.log (z : ℝ) / Real.pi + 1 := by
    have : (0 : ℝ) ≤ 2 * T * Real.log (z : ℝ) / Real.pi := by positivity
    linarith
  rw [halaszWindowMeasureBound]
  refine mul_le_mul_of_nonneg_left ?_ hfac0
  -- compare the two square roots
  have hkey : 2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z
      ≤ (2 * Real.sqrt 2 * Real.pi * δ / Real.log z) ^ (2 : ℕ) := by
    have hsq2 : (Real.sqrt 2) ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
    have hrhs : (2 * Real.sqrt 2 * Real.pi * δ / Real.log z) ^ (2 : ℕ)
        = 8 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / (Real.log z) ^ (2 : ℕ) := by
      field_simp
      nlinarith [hsq2]
    rw [hrhs, div_le_div_iff₀ hW0 (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hW
      (by positivity : (0 : ℝ) ≤ 8 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ))
    nlinarith [hmul]
  have hsqrt : Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z)
      ≤ 2 * Real.sqrt 2 * Real.pi * δ / Real.log z := by
    have h := Real.sqrt_le_sqrt hkey
    rwa [Real.sqrt_sq (by positivity)] at h
  calc 2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z)
      ≤ 2 * (2 * Real.sqrt 2 * Real.pi * δ / Real.log z) := by linarith [hsqrt]
    _ = 4 * Real.sqrt 2 * Real.pi * δ / Real.log z := by ring

end RHTower.Sieve
end
