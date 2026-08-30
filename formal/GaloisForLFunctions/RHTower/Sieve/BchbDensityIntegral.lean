import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The archimedean integral of the twisted second-moment density

The adapted diagonal of the twisted second moment has density (in `t`)

```text
2 · ( ½ log( c t ) + γ )  =  log(ct) + 2γ,      c = (h,k)²/(2π h k),
```

which integrates to the Balasubramanian--Conrey--Heath-Brown shape

```text
∫_a^b ( log(ct) + 2γ ) dt = b( log(cb) + 2γ − 1 ) − a( log(ca) + 2γ − 1 ).
```

The `−1` is precisely the classical `2γ − 1` of the second moment: it is produced by the
integration, not by the arithmetic.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace RHTower.Sieve

/-- The density of the twisted second moment at archimedean scale `t`. -/
def bchbLogDensity (c t : ℝ) : ℝ := Real.log (c * t) + 2 * Real.eulerMascheroniConstant

/-- Its antiderivative. -/
def bchbLogPrimitive (c t : ℝ) : ℝ :=
  t * (Real.log (c * t) + 2 * Real.eulerMascheroniConstant - 1)

theorem hasDerivAt_bchbLogPrimitive {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (bchbLogPrimitive c) (bchbLogDensity c t) t := by
  have hct : c * t ≠ 0 := by positivity
  have hmul : HasDerivAt (fun x : ℝ => c * x) c t := by
    simpa using (hasDerivAt_id' (x := t)).const_mul c
  have hlog : HasDerivAt (fun x : ℝ => Real.log (c * x)) ((c * t)⁻¹ * c) t :=
    (Real.hasDerivAt_log hct).comp t hmul
  have hinner : HasDerivAt
      (fun x : ℝ => Real.log (c * x) + 2 * Real.eulerMascheroniConstant - 1)
      ((c * t)⁻¹ * c) t := by
    simpa using (hlog.add_const (2 * Real.eulerMascheroniConstant)).sub_const 1
  have h := (hasDerivAt_id' (x := t)).mul hinner
  refine h.congr_deriv ?_
  simp only [bchbLogDensity]
  field_simp
  ring

/-- **The archimedean integral.**  The `2γ − 1` of the twisted second moment. -/
theorem integral_bchbLogDensity {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, bchbLogDensity c t)
      = b * (Real.log (c * b) + 2 * Real.eulerMascheroniConstant - 1)
        - a * (Real.log (c * a) + 2 * Real.eulerMascheroniConstant - 1) := by
  have hsub : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    intro t ht
    rw [hsub] at ht
    exact lt_of_lt_of_le ha ht.1
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (bchbLogPrimitive c) (bchbLogDensity c t) t :=
    fun t ht => hasDerivAt_bchbLogPrimitive hc (hpos t ht)
  have hcont : ContinuousOn (bchbLogDensity c) (Set.uIcc a b) := by
    intro t ht
    have h1 : (0 : ℝ) < c * t := by
      have := hpos t ht
      positivity
    have : ContinuousAt (bchbLogDensity c) t := by
      unfold bchbLogDensity
      exact ((Real.continuousAt_log (ne_of_gt h1)).comp
        (by fun_prop : ContinuousAt (fun x : ℝ => c * x) t)).add continuousAt_const
    exact this.continuousWithinAt
  have hint : IntervalIntegrable (bchbLogDensity c) volume a b :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rfl

end RHTower.Sieve
