import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilMixedDecay
import GaloisForLFunctions.BiScaleUncertainty.FactorialTentWeilCoercivity

/-! Quantitative elimination of the tent direction in the actual full Weil form.
The ramp diagonal's sign is not assumed or asserted. -/

open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

/-- Energy of the actual ramp with its optimal tent correction. -/
def factorialWeilMinRamp (n : ℕ) : ℝ :=
  factorialSpanWeil n 1 (-(factorialWeilMixed n)/(2*factorialSpanWeil n 0 1))

private theorem mixed_sq_le (n : ℕ) :
    (factorialWeilMixed n)^2 ≤ (factorialWeilMixedBound n)^2 := by
  have h := factorialWeilMixed_abs_le n
  have he := (abs_nonneg (factorialWeilMixed n)).trans h
  have hp := mul_nonneg (sub_nonneg.mpr h) (add_nonneg he (abs_nonneg (factorialWeilMixed n)))
  nlinarith [sq_abs (factorialWeilMixed n)]

/-- Uniform control of every coefficient choice; the only uncontrolled diagonal
is the concrete pure-ramp energy, with an explicit vanishing subtraction. -/
theorem factorialSpanWeil_eventual_lower :
    ∀ᶠ n in atTop, ∀ c d : ℝ,
      c^2*(factorialSpanWeil n 1 0-factorialWeilGramError n)+
        (factorialSpanWeil n 0 1/2)*d^2 ≤ factorialSpanWeil n c d := by
  filter_upwards [factorialTentWeil_eventually_ge_scale] with n hD
  intro c d
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hs := sq_nonneg (((n+1 : ℕ) : ℝ)*d+c*factorialWeilMixed n)
  have he := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (mixed_sq_le n))
  have hd := mul_nonneg (mul_nonneg hn.le (sub_nonneg.mpr hD)) (sq_nonneg d)
  rw [factorialSpanWeil_gram]
  unfold factorialWeilGramError
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2*((n+1 : ℕ) : ℝ) by positivity)).1
  field_simp [hn.ne']
  nlinarith

/-- Exact completion of the square on the concrete source span. -/
theorem factorialSpanWeil_eventual_complete_square :
    ∀ᶠ n in atTop, ∀ c d : ℝ,
      factorialSpanWeil n c d =
        factorialSpanWeil n 0 1*(d+c*factorialWeilMixed n/(2*factorialSpanWeil n 0 1))^2+
        c^2*factorialWeilMinRamp n := by
  filter_upwards [factorialTentWeil_eventually_ge_scale] with n hn
  have hD : 0 < factorialSpanWeil n 0 1 :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ)) hn
  intro c d
  unfold factorialWeilMinRamp
  rw [factorialSpanWeil_gram n c d, factorialSpanWeil_gram n 1]
  field_simp [hD.ne']
  ring

theorem factorialWeilMinRamp_eventually_min :
    ∀ᶠ n in atTop, ∀ d : ℝ, factorialWeilMinRamp n ≤ factorialSpanWeil n 1 d := by
  filter_upwards [factorialSpanWeil_eventual_complete_square,
    factorialTentWeil_eventually_ge_scale] with n hsq hD
  intro d
  rw [hsq 1 d]
  have hD0 : 0 ≤ factorialSpanWeil n 0 1 := le_trans (by positivity) hD
  have hp := mul_nonneg hD0 (sq_nonneg (d+factorialWeilMixed n/(2*factorialSpanWeil n 0 1)))
  nlinarith

theorem factorialWeilMinRamp_eventual_gap :
    ∀ᶠ n in atTop,
      0 ≤ factorialSpanWeil n 1 0-factorialWeilMinRamp n ∧
      factorialSpanWeil n 1 0-factorialWeilMinRamp n ≤ factorialWeilGramError n := by
  filter_upwards [factorialSpanWeil_eventual_lower, factorialWeilMinRamp_eventually_min,
    factorialTentWeil_eventually_ge_scale] with n hlo hmin hD
  constructor
  · linarith [hmin 0]
  · have hh := hlo 1 (-(factorialWeilMixed n)/(2*factorialSpanWeil n 0 1))
    change _ ≤ factorialWeilMinRamp n at hh
    have hD0 : 0 ≤ factorialSpanWeil n 0 1 := le_trans (by positivity) hD
    have hp := mul_nonneg (div_nonneg hD0 (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (-(factorialWeilMixed n)/(2*factorialSpanWeil n 0 1)))
    nlinarith

/-- Optimizing over all tent coefficients changes the pure-ramp energy by a
quantity tending to zero, unconditionally. -/
theorem factorialWeilMinRamp_gap_tendsto :
    Tendsto (fun n => factorialSpanWeil n 1 0-factorialWeilMinRamp n) atTop (𝓝 0) :=
  squeeze_zero' (factorialWeilMinRamp_eventual_gap.mono fun _ h => h.1)
    (factorialWeilMinRamp_eventual_gap.mono fun _ h => h.2) factorialWeilGramError_tendsto

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
