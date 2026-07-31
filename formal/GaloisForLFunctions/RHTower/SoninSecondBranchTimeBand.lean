import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# The second branch factors through a fixed time-band operator

The forward dilation carries an inner-band vector inside the inner aperture, so on such a vector
the second branch of the coupling can be rewritten with the Fourier cutoff moved outside the
dilation.  What appears there is a Fourier cutoff composed with a physical cutoff — a finite
time-band block, which the corpus knows to be Schatten-1.

So the second branch of the coupling is not an arbitrary operator: it factors through a fixed
trace-class time-band operator, uniformly in the test vector.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- On an inner-band vector the forward dilation and the Fourier cutoff exchange places, and the
physical cutoff at the inner aperture may be inserted for free. -/
theorem evenDilationCLM_evenFourierCutoff_apply_of_indicatorCutoff_eq_self
    {a b c r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w) =
      (evenFourierCutoff (r * b) * evenIndicatorCutoff a)
        (evenDilationCLM r (zero_lt_one.trans hr) w) := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hmove := evenDilationCLM_mul_evenFourierCutoff b r hr0
  have hswap : evenDilationCLM r hr0 (evenFourierCutoff b w) =
      evenFourierCutoff (r * b) (evenDilationCLM r hr0 w) := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T w) hmove
    simpa only [mul_apply_eq_comp] using this
  have hinner : evenIndicatorCutoff a (evenDilationCLM r hr0 w) =
      evenDilationCLM r hr0 w :=
    indicatorCutoff_evenDilationCLM_apply_of_indicatorCutoff_eq_self hr hcr hw
  rw [hswap]
  change _ = evenFourierCutoff (r * b)
    (evenIndicatorCutoff a (evenDilationCLM r hr0 w))
  rw [hinner]

/-- **Second branch factors through a time-band block.**  The second term of the branch normal form
is the aperture layer applied to a fixed Schatten-1 time-band operator evaluated at the dilated
test vector. -/
theorem evenSoninApertureLayer_secondBranch_eq_timeBand
    {a b c r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    evenSoninApertureLayer a b
        (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w)) =
      evenSoninApertureLayer a b
        ((evenFourierCutoff (r * b) * evenIndicatorCutoff a)
          (evenDilationCLM r (zero_lt_one.trans hr) w)) := by
  rw [evenDilationCLM_evenFourierCutoff_apply_of_indicatorCutoff_eq_self hr hcr hw]

/-- The time-band block appearing in the second branch is Schatten-1. -/
theorem memSchattenClass_one_secondBranch_timeBand
    {a b r : ℝ} (hb : 0 < b) (hr : 1 < r) :
    MemSchattenClass 1
      (evenFourierCutoff (r * b) * evenIndicatorCutoff a) := by
  have hrb : 0 < r * b := mul_pos (zero_lt_one.trans hr) hb
  exact IsSoninPrincipalRelativeIdeal.fourierIndicator_memSchattenClass_one
    (r * b) a hrb

/-- Consequently the second branch is bounded by the operator norm of a fixed trace-class block,
uniformly in the test vector. -/
theorem norm_evenSoninApertureLayer_secondBranch_le
    {a b c r : ℝ} (hab : a ≤ b) (hr : 1 < r) (hcr : c ≤ r * a)
    {w : evenSubspace} (hw : evenIndicatorCutoff c w = w) :
    ‖evenSoninApertureLayer a b
        (evenDilationCLM r (zero_lt_one.trans hr) (evenFourierCutoff b w))‖ ≤
      ‖evenFourierCutoff (r * b) * evenIndicatorCutoff a‖ * ‖w‖ := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  rw [evenSoninApertureLayer_secondBranch_eq_timeBand hr hcr hw]
  calc
    ‖evenSoninApertureLayer a b
        ((evenFourierCutoff (r * b) * evenIndicatorCutoff a)
          (evenDilationCLM r hr0 w))‖
        ≤ ‖(evenFourierCutoff (r * b) * evenIndicatorCutoff a)
            (evenDilationCLM r hr0 w)‖ :=
      norm_evenSoninApertureLayer_apply_le hab _
    _ ≤ ‖evenFourierCutoff (r * b) * evenIndicatorCutoff a‖ *
          ‖evenDilationCLM r hr0 w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖evenFourierCutoff (r * b) * evenIndicatorCutoff a‖ * ‖w‖ := by
      rw [norm_evenDilationCLM_apply r hr0 w]

end RHTower
