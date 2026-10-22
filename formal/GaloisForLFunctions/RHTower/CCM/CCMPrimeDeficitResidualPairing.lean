import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitTruncationDefect
import GaloisForLFunctions.RHTower.LogarithmicLinearEntryConvolution

/-!
# Factoring the complete divisor source through residual coefficients

The source has two causal components, exponential and linear. Both may
be factored through literal divisor sums of an arbitrary signed sequence.
This identity has no short-window restriction.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def logarithmicDivisorTransform (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, w d

def logarithmicLogDivisorTransform (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, w d * Real.log (n / d : ℕ)

theorem logarithmicWeightedDilation_sub_profile (a : ℕ → ℝ) (f g : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (fun t => f t - g t) T =
      logarithmicWeightedDilation a f T - logarithmicWeightedDilation a g T := by
  simp only [logarithmicWeightedDilation, mul_sub, Finset.sum_sub_distrib]

theorem logarithmicWeightedDilation_pair_sub_profile (a b : ℕ → ℝ) (f g : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation a (logarithmicWeightedDilation b (fun t => f t - g t)) T =
      logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T -
        logarithmicWeightedDilation a (logarithmicWeightedDilation b g) T := by
  have h := funext (logarithmicWeightedDilation_sub_profile b f g)
  rw [h, logarithmicWeightedDilation_sub_profile]

theorem logarithmicWeightedDilation_congr_nonneg (a : ℕ → ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ t, 0 ≤ t → f t = g t) (T : ℝ) :
    logarithmicWeightedDilation a f T = logarithmicWeightedDilation a g T := by
  unfold logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnp).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
  rw [hfg _ (sub_nonneg.mpr hlog)]

theorem logarithmicWeightedDilation_divisorTransform (w : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicDilationSum f) T =
      logarithmicWeightedDilation (logarithmicDivisorTransform w) f T := by
  change logarithmicWeightedDilation w (logarithmicWeightedDilation (fun _ => 1) f) T = _
  rw [logarithmicWeightedDilation_comp]
  congr 1
  funext n
  simpa only [mul_one, logarithmicDivisorTransform] using
    Nat.sum_divisorsAntidiagonal (fun d _ => w d)

theorem logarithmicWeightedDilation_logDivisorTransform (w : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation (fun n => Real.log n) f) T =
      logarithmicWeightedDilation (logarithmicLogDivisorTransform w) f T := by
  rw [logarithmicWeightedDilation_comp]
  congr 1
  funext n
  exact Nat.sum_divisorsAntidiagonal (fun d e => w d * Real.log e)

theorem logarithmicWeightedDilation_pair_dilationSum (w : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation w (logarithmicDilationSum f)) T =
      logarithmicWeightedDilation (logarithmicDivisorTransform w)
        (logarithmicWeightedDilation w f) T := by
  have hc : logarithmicWeightedDilation w (logarithmicDilationSum f) =
      logarithmicDilationSum (logarithmicWeightedDilation w f) :=
    funext (logarithmicWeightedDilation_comm w (fun _ => 1) f)
  rw [hc, logarithmicWeightedDilation_divisorTransform]

theorem ccmPrimeDeficitDilationSource_eq_causal_ramps (T : ℝ) :
    ccmPrimeDeficitDilationSource T = logarithmicDilationSum logarithmicExponentialRamp T -
      logarithmicWeightedDilation (fun n => Real.log n) logarithmicLinearRamp T := by
  rw [ccmPrimeDeficitDilationSource_eq_elementary_dilations]
  have he := logarithmicWeightedDilation_congr_nonneg (fun _ => 1)
    (fun t => Real.exp t - 1) logarithmicExponentialRamp
    (fun _ ht => (logarithmicExponentialRamp_of_nonneg ht).symm) T
  have hl := logarithmicWeightedDilation_congr_nonneg (fun n => Real.log n)
    (fun t => t) logarithmicLinearRamp
    (fun _ ht => (logarithmicLinearRamp_of_nonneg ht).symm) T
  exact congrArg₂ (fun x y : ℝ => x - y) he hl

theorem ccmPrimeDeficitDivisorSource_eq_causal_ramps (T : ℝ) :
    ccmPrimeDeficitDivisorSource T =
      logarithmicDilationSum (logarithmicDilationSum logarithmicExponentialRamp) T -
        logarithmicDilationSum
          (logarithmicWeightedDilation (fun n => Real.log n) logarithmicLinearRamp) T := by
  rw [← logarithmicDilationSum_dilationSource_eq_divisorSource,
    funext ccmPrimeDeficitDilationSource_eq_causal_ramps]
  exact logarithmicWeightedDilation_sub_profile _ _ _ T

/-- Exact factorization of the complete signed source pairing, valid at
every time and for every coefficient sequence. -/
theorem logarithmicWeightedDilation_pair_divisorSource (w : ℕ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation w ccmPrimeDeficitDivisorSource) T =
      logarithmicWeightedDilation (logarithmicDivisorTransform w)
        (logarithmicWeightedDilation (logarithmicDivisorTransform w) logarithmicExponentialRamp) T -
      logarithmicWeightedDilation (logarithmicLogDivisorTransform w)
        (logarithmicWeightedDilation (logarithmicDivisorTransform w) logarithmicLinearRamp) T := by
  rw [funext ccmPrimeDeficitDivisorSource_eq_causal_ramps,
    logarithmicWeightedDilation_pair_sub_profile,
    logarithmicWeightedDilation_pair_dilationSum, logarithmicWeightedDilation_pair_dilationSum]
  rw [funext (logarithmicWeightedDilation_divisorTransform w logarithmicExponentialRamp),
    funext (logarithmicWeightedDilation_logDivisorTransform w logarithmicLinearRamp)]
  rw [logarithmicWeightedDilation_comm (logarithmicDivisorTransform w)
    (logarithmicLogDivisorTransform w) logarithmicLinearRamp]

def ccmPrimeDeficitResidualCoeff (m : ℕ) : ℕ → ℝ :=
  logarithmicDivisorTransform (logarithmicLongTail m moebiusCoeff)

def ccmPrimeDeficitResidualLogCoeff (m : ℕ) : ℕ → ℝ :=
  logarithmicLogDivisorTransform (logarithmicLongTail m moebiusCoeff)

theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_residual_pair (m : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      logarithmicWeightedDilation (ccmPrimeDeficitResidualCoeff m)
        (logarithmicWeightedDilation (ccmPrimeDeficitResidualCoeff m) logarithmicExponentialRamp) T -
      logarithmicWeightedDilation (ccmPrimeDeficitResidualLogCoeff m)
        (logarithmicWeightedDilation (ccmPrimeDeficitResidualCoeff m) logarithmicLinearRamp) T := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction m hT]
  exact logarithmicWeightedDilation_pair_divisorSource _ T

end RHTower
