import GaloisForLFunctions.RHTower.CCMPrimeDeficitEulerResidual

/-!
# A positive delayed recurrence from Euler completion

The coefficient residual after completing a finite Euler product has one
sign. Its quadratic error is therefore a positive delay operator applied
to the actual signed deficit itself. The two nonnegative causal work
terms retain the complete prime correction.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem logarithmicWeightedDilation_pair_neg_coeff (a b : ℕ → ℝ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation (fun n => -a n)
      (logarithmicWeightedDilation (fun n => -b n) f) T =
        logarithmicWeightedDilation a (logarithmicWeightedDilation b f) T := by
  simp only [logarithmicWeightedDilation, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]

/-- The full divisor source transfers the residual back to actual earlier deficit values. -/
theorem logarithmicWeightedDilation_pair_divisorSource_eq_deficit_pair
    (w : ℕ → ℝ) (T : ℝ) :
    logarithmicWeightedDilation w (logarithmicWeightedDilation w ccmPrimeDeficitDivisorSource) T =
      logarithmicWeightedDilation (logarithmicDivisorTransform w)
        (logarithmicWeightedDilation (logarithmicDivisorTransform w)
          ccmLogChebyshevDeficitPrimitive) T := by
  have hg : logarithmicDilationSum ccmLogChebyshevDeficitPrimitive =
      ccmPrimeDeficitDilationSource := by
    funext t
    simpa only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul] using
      ccmLogChebyshevDeficitPrimitive_dilation_conservation t
  rw [← funext logarithmicDilationSum_dilationSource_eq_divisorSource, ← hg,
    logarithmicWeightedDilation_pair_dilationSum,
    funext (logarithmicWeightedDilation_divisorTransform w ccmLogChebyshevDeficitPrimitive)]

def ccmPrimeDeficitEulerAction (P : ℕ) (T : ℝ) : ℝ :=
  ccmPrimeDeficitCoefficientAction T (ccmEulerMobius P)

private theorem euler_action_defect (P : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitEulerAction P T =
      logarithmicWeightedDilation (ccmEulerMobiusTail P)
        (logarithmicWeightedDilation (ccmEulerMobiusTail P) ccmPrimeDeficitDivisorSource) T := by
  have hc : (ccmEulerMobius P : ℕ → ℝ) =
      fun n => (ArithmeticFunction.moebius n : ℝ) + (-1) * ccmEulerMobiusTail P n := by
    funext n
    change ccmEulerMobius P n = (ArithmeticFunction.moebius n : ℝ) +
      (-1) * ((ArithmeticFunction.moebius n : ℝ) - ccmEulerMobius P n)
    ring
  rw [ccmPrimeDeficitEulerAction, hc,
    ccmPrimeDeficitCoefficientAction_mobius_line _ hT (-1)]
  ring

/-- Positive renewal: every coefficient of the delay operator is nonnegative;
the values of the deficit retain their actual signs. -/
theorem ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_renewal
    (P : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitEulerAction P T =
      logarithmicWeightedDilation (ccmEulerRough P)
        (logarithmicWeightedDilation (ccmEulerRough P) ccmLogChebyshevDeficitPrimitive) T := by
  rw [euler_action_defect P hT,
    logarithmicWeightedDilation_pair_divisorSource_eq_deficit_pair,
    funext (logarithmicDivisorTransform_ccmEulerMobiusTail P),
    logarithmicWeightedDilation_pair_neg_coeff]

def ccmPrimeDeficitEulerExponentialWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation (ccmEulerRough P)
    (logarithmicWeightedDilation (ccmEulerRough P) logarithmicExponentialRamp) T

def ccmPrimeDeficitEulerPrimeWork (P : ℕ) (T : ℝ) : ℝ :=
  logarithmicWeightedDilation
    (ccmEulerRough P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)
      (logarithmicWeightedDilation (ccmEulerRough P) logarithmicLinearRamp) T

theorem ccmLogChebyshevDeficitPrimitive_sub_eulerAction_eq_work_difference
    (P : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitEulerAction P T =
      ccmPrimeDeficitEulerExponentialWork P T - ccmPrimeDeficitEulerPrimeWork P T := by
  rw [euler_action_defect P hT, logarithmicWeightedDilation_pair_divisorSource,
    funext (logarithmicDivisorTransform_ccmEulerMobiusTail P),
    funext (logarithmicLogDivisorTransform_ccmEulerMobiusTail P),
    logarithmicWeightedDilation_pair_neg_coeff, logarithmicWeightedDilation_pair_neg_coeff]
  rfl

theorem ccmPrimeDeficitEulerExponentialWork_nonneg (P : ℕ) (T : ℝ) :
    0 ≤ ccmPrimeDeficitEulerExponentialWork P T := by
  unfold ccmPrimeDeficitEulerExponentialWork logarithmicWeightedDilation
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (ccmEulerRough_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (ccmEulerRough_nonneg _ _)
      (le_max_right _ _))

theorem ccmPrimeDeficitEulerPrimeWork_nonneg (P : ℕ) (T : ℝ) :
    0 ≤ ccmPrimeDeficitEulerPrimeWork P T := by
  unfold ccmPrimeDeficitEulerPrimeWork logarithmicWeightedDilation
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (ccmEulerRough_primeForce_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (ccmEulerRough_nonneg _ _)
      (le_max_right _ _))

/-- The Euler completion lies in the already proved affine symmetry slice. -/
theorem ccmPrimeDeficitEulerAction_factorial_half (T : ℝ) (hT : 0 ≤ T) :
    ccmPrimeDeficitEulerAction (⌊Real.exp (T / 2)⌋₊.factorial) T =
      ccmLogChebyshevDeficitPrimitive T := by
  have he : (ccmEulerMobius (⌊Real.exp (T / 2)⌋₊.factorial) : ℕ → ℝ) =
      logarithmicMobiusHeadExtension ⌊Real.exp (T / 2)⌋₊
        (ccmEulerMobius (⌊Real.exp (T / 2)⌋₊.factorial)) := by
    funext n
    by_cases hn : n ≤ ⌊Real.exp (T / 2)⌋₊
    · simp only [logarithmicMobiusHeadExtension, if_pos hn,
        ccmEulerMobius_factorial_of_le hn]
    · simp only [logarithmicMobiusHeadExtension, if_neg hn]
  rw [ccmPrimeDeficitEulerAction, he]
  exact ccmPrimeDeficitCoefficientAction_headExtension _ hT

end RHTower
